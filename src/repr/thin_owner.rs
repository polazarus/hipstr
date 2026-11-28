//! Thin-only heap handle that points to the **data** of a thin buffer.
//!
//! Like [`Owner`](super::owner::Owner) without the adopted-`Vec` case: the
//! bytes always follow the header in the same allocation, at the constant
//! offset `DATA_OFFSET`. Pointing to the data rather than to the header lets
//! reads use the pointer as is (no header load, no kind branch); the header,
//! needed only to clone, drop or mutate, is one subtraction away.
//!
//! The pointer always derives from the allocation's base pointer (through
//! `ThinBase`), never from a slice reference: walking back to the header
//! needs the provenance of the whole allocation.

use alloc::vec::Vec;
use core::marker::PhantomData;
use core::ptr::NonNull;

use crate::backend::{Backend, Counter, UpdateResult};
use crate::common::header::ThinHeader;
use crate::common::tagged_pointer::TaggedPointer;
use crate::thin::TryReserveError;

type Header<B> = ThinHeader<<B as Backend>::Counter>;
type ThinBase<B> = crate::thin::Base<<B as Backend>::Counter>;

/// Thin-only heap handle (see the module documentation).
///
/// `Copy` on purpose, like `Owner`: copying does not touch the counter.
#[repr(transparent)]
pub struct ThinOwner<B: Backend>(NonNull<u8>, PhantomData<B>);

impl<B: Backend> Copy for ThinOwner<B> {}
impl<B: Backend> Clone for ThinOwner<B> {
    fn clone(&self) -> Self {
        *self
    }
}

const _: () = {
    type B = crate::backend::Rc;
    assert!(size_of::<ThinOwner<B>>() == size_of::<usize>());
    // the data pointer keeps the header's alignment (tags in the low bits)
    assert!(Header::<B>::DATA_OFFSET.is_multiple_of(align_of::<Header<B>>()));
};

#[allow(clippy::len_without_is_empty, reason = "a handle, never empty")]
impl<B: Backend> ThinOwner<B> {
    /// Wraps an allocated thin buffer.
    pub(crate) const fn from_base(base: &ThinBase<B>) -> Self {
        let header = base.0.as_non_null().expect("allocated thin buffer");
        // SAFETY: an allocated header is followed by its data
        Self(unsafe { Header::<B>::data(header) }, PhantomData)
    }

    /// The thin buffer, to grow, shrink or free it.
    pub(crate) fn into_base(self) -> ThinBase<B> {
        crate::thin::Base(TaggedPointer::from(self.header_ptr()))
    }

    /// Allocates a buffer with room for `capacity` (non-zero) elements.
    ///
    /// # Errors
    ///
    /// On capacity overflow or allocation failure.
    pub fn try_with_capacity(capacity: usize) -> Result<Self, TryReserveError> {
        debug_assert!(capacity != 0);
        ThinBase::<B>::try_with_capacity(capacity).map(|base| Self::from_base(&base))
    }

    /// Rebuilds a handle from its data pointer.
    ///
    /// # Safety
    ///
    /// `data` must come from [`data`](Self::data) of a live handle.
    #[inline]
    #[must_use]
    pub const unsafe fn from_data(data: NonNull<u8>) -> Self {
        Self(data, PhantomData)
    }

    /// The data pointer (with the provenance of the whole allocation).
    #[inline]
    #[must_use]
    pub const fn data(self) -> NonNull<u8> {
        self.0
    }

    #[inline]
    const fn header_ptr(self) -> NonNull<Header<B>> {
        // SAFETY: the header precedes the data in the same allocation, and the
        // pointer has the provenance of the whole allocation
        unsafe { self.0.byte_sub(Header::<B>::DATA_OFFSET).cast() }
    }

    #[inline]
    const fn header(&self) -> &Header<B> {
        // SAFETY: type invariant, a live header
        unsafe { self.header_ptr().as_ref() }
    }

    #[inline]
    #[must_use]
    pub const fn len(self) -> usize {
        self.header().len
    }

    #[inline]
    #[must_use]
    pub const fn capacity(self) -> usize {
        self.header().cap
    }

    /// The owned elements (the whole buffer, not a view of it).
    #[inline]
    #[must_use]
    pub const fn as_slice<'a>(self) -> &'a [u8] {
        // SAFETY: type invariant, the first `len` elements are initialized
        unsafe { core::slice::from_raw_parts(self.0.as_ptr(), self.len()) }
    }

    #[inline]
    #[must_use]
    pub fn is_unique(self) -> bool {
        self.header().prefix.is_unique()
    }

    /// Sets the length of the buffer.
    ///
    /// # Safety
    ///
    /// The handle must be unique, `len <= capacity` and the elements
    /// initialized.
    #[inline]
    pub const unsafe fn set_len(self, len: usize) {
        debug_assert!(len <= self.capacity());
        // SAFETY: precondition, unique access
        unsafe { (*self.header_ptr().as_ptr()).len = len };
    }

    /// Increments the reference count and returns a new handle; `None` if
    /// the backend asks for a deep copy instead.
    ///
    /// # Panics
    ///
    /// On counter overflow for backends that panic on overflow.
    #[inline]
    #[must_use]
    pub fn try_clone(self) -> Option<Self> {
        match self.header().prefix.incr() {
            UpdateResult::Done => Some(self),
            UpdateResult::Overflow if B::PANIC_ON_OVERFLOW => {
                panic!("reference count overflow")
            }
            UpdateResult::Overflow => None,
        }
    }

    /// Decrements the reference count, freeing the buffer on the last release.
    ///
    /// # Safety
    ///
    /// The handle must not be used afterwards.
    pub unsafe fn release(self) {
        if self.header().prefix.decr() == UpdateResult::Overflow {
            // SAFETY: last handle; elements are `Copy`, nothing to drop
            unsafe { self.into_base().drop_container() }
        }
    }

    /// A copy of the first `len` elements as a vector, releasing the handle.
    #[must_use]
    pub fn into_vec_prefix(self, len: usize) -> Vec<u8> {
        debug_assert!(len <= self.len());
        let vec = self.as_slice()[..len].to_vec();
        // SAFETY: the handle is consumed
        unsafe { self.release() };
        vec
    }

    /// Ensures room for `required` (more than the capacity) elements;
    /// `exact` asks for no more than that.
    ///
    /// # Errors
    ///
    /// On capacity overflow or allocation failure; the buffer is unchanged.
    ///
    /// # Safety
    ///
    /// The handle must be unique; it may move, the caller stores it back.
    pub unsafe fn try_grow(&mut self, required: usize, exact: bool) -> Result<(), TryReserveError> {
        debug_assert!(required > self.capacity());
        let mut base = self.into_base();
        let result = if exact {
            // SAFETY: `required > capacity >= len`
            unsafe { base.try_realloc(required) }
        } else {
            base.try_reserve(required - self.len())
        };
        // the (possibly moved) buffer, failure or not
        *self = Self::from_base(&base);
        result
    }

    /// Shrinks the buffer to about `target` elements (`len <= target`).
    ///
    /// # Errors
    ///
    /// If the allocator fails; the buffer is then unchanged.
    ///
    /// # Safety
    ///
    /// The handle must be unique; it may move, the caller stores it back.
    pub unsafe fn try_shrink(&mut self, target: usize) -> Result<(), TryReserveError> {
        debug_assert!(self.len() <= target && target != 0);
        let mut base = self.into_base();
        // SAFETY: `target >= len`
        let result = unsafe { base.try_realloc(target) };
        *self = Self::from_base(&base);
        result
    }
}

#[cfg(test)]
impl<B: Backend> ThinOwner<B> {
    /// A handle over a header built by a test, followed by its data.
    pub(crate) fn from_header_for_tests(header: NonNull<Header<B>>) -> Self {
        // SAFETY: the test provides a header followed by its data
        Self(unsafe { Header::<B>::data(header) }, PhantomData)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::backend::Rc;

    /// A thin header and a few bytes, on the stack: no allocation to leak
    /// when a test panics.
    #[repr(C)]
    struct Fake {
        header: Header<Rc>,
        data: [u8; 8],
    }

    fn fake(count: usize) -> Fake {
        Fake {
            header: Header::<Rc> {
                prefix: crate::backend::Count(core::cell::Cell::new(count)),
                ptr: const_default::ConstDefault::DEFAULT,
                cap: 8,
                len: 3,
            },
            data: *b"abcdefgh",
        }
    }

    #[test]
    #[allow(clippy::clone_on_copy, reason = "covers the impl")]
    fn clone_is_a_copy() {
        let mut f = fake(0);
        let o = ThinOwner::<Rc>::from_header_for_tests(NonNull::from(&mut f).cast());
        assert_eq!(o.clone().as_slice(), b"abc");
        assert_eq!(o.data(), NonNull::from(&mut f.data).cast());
    }

    #[test]
    #[should_panic(expected = "reference count overflow")]
    fn count_overflow() {
        let mut f = fake(usize::MAX - 1);
        let o = ThinOwner::<Rc>::from_header_for_tests(NonNull::from(&mut f).cast());
        let _ = o.try_clone();
    }
}
