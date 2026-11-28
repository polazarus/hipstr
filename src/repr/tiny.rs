//! 1-word representation: inline or heap; no borrowing, no slicing.
//!
//! ```text
//! inline     [tagged len|data...]     bit 0 = 1 (the length byte is the least significant)
//! heap       [data ptr + 0b10]        bits 1..0 = 0b10
//! ```
//!
//! Borrowed slices are copied: a single word cannot hold a pointer and a
//! length. Heap values are always thin buffers (no adopted `Vec`); the word
//! is the (tagged) pointer to their data, the length is read from the header,
//! at a constant offset before it.

use alloc::vec::Vec;
use core::marker::PhantomData;
use core::mem::transmute;
use core::ptr::NonNull;

use super::parts::{InlineBytes, Parts, ThinView};
use super::thin_owner::ThinOwner;
use super::{HeapKind, Kind, Repr, capacity_overflow};
use crate::backend::Backend;
use crate::thin::TryReserveError;

type Inline = crate::inline_buf::Tiny;

/// Tag of heap words, added to the (word-aligned) data pointer.
const HEAP_TAG: usize = 0b10;

const _: () = {
    assert!(size_of::<Inline>() == size_of::<usize>());
    assert!(size_of::<ThinOwner<crate::backend::Rc>>() == size_of::<usize>());
};

/// 1-word copy-on-write sequence (see the module documentation).
#[repr(transparent)]
pub struct Tiny<B: Backend> {
    word: NonNull<()>,
    marker: PhantomData<ThinOwner<B>>,
}

const _: () = {
    type W = Tiny<crate::backend::Rc>;
    assert!(size_of::<W>() == size_of::<usize>());
    assert!(size_of::<Option<W>>() == size_of::<W>());
};

// SAFETY: see `Wide`
unsafe impl<B: Backend> Send for Tiny<B> where B::Counter: Send + Sync {}
// SAFETY: see `Wide`
unsafe impl<B: Backend> Sync for Tiny<B> where B::Counter: Send + Sync {}

impl<B: Backend> Tiny<B> {
    const fn from_inline(inline: Inline) -> Self {
        Self {
            // SAFETY: same size, an inline word is tagged and non-zero
            word: unsafe { transmute::<Inline, NonNull<()>>(inline) },
            marker: PhantomData,
        }
    }

    const fn from_owner(owner: ThinOwner<B>) -> Self {
        Self {
            // SAFETY: the data pointer is word-aligned, the tag fits its low
            // bits (the result stays in the allocation's provenance, and is
            // even: not inline)
            word: unsafe { owner.data().byte_add(HEAP_TAG).cast() },
            marker: PhantomData,
        }
    }

    #[inline]
    pub const fn new() -> Self {
        Self::from_inline(Inline::new())
    }

    /// Copies `slice` inline, in a `const` context too.
    ///
    /// # Panics
    ///
    /// Panics if `slice` is longer than the inline capacity.
    #[inline]
    pub const fn inline_copy(slice: &[u8]) -> Self {
        assert!(slice.len() <= Inline::CAPACITY, "too long to be inlined");
        Self::from_inline(Inline::from_slice_copy(slice))
    }

    #[inline]
    pub const fn is_inline(&self) -> bool {
        super::word_bits(&self.word) & 1 == 1
    }

    /// Always `false`: this representation never borrows.
    #[inline]
    pub const fn is_borrowed(&self) -> bool {
        false
    }

    #[inline]
    pub const fn is_heap(&self) -> bool {
        !self.is_inline()
    }

    /// Always `None`: this representation never borrows.
    #[inline]
    pub const fn borrowed_slice<'a>(&self) -> Option<&'a [u8]> {
        None
    }

    #[inline]
    const fn inline(&self) -> &Inline {
        // SAFETY: inline case, same size
        unsafe { transmute::<&NonNull<()>, &Inline>(&self.word) }
    }

    #[inline]
    const fn inline_mut(&mut self) -> &mut Inline {
        // SAFETY: inline case, same size
        unsafe { transmute::<&mut NonNull<()>, &mut Inline>(&mut self.word) }
    }

    #[inline]
    const fn owner(&self) -> ThinOwner<B> {
        // SAFETY: heap case, the word is the data pointer plus the tag
        unsafe { ThinOwner::from_data(self.word.byte_sub(HEAP_TAG).cast()) }
    }

    /// Runs `f` on the handle (heap case), then stores it back: it may
    /// move, whatever `f` returns, even if `f` panics (the guard stores it
    /// back while unwinding, so the word never points to a moved buffer).
    #[inline]
    fn with_owner<T>(&mut self, f: impl FnOnce(&mut ThinOwner<B>) -> T) -> T {
        /// Stores the handle back into the word when dropped.
        struct StoreBack<'t, B: Backend> {
            tiny: &'t mut Tiny<B>,
            owner: ThinOwner<B>,
        }

        impl<B: Backend> Drop for StoreBack<'_, B> {
            fn drop(&mut self) {
                // the word only: the old value is not dropped (same buffer)
                self.tiny.word = core::mem::ManuallyDrop::new(Tiny::from_owner(self.owner)).word;
            }
        }

        let mut guard = StoreBack {
            owner: self.owner(),
            tiny: self,
        };
        f(&mut guard.owner)
    }

    #[inline]
    pub const fn len(&self) -> usize {
        if self.is_inline() {
            self.inline().len()
        } else {
            self.owner().len()
        }
    }

    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    pub const fn as_slice(&self) -> &[u8] {
        if self.is_inline() {
            self.inline().as_slice()
        } else {
            self.owner().as_slice()
        }
    }

    /// Copies `slice` to a new heap buffer; kept out of line so that the
    /// inline path of `from_slice` stays small enough to be inlined.
    #[inline(never)]
    fn heap_from_slice(slice: &[u8]) -> Self {
        crate::thin::unwrap_or_oom(Self::try_from_slice(slice, slice.len()))
    }

    fn try_from_slice(slice: &[u8], capacity: usize) -> Result<Self, TryReserveError> {
        debug_assert!(capacity >= slice.len());
        if capacity <= Inline::CAPACITY {
            return Ok(Self::from_inline(Inline::from_slice_copy(slice)));
        }
        let owner = ThinOwner::<B>::try_with_capacity(capacity)?;
        // SAFETY: fresh unique owner with enough capacity
        unsafe {
            owner
                .data()
                .as_ptr()
                .copy_from_nonoverlapping(slice.as_ptr(), slice.len());
            owner.set_len(slice.len());
        }
        Ok(Self::from_owner(owner))
    }
}

impl<B: Backend> Default for Tiny<B> {
    fn default() -> Self {
        Self::new()
    }
}

impl<B: Backend> Clone for Tiny<B> {
    fn clone(&self) -> Self {
        if !self.is_inline() && self.owner().try_clone().is_none() {
            return crate::thin::unwrap_or_oom(Self::try_from_slice(self.as_slice(), self.len()));
        }
        Self {
            word: self.word,
            marker: PhantomData,
        }
    }
}

impl<B: Backend> Drop for Tiny<B> {
    fn drop(&mut self) {
        if !self.is_inline() {
            // SAFETY: this handle is dropped
            unsafe { self.owner().release() };
        }
    }
}

// SAFETY: see the trait's contract, upheld by `try_reserve`
unsafe impl<'a, B: Backend> Repr<'a> for Tiny<B> {
    type Owned = Self;
    type Backend = B;
    const WORDS: usize = 1;
    const INLINE_CAPACITY: usize = Inline::CAPACITY;
    const MAX_LEN: usize = isize::MAX as usize;
    const BORROWS: bool = false;
    const ADOPTS_VEC: bool = false;

    fn into_parts(self) -> Parts<'a, B> {
        let this = core::mem::ManuallyDrop::new(self);
        if this.is_inline() {
            return Parts::Inline(InlineBytes::new(this.as_slice()));
        }
        // the reference held by `self` moves to the parts
        let owner = this.owner();
        Parts::Thin(ThinView {
            base: owner.into_base(),
            start: 0,
            len: owner.len(),
        })
    }

    fn try_from_parts(parts: Parts<'a, B>) -> Result<Self, Parts<'a, B>> {
        let len = parts.as_slice().len();
        // the length lives in the header: the view must be the whole
        // buffer, or a prefix of a unique one (then truncated)
        let base = match &parts {
            // inline, or a short heap view: copied inline (normalized), the
            // parts released
            _ if len <= Inline::CAPACITY => {
                return Ok(Self::from_inline(Inline::from_slice_copy(parts.as_slice())));
            }
            Parts::Thin(view)
                if view.start == 0
                    && (len == view.base.len()
                        || crate::backend::Counter::is_unique(view.base.prefix())) =>
            {
                view.base.0
            }
            _ => return Err(parts),
        };
        // the reference held by the parts moves to the result
        core::mem::forget(parts);
        let owner = ThinOwner::from_base(&crate::thin::Base(base));
        // SAFETY: unique (or unchanged length), shorter initialized prefix
        unsafe { owner.set_len(len) };
        Ok(Self::from_owner(owner))
    }

    #[inline]
    fn new() -> Self {
        Self::new()
    }

    #[inline]
    fn from_slice(slice: &[u8]) -> Self {
        if slice.len() <= Inline::CAPACITY {
            Self::from_inline(Inline::from_slice_copy(slice))
        } else {
            Self::heap_from_slice(slice)
        }
    }

    #[inline]
    fn from_borrowed(slice: &'a [u8]) -> Self {
        <Self as Repr<'a>>::from_slice(slice)
    }

    fn from_vec(vec: Vec<u8>) -> Self {
        // thin buffers only: a copy
        <Self as Repr<'a>>::from_slice(&vec)
    }

    #[inline]
    fn into_owned(self) -> Self {
        self
    }

    #[inline]
    fn as_borrowed(&self) -> Option<&'a [u8]> {
        None
    }

    fn kind(&self) -> Kind {
        if self.is_inline() {
            Kind::Inline
        } else {
            Kind::Heap(HeapKind::Thin)
        }
    }

    #[inline]
    fn as_slice(&self) -> &[u8] {
        self.as_slice()
    }

    #[inline]
    fn len(&self) -> usize {
        self.len()
    }

    fn into_vec(self) -> Vec<u8> {
        if self.is_inline() {
            return self.as_slice().to_vec();
        }
        let this = core::mem::ManuallyDrop::new(self);
        this.owner().into_vec_prefix(this.len())
    }

    fn is_unique(&self) -> bool {
        self.is_inline() || self.owner().is_unique()
    }

    fn try_reserve_with(&mut self, additional: usize, exact: bool) -> Result<(), TryReserveError> {
        let len = self.len();
        let required = len.checked_add(additional).ok_or(capacity_overflow())?;
        if self.is_inline() {
            if required > Inline::CAPACITY {
                *self = Self::try_from_slice(self.as_slice(), required)?;
            }
        } else if self.owner().is_unique() {
            if required > self.owner().capacity() {
                // SAFETY: unique owner, the updated handle is stored back
                self.with_owner(|o| unsafe { o.try_grow(required, exact) })?;
            }
        } else {
            *self = Self::try_from_slice(self.as_slice(), required)?;
        }
        Ok(())
    }

    fn try_shrink_in_place(&mut self, target: usize) -> Result<bool, TryReserveError> {
        if self.is_inline() || !self.owner().is_unique() {
            return Ok(false);
        }
        // SAFETY: unique owner, the updated handle is stored back
        self.with_owner(|o| unsafe { o.try_shrink(target) })?;
        Ok(true)
    }

    #[inline]
    fn is_partial_view(&self) -> bool {
        // no per-handle length: always the whole buffer
        false
    }

    #[inline]
    fn shrink_view(&mut self, _len: usize) -> bool {
        // a single word has no room for a per-handle length
        false
    }

    fn capacity(&self) -> usize {
        if self.is_inline() {
            Inline::CAPACITY
        } else {
            self.owner().capacity()
        }
    }

    unsafe fn as_mut_ptr(&mut self) -> *mut u8 {
        if self.is_inline() {
            self.inline_mut().as_mut_ptr()
        } else {
            self.owner().data().as_ptr()
        }
    }

    unsafe fn set_len(&mut self, len: usize) {
        if self.is_inline() {
            // SAFETY: precondition
            unsafe { self.inline_mut().set_len(len) };
        } else {
            // SAFETY: precondition, unique owner
            unsafe { self.owner().set_len(len) };
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::backend::Unique;

    #[test]
    fn default_and_unique_clone() {
        assert_eq!(Tiny::<Unique>::default().len(), 0);
        // a unique owner cannot be shared: cloning copies
        let long = [7u8; 100];
        let a = Tiny::<Unique>::from_slice(&long);
        let b = a.clone();
        assert_eq!(b.as_slice(), &long[..]);
        assert_ne!(a.as_slice().as_ptr(), b.as_slice().as_ptr());
    }

    #[cfg(feature = "std")]
    #[test]
    fn with_owner_stores_back_on_panic() {
        let mut t = Tiny::<crate::backend::Rc>::from_slice(&[7; 32]);
        let result = std::panic::catch_unwind(core::panic::AssertUnwindSafe(|| {
            t.with_owner(|owner| {
                // moves the buffer, then panics before returning
                // SAFETY: unique, more than the capacity
                unsafe { owner.try_grow(4096, true) }.unwrap();
                panic!("after moving the buffer");
            })
        }));
        assert!(result.is_err());
        // the word follows the moved buffer
        assert_eq!(t.as_slice(), &[7; 32]);
        assert!(t.capacity() >= 4096);
    }
}
