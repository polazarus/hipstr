//! Shared heap handle, common to all representations.
//!
//! An [`Owner`] is one tagged word pointing to a reference-counted header.
//! The header is either
//!
//! - **thin**: the elements follow the header in the same allocation
//!   (`header.ptr` is `None`), or
//! - **vec**: the header is boxed separately and points to the buffer of an
//!   adopted [`Vec`] (`header.ptr` is `Some`), which keeps `From<Vec<T>>` and
//!   [`Owner::into_vec`] in O(1).
//!
//! The pointer is tagged with `0b10`: bit 0 is always clear so the word can
//! share its slot with a "low" inline layout, and the word is never zero, which
//! gives the surrounding types a niche. The null owner (the tag alone) is only
//! used by the 3-word representation, to mean "borrowed".

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::marker::PhantomData;
use core::mem::{ManuallyDrop, transmute};
use core::ptr::NonNull;

use crate::next::backend::{Backend, Counter, UpdateResult};
use crate::next::common::header::{Header, ThinHeader};
use crate::next::common::tagged_pointer::TaggedPointer;
use crate::next::thin::{self, TryReserveError, TryReserveErrorKind};

/// Owner tag.
pub const TAG: usize = 0b10;

/// Header as seen through an owner, thin or vec.
pub type VecHeader<T, B> = Header<T, <B as Backend>::Counter, Option<NonNull<T>>>;

/// Thin vector base with the backend's counter as prefix.
pub type ThinBase<T, B> = thin::Base<T, <B as Backend>::Counter>;

/// Heap kind of an owner.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HeapKind {
    Thin,
    Vec,
}

/// Shared heap handle (see the module documentation).
///
/// This type is `Copy` on purpose: copying it does **not** touch the counter.
/// Use [`Owner::try_clone`] and [`Owner::release`] for the reference-counting
/// operations.
#[repr(transparent)]
pub struct Owner<T: Copy, B: Backend>(TaggedPointer<VecHeader<T, B>, TAG>, PhantomData<B>);

impl<T: Copy, B: Backend> Copy for Owner<T, B> {}
impl<T: Copy, B: Backend> Clone for Owner<T, B> {
    fn clone(&self) -> Self {
        *self
    }
}

const _: () = {
    type B = crate::next::backend::Rc;
    assert!(size_of::<Owner<u8, B>>() == size_of::<usize>());
    assert!(size_of::<Option<Owner<u8, B>>>() == size_of::<usize>());
    assert!(size_of::<ThinBase<u8, B>>() == size_of::<Owner<u8, B>>());
};

impl<T: Copy, B: Backend> Owner<T, B> {
    /// Null owner, only used as "borrowed" marker by the 3-word representation.
    pub const NONE: Self = Self(TaggedPointer::null(), PhantomData);

    /// Wraps a non-empty thin vector.
    ///
    /// The thin vector must have an allocation (non-zero capacity).
    pub const fn from_thin(thin: ThinBase<T, B>) -> Self {
        // SAFETY: same tagged-pointer representation; `ThinHeader` and
        // `VecHeader` share their layout, a thin header's `ptr` being zero,
        // i.e. `None`.
        let this = unsafe { transmute::<ThinBase<T, B>, Self>(thin) };
        debug_assert!(this.is_some(), "thin owner must be allocated");
        this
    }

    /// Adopts the buffer of a vector, without copying.
    pub fn from_vec(vec: Vec<T>) -> Self {
        debug_assert!(vec.capacity() != 0 && size_of::<T>() != 0);
        Self(TaggedPointer::from(Header::from_vec(vec)), PhantomData)
    }

    /// Allocates a thin owner holding a copy of `slice`.
    pub fn from_slice(slice: &[T]) -> Self {
        debug_assert!(!slice.is_empty());
        Self::from_thin(ThinBase::<T, B>::from_slice_copy(slice))
    }

    /// Allocates a thin owner with room for `capacity` elements.
    pub fn try_with_capacity(capacity: usize) -> Result<Self, TryReserveError> {
        debug_assert!(capacity != 0);
        ThinBase::<T, B>::try_with_capacity(capacity).map(Self::from_thin)
    }

    #[inline]
    pub const fn is_some(self) -> bool {
        self.0.as_non_null().is_some()
    }

    #[inline]
    pub const fn is_none(self) -> bool {
        !self.is_some()
    }

    #[inline]
    const fn header_ptr(self) -> NonNull<VecHeader<T, B>> {
        match self.0.as_non_null() {
            Some(ptr) => ptr,
            None => panic!("null owner"),
        }
    }

    #[inline]
    pub const fn header(&self) -> &VecHeader<T, B> {
        // SAFETY: type invariant, a non-null owner points to a live header
        unsafe { self.header_ptr().as_ref() }
    }

    #[inline]
    pub const fn kind(self) -> HeapKind {
        if self.header().ptr.is_none() {
            HeapKind::Thin
        } else {
            HeapKind::Vec
        }
    }

    /// Pointer to the first element of the owned buffer.
    #[inline]
    pub const fn data(self) -> NonNull<T> {
        match self.header().ptr {
            Some(ptr) => ptr,
            // SAFETY: thin header, data follows in the same allocation
            None => unsafe { ThinHeader::<T, B::Counter>::data(self.header_ptr().cast()) },
        }
    }

    #[inline]
    pub const fn len(self) -> usize {
        self.header().len
    }

    #[inline]
    pub const fn capacity(self) -> usize {
        self.header().cap
    }

    /// The owned elements (the full buffer, not a slice of it).
    #[inline]
    pub const fn as_slice<'a>(self) -> &'a [T] {
        // SAFETY: type invariant, the first `len` elements are initialized
        unsafe { core::slice::from_raw_parts(self.data().as_ptr(), self.len()) }
    }

    #[inline]
    pub fn is_unique(self) -> bool {
        self.header().prefix.is_unique()
    }

    /// Sets the length of the owned buffer.
    ///
    /// # Safety
    ///
    /// The owner must be unique, `len <= capacity` and the elements initialized.
    #[inline]
    pub const unsafe fn set_len(self, len: usize) {
        debug_assert!(len <= self.capacity());
        // SAFETY: precondition, unique access
        unsafe {
            (*self.header_ptr().as_ptr()).len = len;
        }
    }

    /// Increments the reference count and returns a new handle.
    ///
    /// Returns `None` if the count cannot be incremented and the backend asks
    /// for a deep copy instead (e.g. [`Unique`](crate::next::backend::Unique)).
    ///
    /// # Panics
    ///
    /// Panics on counter overflow for backends that panic on overflow.
    #[inline]
    pub fn try_clone(self) -> Option<Self> {
        match self.header().prefix.incr() {
            UpdateResult::Done => Some(self),
            UpdateResult::Overflow if B::PANIC_ON_OVERFLOW => {
                panic!("reference count overflow")
            }
            UpdateResult::Overflow => None,
        }
    }

    /// Decrements the reference count, freeing the allocation(s) on the last
    /// release.
    ///
    /// # Safety
    ///
    /// The handle must not be used afterwards.
    pub unsafe fn release(self) {
        if self.header().prefix.decr() == UpdateResult::Overflow {
            // SAFETY: last handle
            unsafe { self.free() }
        }
    }

    /// Frees the allocation(s), regardless of the count.
    ///
    /// # Safety
    ///
    /// Must be the last handle, which is not used afterwards.
    unsafe fn free(self) {
        match self.kind() {
            HeapKind::Thin => {
                let mut thin = unsafe { transmute::<Self, ThinBase<T, B>>(self) };
                // SAFETY: last handle; elements are `Copy`, nothing to drop
                unsafe { thin.drop_container() }
            }
            HeapKind::Vec => {
                // SAFETY: last handle, the header was boxed by `Header::from_vec`
                let header = unsafe { Box::from_raw(self.header_ptr().as_ptr()) };
                let ptr = header.ptr.unwrap();
                // SAFETY: rebuilds the adopted vector, length 0 since `T: Copy`
                drop(unsafe { Vec::from_raw_parts(ptr.as_ptr(), 0, header.cap) });
            }
        }
    }

    /// Converts into a vector, in O(1) for a unique vec owner, otherwise by
    /// copying the owned elements.
    pub fn into_vec(self) -> Vec<T> {
        if self.kind() == HeapKind::Vec && self.is_unique() {
            // SAFETY: unique vec owner, the header was boxed by `Header::from_vec`
            let header = unsafe { Box::from_raw(self.header_ptr().as_ptr()) };
            // SAFETY: rebuilds the adopted vector with its current length
            unsafe { Vec::from_raw_parts(header.ptr.unwrap().as_ptr(), header.len, header.cap) }
        } else {
            let vec = self.as_slice().to_vec();
            // SAFETY: the handle is consumed
            unsafe { self.release() };
            vec
        }
    }

    /// Ensures room for `required` elements in total.
    ///
    /// # Safety
    ///
    /// The owner must be unique. The handle may move: the caller must store
    /// the updated `self` back.
    pub unsafe fn try_grow(&mut self, required: usize) -> Result<(), TryReserveError> {
        let additional = required.saturating_sub(self.len());
        match self.kind() {
            HeapKind::Thin => {
                // SAFETY: same representation, unique access
                let thin = unsafe { transmute::<&mut Self, &mut ThinBase<T, B>>(self) };
                thin.try_reserve(additional)
            }
            HeapKind::Vec => {
                let mut header = self.header_ptr();
                // SAFETY: unique access to a vec header
                let header = unsafe { header.as_mut() };
                // SAFETY: rebuilds the adopted vector temporarily
                let mut vec = ManuallyDrop::new(unsafe {
                    Vec::from_raw_parts(header.ptr.unwrap().as_ptr(), header.len, header.cap)
                });
                let result = vec
                    .try_reserve(additional)
                    .map_err(|_| TryReserveError(TryReserveErrorKind::CapacityOverflow));
                header.ptr = NonNull::new(vec.as_mut_ptr());
                header.cap = vec.capacity();
                result
            }
        }
    }
}
