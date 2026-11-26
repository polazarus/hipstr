//! 1-word representation: inline or heap; no borrowing, no slicing.
//!
//! ```text
//! inline     [tagged len|data...]     bit 0 = 1 (the length byte is the least significant)
//! heap       [owner]                  bits 1..0 = 0b10
//! ```
//!
//! Borrowed slices are copied: a single word cannot hold a pointer and a
//! length. The heap length is read from the header.

use alloc::vec::Vec;
use core::marker::PhantomData;
use core::mem::transmute;
use core::ptr::NonNull;

use super::owner::Owner;
use super::{Kind, Repr, capacity_overflow};
use crate::next::backend::Backend;
use crate::next::inline::base::Base as InlineBase;
use crate::next::inline::layouts::TinyLayout;
use crate::next::thin::TryReserveError;

type Inline<T> = InlineBase<T, TinyLayout>;

const _: () = {
    assert!(size_of::<Inline<u8>>() == size_of::<usize>());
    assert!(size_of::<Owner<u8, crate::next::backend::Rc>>() == size_of::<usize>());
};

/// 1-word copy-on-write sequence (see the module documentation).
#[repr(transparent)]
pub struct Tiny<T: Copy + 'static, B: Backend> {
    word: NonNull<()>,
    marker: PhantomData<Owner<T, B>>,
}

const _: () = {
    type W = Tiny<u8, crate::next::backend::Rc>;
    assert!(size_of::<W>() == size_of::<usize>());
    assert!(size_of::<Option<W>>() == size_of::<W>());
};

// SAFETY: see `Wide`
unsafe impl<T: Copy + Send + Sync + 'static, B: Backend> Send for Tiny<T, B> where
    B::Counter: Send + Sync
{
}
// SAFETY: see `Wide`
unsafe impl<T: Copy + Send + Sync + 'static, B: Backend> Sync for Tiny<T, B> where
    B::Counter: Send + Sync
{
}

impl<T: Copy + 'static, B: Backend> Tiny<T, B> {
    const fn from_inline(inline: Inline<T>) -> Self {
        Self {
            // SAFETY: same size, an inline word is tagged and non-zero
            word: unsafe { transmute::<Inline<T>, NonNull<()>>(inline) },
            marker: PhantomData,
        }
    }

    const fn from_owner(owner: Owner<T, B>) -> Self {
        debug_assert!(owner.is_some());
        Self {
            // SAFETY: same size, a non-null owner is a tagged non-null pointer
            word: unsafe { transmute::<Owner<T, B>, NonNull<()>>(owner) },
            marker: PhantomData,
        }
    }

    #[inline]
    pub const fn new() -> Self {
        Self::from_inline(Inline::new())
    }

    #[inline]
    pub const fn is_inline(&self) -> bool {
        super::word_bits(&self.word) & 1 == 1
    }

    #[inline]
    const fn inline(&self) -> &Inline<T> {
        // SAFETY: inline case, same size
        unsafe { transmute::<&NonNull<()>, &Inline<T>>(&self.word) }
    }

    #[inline]
    const fn inline_mut(&mut self) -> &mut Inline<T> {
        // SAFETY: inline case, same size
        unsafe { transmute::<&mut NonNull<()>, &mut Inline<T>>(&mut self.word) }
    }

    #[inline]
    const fn owner(&self) -> Owner<T, B> {
        // SAFETY: heap case, same size
        unsafe { transmute::<NonNull<()>, Owner<T, B>>(self.word) }
    }

    #[inline]
    const fn owner_mut(&mut self) -> &mut Owner<T, B> {
        // SAFETY: heap case, same size
        unsafe { transmute::<&mut NonNull<()>, &mut Owner<T, B>>(&mut self.word) }
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
    pub const fn as_slice(&self) -> &[T] {
        if self.is_inline() {
            self.inline().as_slice()
        } else {
            self.owner().as_slice()
        }
    }

    fn try_from_slice(slice: &[T], capacity: usize) -> Result<Self, TryReserveError> {
        debug_assert!(capacity >= slice.len());
        if capacity <= Inline::<T>::CAPACITY {
            return Ok(Self::from_inline(Inline::from_slice_copy(slice)));
        }
        let owner = Owner::<T, B>::try_with_capacity(capacity)?;
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

impl<T: Copy + 'static, B: Backend> Default for Tiny<T, B> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Copy + 'static, B: Backend> Clone for Tiny<T, B> {
    fn clone(&self) -> Self {
        if !self.is_inline() && self.owner().try_clone().is_none() {
            return Self::try_from_slice(self.as_slice(), self.len())
                .unwrap_or_else(|e| crate::next::thin::unwrap_or_oom(Err(e)));
        }
        Self {
            word: self.word,
            marker: PhantomData,
        }
    }
}

impl<T: Copy + 'static, B: Backend> Drop for Tiny<T, B> {
    fn drop(&mut self) {
        if !self.is_inline() {
            // SAFETY: this handle is dropped
            unsafe { self.owner().release() };
        }
    }
}

// SAFETY: see the trait's contract, upheld by `try_reserve`
unsafe impl<'a, T: Copy + 'static, B: Backend> Repr<'a, T> for Tiny<T, B> {
    type Owned = Self;
    const WORDS: usize = 1;
    const INLINE_CAPACITY: usize = Inline::<T>::CAPACITY;
    const MAX_LEN: usize = isize::MAX as usize;
    const BORROWS: bool = false;

    #[inline]
    fn new() -> Self {
        Self::new()
    }

    fn from_slice(slice: &[T]) -> Self {
        crate::next::thin::unwrap_or_oom(Self::try_from_slice(slice, slice.len()))
    }

    #[inline]
    fn from_borrowed(slice: &'a [T]) -> Self {
        <Self as Repr<'a, T>>::from_slice(slice)
    }

    fn from_vec(vec: Vec<T>) -> Self {
        if vec.len() <= Inline::<T>::CAPACITY {
            Self::from_inline(Inline::from_slice_copy(&vec))
        } else {
            Self::from_owner(Owner::from_vec(vec))
        }
    }

    #[inline]
    fn into_owned(self) -> Self {
        self
    }

    #[inline]
    fn as_borrowed(&self) -> Option<&'a [T]> {
        None
    }

    fn kind(&self) -> Kind {
        if self.is_inline() {
            Kind::Inline
        } else {
            Kind::Heap(self.owner().kind())
        }
    }

    #[inline]
    fn as_slice(&self) -> &[T] {
        self.as_slice()
    }

    #[inline]
    fn len(&self) -> usize {
        self.len()
    }

    fn into_vec(self) -> Vec<T> {
        if self.is_inline() {
            return self.as_slice().to_vec();
        }
        let this = core::mem::ManuallyDrop::new(self);
        this.owner().into_vec()
    }

    fn is_unique(&self) -> bool {
        self.is_inline() || self.owner().is_unique()
    }

    fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        let len = self.len();
        let required = len.checked_add(additional).ok_or(capacity_overflow())?;
        if self.is_inline() {
            if required > Inline::<T>::CAPACITY {
                *self = Self::try_from_slice(self.as_slice(), required)?;
            }
        } else if self.owner().is_unique() {
            if required > self.owner().capacity() {
                // SAFETY: unique owner, the updated handle is stored back in place
                unsafe { self.owner_mut().try_grow(required)? };
            }
        } else {
            *self = Self::try_from_slice(self.as_slice(), required)?;
        }
        Ok(())
    }

    fn capacity(&self) -> usize {
        if self.is_inline() {
            Inline::<T>::CAPACITY
        } else {
            self.owner().capacity()
        }
    }

    unsafe fn as_mut_ptr(&mut self) -> *mut T {
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
