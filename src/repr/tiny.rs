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
use crate::backend::Backend;
use crate::thin::TryReserveError;

type Inline = crate::inline_buf::Tiny;

const _: () = {
    assert!(size_of::<Inline>() == size_of::<usize>());
    assert!(size_of::<Owner<crate::backend::Rc>>() == size_of::<usize>());
};

/// 1-word copy-on-write sequence (see the module documentation).
#[repr(transparent)]
pub struct Tiny<B: Backend> {
    word: NonNull<()>,
    marker: PhantomData<Owner<B>>,
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

    const fn from_owner(owner: Owner<B>) -> Self {
        debug_assert!(owner.is_some());
        Self {
            // SAFETY: same size, a non-null owner is a tagged non-null pointer
            word: unsafe { transmute::<Owner<B>, NonNull<()>>(owner) },
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
    const fn owner(&self) -> Owner<B> {
        // SAFETY: heap case, same size
        unsafe { transmute::<NonNull<()>, Owner<B>>(self.word) }
    }

    #[inline]
    const fn owner_mut(&mut self) -> &mut Owner<B> {
        // SAFETY: heap case, same size
        unsafe { transmute::<&mut NonNull<()>, &mut Owner<B>>(&mut self.word) }
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
        let owner = Owner::<B>::try_with_capacity(capacity)?;
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
    const WORDS: usize = 1;
    const INLINE_CAPACITY: usize = Inline::CAPACITY;
    const MAX_LEN: usize = isize::MAX as usize;
    const BORROWS: bool = false;

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
        if vec.len() <= Inline::CAPACITY {
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
    fn as_borrowed(&self) -> Option<&'a [u8]> {
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
        this.owner().into_vec()
    }

    fn is_unique(&self) -> bool {
        self.is_inline() || self.owner().is_unique()
    }

    fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        let len = self.len();
        let required = len.checked_add(additional).ok_or(capacity_overflow())?;
        if self.is_inline() {
            if required > Inline::CAPACITY {
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
}
