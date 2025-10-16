//! Internal representation of hip vectors.

use core::marker::PhantomData;
use core::mem::{transmute, MaybeUninit};
use core::ptr::{self, NonNull};

use const_default::ConstDefault;

use crate::vecs::reprs::{FatOrThinRepr, ThinRepr, Variant, INLINE, INLINE_MASK, SLICED};
use crate::vecs::smart_fat::SmartFatVec;
use crate::vecs::smart_thin::SmartThinVec;
use crate::Backend;

pub type Allocated<T, B> = Sliced<T, Owner<T, B>>;

/// Owner of a owned hip vector.
#[repr(transparent)]
pub struct Owner<T, B>(FatOrThinRepr<T, B>);

impl<T, B: Backend> Owner<T, B> {
    /// Drops the owner now.
    ///
    /// # Safety
    ///
    /// The owner must not be used after drop.
    pub unsafe fn drop(&mut self) {
        match self.0.into_split() {
            Variant::Thin(repr) => {
                // SAFETY: should not be used after drop
                let _ = SmartThinVec(repr);
            }
            Variant::Fat(repr) => {
                // SAFETY: should not be used after drop
                let _ = SmartFatVec(repr);
            }
        }
    }

    pub fn is_unique(&self) -> bool {
        self.0.as_ref().unwrap().prefix.is_unique()
    }

    pub const fn is_fat(&self) -> bool {
        self.0.is_fat()
    }

    pub const fn is_thin(&self) -> bool {
        self.0.is_thin()
    }

    pub const fn counter(&self) -> &B {
        &self.0.as_ref().unwrap().prefix
    }

    pub const fn data(&self) -> NonNull<T> {
        if let Some(r) = self.0.as_ref() {
            if let Some(p) = r.ptr {
                p
            } else {
                let repr: &ThinRepr<T, B> = unsafe { &*ptr::from_ref(self).cast() };
                repr.data()
            }
        } else {
            NonNull::dangling()
        }
    }

    /// Sets the length of the owner.
    pub unsafe fn set_len(&mut self, len: usize) {
        if let Some(r) = self.0.as_mut() {
            debug_assert!(len < r.cap);
            r.len = len;
        }
    }

    /// Gets the length of the owner.
    pub const fn len(&self) -> usize {
        if let Some(r) = self.0.as_ref() {
            r.len
        } else {
            0
        }
    }
}

/// Pivot representation.
#[derive(Clone, Copy)]
#[repr(C)]
pub struct Pivot {
    #[cfg(target_endian = "little")]
    tagged_word: NonNull<()>,

    _rest: MaybeUninit<[*mut (); 2]>,

    #[cfg(target_endian = "big")]
    tagged_word: NonNull<()>,
}

impl Pivot {
    /// Checks if the hip vector is inline.
    #[inline]
    pub const fn is_inline(&self) -> bool {
        let word = unsafe { transmute::<NonNull<()>, usize>(self.tagged_word) };
        word & INLINE_MASK == INLINE
    }

    /// Checks if the hip vector is borrowed.
    #[inline]
    pub const fn is_borrowed(&self) -> bool {
        let word = unsafe { transmute::<NonNull<()>, usize>(self.tagged_word) };
        word == SLICED
    }

    /// Checks if the hip vector is allocated (fat or thin).
    #[inline]
    pub const fn is_allocated(&self) -> bool {
        !(self.is_inline() || self.is_borrowed())
    }
}

/// Representation of a borrowed hip vector.
pub type Borrowed<'borrow, T> = Sliced<T, BorrowedTag<'borrow>>;

impl<'borrow, T> Borrowed<'borrow, T> {
    pub const fn new(slice: &'borrow [T]) -> Self {
        Self {
            owner: BorrowedTag::DEFAULT,
            ptr: slice.as_ptr(),
            len: slice.len(),
        }
    }
}

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct BorrowedTag<'borrow> {
    _reserved: BorrowedReserved,
    _marker: PhantomData<&'borrow ()>,
}

impl ConstDefault for BorrowedTag<'_> {
    const DEFAULT: Self = Self {
        _reserved: BorrowedReserved::Value,
        _marker: PhantomData,
    };
}

#[derive(Clone, Copy)]
#[repr(usize)]
pub enum BorrowedReserved {
    Value = SLICED,
}

/// Representation of a sliced hip vector, that is, a non inline hip vector.
#[repr(C)]
pub struct Sliced<T, O> {
    #[cfg(target_endian = "little")]
    pub owner: O,

    pub ptr: *const T,
    pub len: usize,

    #[cfg(target_endian = "big")]
    pub owner: O,
}

impl<T, O> Sliced<T, O> {
    pub const fn as_ptr(&self) -> *const T {
        self.ptr
    }

    pub const fn len(&self) -> usize {
        self.len
    }

    pub const fn as_slice(&self) -> &[T] {
        unsafe { core::slice::from_raw_parts(self.ptr, self.len) }
    }
}

pub type UnknownSliced<T> = Sliced<T, NonNull<()>>;
