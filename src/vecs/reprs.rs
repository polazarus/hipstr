//! Definitions of various vector representations: thin, wide, and wide-or-thin.
//!
//! This module defines the data structures and associated functions for handling
//! different vector representations:
//! - thin: `ThinRepr`, `ThinHeader`
//! - wide: `WideRepr`, `WideInner`
//! - wide-or-thin: `WideOrThinRepr`, `WideOrThinView`

use core::mem::transmute;
use core::ptr::{self, NonNull};

/// Maximum size of the tag in bits
pub const MAX_TAG_SIZE: usize = 2; // 2 bits

/// Minimal alignment to store the tag
pub const MIN_ALIGN: usize = 1 << MAX_TAG_SIZE; // minimal alignment is 4 bytes

/// Mask to extract the inline tag
pub const INLINE_MASK: usize = 1;

/// Tag for sliced representation (borrowed or allocated)
pub const SLICED: usize = 0b10;

/// Tag for inline representation
pub const INLINE: usize = 1; // 0b01

/// A tagged pointer, guaranted to have a niche at zero, but can be null.
#[repr(transparent)]
pub struct MagicPointer<T, const TAG: usize = SLICED> {
    inner: NonNull<T>,
}

impl<T, const TAG: usize> Copy for MagicPointer<T, TAG> {}

impl<T, const TAG: usize> Clone for MagicPointer<T, TAG> {
    #[cfg_attr(coverage_nightly, coverage(off))]
    fn clone(&self) -> Self {
        *self
    }
}

impl<T, const TAG: usize> MagicPointer<T, TAG> {
    /// Checks if the pointer is null.
    ///
    /// The underlying representation is a tagged null.
    pub(crate) const fn is_null(self) -> bool {
        let addr: usize = unsafe { transmute(self.inner) };
        addr == SLICED
    }

    /// A null magic pointer.
    pub const NULL: Self = Self {
        inner: NonNull::new(ptr::without_provenance_mut(TAG)).unwrap(),
    };

    /// Creates a new magic pointer from a non null pointer.
    pub const fn new(header: NonNull<T>) -> Self {
        Self {
            inner: unsafe { header.byte_add(TAG) },
        }
    }

    /// Gets the underlying pointer, or `None` if null.
    pub const fn get(self) -> Option<NonNull<T>> {
        if self.is_null() {
            None
        } else {
            let ptr = unsafe { self.inner.as_ptr().byte_sub(SLICED) };
            NonNull::new(ptr)
        }
    }

    /// Gets a reference to the underlying data, or `None` if null.
    pub const fn as_ref(&self) -> Option<&T> {
        match self.get() {
            Some(ptr) => unsafe { Some(ptr.as_ref()) },
            None => None,
        }
    }

    /// Gets a mutable reference to the underlying data, or `None` if null.
    #[allow(clippy::needless_pass_by_ref_mut)]
    pub const fn as_mut(&mut self) -> Option<&mut T> {
        match self.get() {
            Some(mut ptr) => unsafe { Some(ptr.as_mut()) },
            None => None,
        }
    }
}
