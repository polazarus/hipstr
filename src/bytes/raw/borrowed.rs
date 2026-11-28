//! Representation for borrowed slice.

use core::mem::{offset_of, size_of};

use super::TAG_OWNED;

#[cfg(test)]
mod tests;

pub const TAG: usize = TAG_OWNED as usize; // a null pointer tagged with `TAG_OWNED`

/// Borrowed slice representation.
///
/// # Warning!
///
/// For big-endian platform, the reserved word is **after** the slice.
/// For little-endian platform, the reserved word is **before** the slice.
#[derive(Clone, Copy)]
#[repr(C)]
pub struct Borrowed<'borrow> {
    #[cfg(target_endian = "little")]
    tag: usize,

    slice: &'borrow [u8],

    #[cfg(target_endian = "big")]
    tag: usize,
}

impl<'borrow> Borrowed<'borrow> {
    /// Creates a new borrowed representation.
    #[inline]
    pub const fn new(slice: &'borrow [u8]) -> Self {
        const {
            if cfg!(target_endian = "little") {
                assert!(offset_of!(Self, tag) == 0);
            } else {
                assert!(offset_of!(Self, tag) == size_of::<Self>() - size_of::<usize>());
            }
        }

        let this = Self { slice, tag: TAG };
        debug_assert!(this.is_valid());
        this
    }

    /// Returns the length of the underlying data.
    #[inline]
    pub const fn len(&self) -> usize {
        debug_assert!(self.is_valid());
        self.slice.len()
    }

    /// Returns the underlying data as a slice
    #[inline]
    pub const fn as_slice(&self) -> &'borrow [u8] {
        debug_assert!(self.is_valid());
        self.slice
    }

    /// Returns the underlying data as a slice
    #[inline]
    pub const fn as_ptr(&self) -> *const u8 {
        debug_assert!(self.is_valid());
        self.slice.as_ptr()
    }

    /// Return `true` iff this representation is valid.
    #[inline]
    pub const fn is_valid(&self) -> bool {
        self.tag == TAG
    }

    /// Sets the length
    ///
    /// # Safety
    ///
    /// `new_len` must be less than or equal to the current length.
    pub unsafe fn set_len(&mut self, new_len: usize) {
        debug_assert!(self.len() >= new_len, "set_len on borrowed slice");

        // SAFETY: function's safety precondition
        self.slice = unsafe { self.slice.get_unchecked(0..new_len) };
    }
}
