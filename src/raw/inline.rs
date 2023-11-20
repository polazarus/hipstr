//! Inline representation.

use core::mem::MaybeUninit;
use core::ptr::copy_nonoverlapping;

#[cfg(test)]
mod tests;

/// Inline representation.
///
/// # Warning!
///
/// For big-endian platform, the shifted length is **after** the data.
/// For little-endian platform, the shifted length is **before** the data.
#[derive(Clone, Copy)]
#[repr(C)]
pub struct Inline<const INLINE_CAPACITY: usize> {
    #[cfg(target_endian = "little")]
    shifted_len: u8,

    data: [MaybeUninit<u8>; INLINE_CAPACITY],

    #[cfg(target_endian = "big")]
    shifted_len: u8,
}

impl<const INLINE_CAPACITY: usize> Inline<INLINE_CAPACITY> {
    /// Creates a new empty `Inline`.
    #[inline]
    pub const fn empty() -> Self {
        // SAFETY: just a noop hack to construct an array of MaybeUninit
        let data = unsafe { MaybeUninit::uninit().assume_init() };
        // waiting for stabilization of MaybeUninit::uninit_array
        // or inline const expression

        #[allow(clippy::inconsistent_struct_constructor)]
        Self {
            data,
            shifted_len: 1,
        }
    }

    /// Creates a new empty `Inline`.
    #[inline]
    pub fn zeroed(len: usize) -> Self {
        // TODO waiting for const-stabilization of MaybeUninit::zeroed

        // SAFETY: just a hack to construct a zeroed array of MaybeUninit
        let data = unsafe { MaybeUninit::zeroed().assume_init() };

        assert!(len <= INLINE_CAPACITY, "invalid length");

        #[allow(clippy::cast_possible_truncation)]
        let shifted_len = ((len << 1) | 1) as u8;

        #[allow(clippy::inconsistent_struct_constructor)]
        Self { data, shifted_len }
    }

    /// Creates a new `Inline` string by copying a byte slice.
    #[inline]
    #[allow(dead_code)]
    pub fn new(sl: &[u8]) -> Self {
        assert!(sl.len() <= INLINE_CAPACITY);
        unsafe { Self::new_unchecked(sl) }
    }

    /// Creates a new `Inline` string by copying a short byte slice.
    ///
    /// # Safety
    ///
    /// The input slice's length MUST be at most `INLINE_CAPACITY`.
    #[inline]
    pub unsafe fn new_unchecked(sl: &[u8]) -> Self {
        let len = sl.len();

        // SAFETY: just a noop hack to construct an array of MaybeUninit
        let mut data: [MaybeUninit<u8>; INLINE_CAPACITY] =
            unsafe { MaybeUninit::uninit().assume_init() };
        // waiting for stabilization of MaybeUninit::uninit_array
        // or inline const expression

        // SAFETY: sl's length is a **function precondition**
        unsafe {
            copy_nonoverlapping(sl.as_ptr(), data.as_mut_ptr().cast(), len);
        }

        #[allow(clippy::cast_possible_truncation)]
        let shifted_len = ((len << 1) | 1) as u8;

        #[allow(clippy::inconsistent_struct_constructor)]
        Self { data, shifted_len }
    }

    /// Returns the length of this inline string.
    #[inline]
    pub const fn len(&self) -> usize {
        debug_assert!(self.is_valid());

        (self.shifted_len >> 1) as usize
    }

    /// Returns an immutable view of this inline string.
    #[inline]
    pub const fn as_slice(&self) -> &[u8] {
        debug_assert!(self.is_valid());

        // XXX could be done with less unsafe one day:
        // waiting for const_slice_index and maybe_uninit_slice
        let data = self.data.as_ptr();
        let len = self.len();

        // SAFETY: type invariant (the first `len`-th bytes are initialized)
        unsafe { core::slice::from_raw_parts(data.cast(), len) }
    }

    /// Returns an immutable raw pointer of this inline string.
    #[inline]
    pub const fn as_ptr(&self) -> *const u8 {
        debug_assert!(self.is_valid());
        self.data.as_ptr().cast()
    }

    /// Returns a mutable view of this inline string.
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        // XXX should add const: waiting for const_mut_refs

        debug_assert!(self.is_valid());

        // XXX could be done without less unsafe: maybe_uninit_slice
        // and const-ly: const_mut_refs, const_slice_index
        let data = self.data.as_mut_ptr();
        let len = self.len();

        // SAFETY: type invariant (the first `len`-th bytes are initialized)
        unsafe { core::slice::from_raw_parts_mut(data.cast(), len) }
    }

    /// Returns `true` iff this representation is valid.
    #[inline]
    pub const fn is_valid(&self) -> bool {
        (self.shifted_len & 1) != 0
    }

    /// Returns the actual `const`-parameter for inline capacity of this type.
    #[inline]
    pub const fn capacity() -> usize {
        INLINE_CAPACITY
    }

    /// Pushes a short slice into this inline string.
    ///
    /// # Safety
    ///
    /// Does not check if the size with `addition` stays inside minimal capacity.
    #[inline]
    pub unsafe fn push_slice_unchecked(&mut self, addition: &[u8]) {
        let len = self.len();
        let add_len = addition.len();
        let new_len = len + add_len;

        debug_assert!(new_len <= INLINE_CAPACITY);

        unsafe {
            copy_nonoverlapping(
                addition.as_ptr().cast(),
                self.data.as_mut_ptr().add(len),
                add_len,
            );
        }
        #[allow(clippy::cast_possible_truncation)]
        {
            self.shifted_len = ((new_len << 1) | 1) as u8;
        }
    }
}
