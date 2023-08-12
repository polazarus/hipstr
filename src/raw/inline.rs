use std::mem::MaybeUninit;

//// Inline string.
///
/// Warning!
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
        let data = unsafe { MaybeUninit::uninit().assume_init() };
        #[allow(clippy::inconsistent_struct_constructor)]
        Self {
            data,
            shifted_len: 1,
        }
    }

    /// Creates a new `Inline` string by copying a byte slice.
    #[inline]
    pub fn new(sl: &[u8]) -> Self {
        let len = sl.len();
        assert!(len <= INLINE_CAPACITY);

        let mut data: [MaybeUninit<u8>; INLINE_CAPACITY];
        unsafe {
            data = MaybeUninit::uninit().assume_init();
            std::ptr::copy_nonoverlapping(sl.as_ptr(), data.as_mut_ptr().cast(), len);
        }

        #[allow(clippy::cast_possible_truncation)]
        let shifted_len = ((len << 1) | 1) as u8;

        #[allow(clippy::inconsistent_struct_constructor)]
        Self { data, shifted_len }
    }

    /// Returns the length of this inline string.
    #[inline]
    pub const fn len(&self) -> usize {
        debug_assert!(self.is_valid(), "Inline::len on an invalid representation");

        (self.shifted_len >> 1) as usize
    }

    /// Returns an immutable view of this `Inline` string.
    #[inline]
    pub const fn as_slice(&self) -> &[u8] {
        debug_assert!(
            self.is_valid(),
            "Inline::as_slice on an invalid representation"
        );

        // waiting for const_slice_index
        let data = self.data.as_ptr();
        let len = self.len();

        // SAFETY: type invariant
        unsafe { std::slice::from_raw_parts(data.cast(), len) }
    }

    /// Returns a mutable view of this `Inline` string.
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        debug_assert!(
            self.is_valid(),
            "Inline::as_mut_slice on an invalid representation"
        );

        let len = self.len();
        unsafe { std::slice::from_raw_parts_mut(self.data.as_mut_ptr().cast(), len) }
    }

    /// Return `true` iff this representation is valid.
    #[inline]
    pub const fn is_valid(&self) -> bool {
        (self.shifted_len & 1) != 0
    }

    #[inline]
    pub const fn capacity() -> usize {
        INLINE_CAPACITY
    }
}
