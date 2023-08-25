/// Static string.
///
/// Warning!
/// For big-endian platform, the reserved word is **after** the data.
/// For little-endian platform, the reserved word is **before** the data.
#[derive(Clone, Copy)]
#[repr(C)]
pub struct Borrowed<'borrow> {
    #[cfg(target_endian = "little")]
    reserved: usize,

    slice: &'borrow [u8],

    #[cfg(target_endian = "big")]
    reserved: usize,
}

impl<'borrow> Borrowed<'borrow> {
    /// Creates a new borrowed representation.
    #[inline]
    pub const fn new(slice: &'borrow [u8]) -> Self {
        Self { slice, reserved: 0 }
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

    /// Return `true` iff this representation is valid.
    #[inline]
    pub const fn is_valid(&self) -> bool {
        self.reserved == 0
    }
}
