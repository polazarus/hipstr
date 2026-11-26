//! Encodings: what the bytes of a [`Hip`](super::hip::Hip) value mean.
//!
//! Every type of the crate stores bytes; an encoding marker states their
//! invariant (none, UTF-8, C string, OS string, path) and maps them to the
//! matching std types.

use alloc::string::String;
use alloc::vec::Vec;

mod seal {
    pub trait Sealed {}
}

/// Encoding of the bytes of a [`Hip`](super::hip::Hip) value.
///
/// # Safety
///
/// `from_bytes_unchecked` and `owned_from_bytes_unchecked` are only called on
/// bytes that come from `as_bytes`/`owned_into_bytes` of the same encoding,
/// possibly concatenated or cut at valid boundaries.
pub unsafe trait Encoding: seal::Sealed + 'static {
    /// Borrowed form, e.g. `str`.
    type Slice: ?Sized + 'static;

    /// Owned std form, e.g. `String`.
    type Owned;

    /// Bytes of the empty value (e.g. a lone NUL for C strings).
    const EMPTY: &'static [u8] = b"";

    /// Number of trailing terminator bytes stored with every value (the NUL of
    /// C strings), excluded from lengths and capacities.
    const TERMINATOR: usize = 0;

    fn as_bytes(slice: &Self::Slice) -> &[u8];

    /// # Safety
    ///
    /// The bytes must satisfy the encoding's invariant.
    unsafe fn from_bytes_unchecked(bytes: &[u8]) -> &Self::Slice;

    fn owned_into_bytes(owned: Self::Owned) -> Vec<u8>;

    /// # Safety
    ///
    /// The bytes must satisfy the encoding's invariant.
    unsafe fn owned_from_bytes_unchecked(bytes: Vec<u8>) -> Self::Owned;
}

/// Raw bytes, no invariant.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Bytes;

/// UTF-8 text.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Utf8;

/// NUL-terminated C string ([`core::ffi::CStr`]), stored with its terminator.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct CStr;

impl seal::Sealed for Bytes {}
impl seal::Sealed for Utf8 {}
impl seal::Sealed for CStr {}

// SAFETY: bytes end with the only NUL (precondition)
unsafe impl Encoding for CStr {
    type Slice = core::ffi::CStr;
    type Owned = alloc::ffi::CString;

    const EMPTY: &'static [u8] = b"\0";
    const TERMINATOR: usize = 1;

    #[inline]
    fn as_bytes(slice: &core::ffi::CStr) -> &[u8] {
        slice.to_bytes_with_nul()
    }

    #[inline]
    unsafe fn from_bytes_unchecked(bytes: &[u8]) -> &core::ffi::CStr {
        // SAFETY: precondition
        unsafe { core::ffi::CStr::from_bytes_with_nul_unchecked(bytes) }
    }

    #[inline]
    fn owned_into_bytes(owned: alloc::ffi::CString) -> Vec<u8> {
        owned.into_bytes_with_nul()
    }

    #[inline]
    unsafe fn owned_from_bytes_unchecked(bytes: Vec<u8>) -> alloc::ffi::CString {
        // SAFETY: precondition
        unsafe { alloc::ffi::CString::from_vec_with_nul_unchecked(bytes) }
    }
}

// SAFETY: no invariant
unsafe impl Encoding for Bytes {
    type Slice = [u8];
    type Owned = Vec<u8>;

    #[inline]
    fn as_bytes(slice: &[u8]) -> &[u8] {
        slice
    }

    #[inline]
    unsafe fn from_bytes_unchecked(bytes: &[u8]) -> &[u8] {
        bytes
    }

    #[inline]
    fn owned_into_bytes(owned: Vec<u8>) -> Vec<u8> {
        owned
    }

    #[inline]
    unsafe fn owned_from_bytes_unchecked(bytes: Vec<u8>) -> Vec<u8> {
        bytes
    }
}

// SAFETY: UTF-8 is preserved by the callers (precondition)
unsafe impl Encoding for Utf8 {
    type Slice = str;
    type Owned = String;

    #[inline]
    fn as_bytes(slice: &str) -> &[u8] {
        slice.as_bytes()
    }

    #[inline]
    unsafe fn from_bytes_unchecked(bytes: &[u8]) -> &str {
        // SAFETY: precondition
        unsafe { core::str::from_utf8_unchecked(bytes) }
    }

    #[inline]
    fn owned_into_bytes(owned: String) -> Vec<u8> {
        owned.into_bytes()
    }

    #[inline]
    unsafe fn owned_from_bytes_unchecked(bytes: Vec<u8>) -> String {
        // SAFETY: precondition
        unsafe { String::from_utf8_unchecked(bytes) }
    }
}

#[cfg(feature = "std")]
pub use os::{OsStr, Path};

#[cfg(feature = "std")]
mod os {
    use alloc::vec::Vec;
    use std::ffi::OsString;
    use std::path::PathBuf;

    use super::{Encoding, seal};

    /// Platform string ([`std::ffi::OsStr`]).
    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
    pub struct OsStr;

    /// Path ([`std::path::Path`]), an OS string with path semantics.
    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
    pub struct Path;

    impl seal::Sealed for OsStr {}
    impl seal::Sealed for Path {}

    // SAFETY: bytes only come from `as_encoded_bytes` (precondition)
    unsafe impl Encoding for OsStr {
        type Slice = std::ffi::OsStr;
        type Owned = OsString;

        #[inline]
        fn as_bytes(slice: &std::ffi::OsStr) -> &[u8] {
            slice.as_encoded_bytes()
        }

        #[inline]
        unsafe fn from_bytes_unchecked(bytes: &[u8]) -> &std::ffi::OsStr {
            // SAFETY: precondition
            unsafe { std::ffi::OsStr::from_encoded_bytes_unchecked(bytes) }
        }

        #[inline]
        fn owned_into_bytes(owned: OsString) -> Vec<u8> {
            owned.into_encoded_bytes()
        }

        #[inline]
        unsafe fn owned_from_bytes_unchecked(bytes: Vec<u8>) -> OsString {
            // SAFETY: precondition
            unsafe { OsString::from_encoded_bytes_unchecked(bytes) }
        }
    }

    // SAFETY: same as `OsStr`
    unsafe impl Encoding for Path {
        type Slice = std::path::Path;
        type Owned = PathBuf;

        #[inline]
        fn as_bytes(slice: &std::path::Path) -> &[u8] {
            slice.as_os_str().as_encoded_bytes()
        }

        #[inline]
        unsafe fn from_bytes_unchecked(bytes: &[u8]) -> &std::path::Path {
            // SAFETY: precondition
            std::path::Path::new(unsafe { std::ffi::OsStr::from_encoded_bytes_unchecked(bytes) })
        }

        #[inline]
        fn owned_into_bytes(owned: PathBuf) -> Vec<u8> {
            owned.into_os_string().into_encoded_bytes()
        }

        #[inline]
        unsafe fn owned_from_bytes_unchecked(bytes: Vec<u8>) -> PathBuf {
            // SAFETY: precondition
            PathBuf::from(unsafe { OsString::from_encoded_bytes_unchecked(bytes) })
        }
    }
}
