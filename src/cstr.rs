//! C strings: [`HipCStr`], [`SmallCStr`], [`TinyCStr`].
//!
//! Values are stored with their NUL terminator, so they dereference to
//! [`CStr`] without copying. Lengths and capacities exclude the terminator
//! (like [`CStr::count_bytes`]): an empty C string has length 0 and occupies
//! one byte, which also counts against the inline capacity.
//!
//! # Examples
//!
//! ```
//! use hipstr::HipCStr;
//!
//! const HELLO: HipCStr = HipCStr::from_static(c"Hello");
//! assert_eq!(HELLO.len(), 5);
//! assert_eq!(HELLO.as_bytes_with_nul(), b"Hello\0");
//!
//! let owned = HipCStr::try_from("world").unwrap();
//! assert_eq!(owned, c"world");
//! assert!(HipCStr::try_from("nul\0inside").is_err());
//! ```

use alloc::borrow::Cow;
use alloc::boxed::Box;
use alloc::ffi::{CString, NulError};
use alloc::string::String;
use alloc::vec::Vec;
use core::ffi::{CStr, FromBytesWithNulError};

use super::enc::{self, Bytes, Utf8};
use super::family::{impl_borrowed_ctors, impl_cmp, impl_std_glue};
use super::hip::Hip;
use super::repr::Repr;
pub use crate::hip::RefMut;

super::generic_aliases!(enc::CStr, HipCStr, SmallCStr, TinyCStr, "C string");

impl_std_glue!(enc::CStr, CStr, CString);
impl_borrowed_ctors!(enc::CStr, CStr, |value| value.to_bytes_with_nul());
super::hip::impl_const_typed_accessors!(
    enc::CStr,
    CStr,
    |b| CStr::from_bytes_with_nul_unchecked(b),
    |v| v.to_bytes_with_nul()
);

impl_cmp!(enc::CStr as CStr;
    [] CStr, [] &CStr, [] CString, [] &CString, [] Box<CStr>, [] &Box<CStr>,
    [] Cow<'_, CStr>, [] &Cow<'_, CStr>,
);

/// `const` C string accessors, per representation.
macro_rules! impl_const_cstr {
    ($([$($lt:lifetime)?] $repr:ty),* $(,)?) => {$(
        impl<$($lt,)? B: super::backend::Backend> Hip<enc::CStr, $repr> {
            /// The C string slice.
            #[inline]
            #[must_use]
            pub const fn as_c_str(&self) -> &CStr {
                self.as_typed()
            }

            /// The bytes, without the NUL terminator (see [`CStr::to_bytes`]).
            #[inline]
            #[must_use]
            pub const fn as_bytes(&self) -> &[u8] {
                self.as_typed().to_bytes()
            }

            /// The bytes, with the NUL terminator (see [`CStr::to_bytes_with_nul`]).
            #[inline]
            #[must_use]
            pub const fn as_bytes_with_nul(&self) -> &[u8] {
                self.repr().as_slice()
            }
        }
    )*};
}

impl_const_cstr!(
    ['a] super::repr::Wide<'a, B>,
    ['a] super::repr::Small<'a, B>,
    [] super::repr::Tiny<B>,
);

impl<'a, R: Repr<'a>> Hip<enc::CStr, R> {
    /// Converts into a `CString`, in O(1) when the value uniquely owns an
    /// adopted buffer, by copying otherwise.
    #[inline]
    #[must_use]
    pub fn into_c_string(self) -> CString {
        self.into_owned_std()
    }

    /// Takes a vector without interior NUL and appends the terminator (see
    /// `CString::from_vec_unchecked`).
    ///
    /// # Safety
    ///
    /// `v` must not contain any NUL byte.
    #[inline]
    #[must_use]
    pub unsafe fn from_vec_unchecked(v: Vec<u8>) -> Self {
        // SAFETY: precondition
        Self::from_owned(unsafe { CString::from_vec_unchecked(v) })
    }

    /// Takes a vector ending with its only NUL, reusing its buffer (see
    /// `CString::from_vec_with_nul`).
    ///
    /// # Errors
    ///
    /// Returns an error if the vector has an interior NUL or does not end
    /// with NUL.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipCStr;
    /// let c = HipCStr::from_vec_with_nul(b"abc\0".to_vec()).unwrap();
    /// assert_eq!(c, c"abc");
    /// assert!(HipCStr::from_vec_with_nul(b"a\0bc\0".to_vec()).is_err());
    /// ```
    #[inline]
    pub fn from_vec_with_nul(v: Vec<u8>) -> Result<Self, alloc::ffi::FromVecWithNulError> {
        CString::from_vec_with_nul(v).map(Self::from_owned)
    }

    /// Takes a vector ending with its only NUL (see
    /// `CString::from_vec_with_nul_unchecked`).
    ///
    /// # Safety
    ///
    /// `v` must end with a NUL byte and contain no other.
    #[inline]
    #[must_use]
    pub unsafe fn from_vec_with_nul_unchecked(v: Vec<u8>) -> Self {
        // SAFETY: precondition
        Self::from_owned(unsafe { CString::from_vec_with_nul_unchecked(v) })
    }

    /// Converts into a `String` if valid UTF-8 (see `CString::into_string`).
    ///
    /// # Errors
    ///
    /// Returns std's error, which gives the C string back, if the bytes are
    /// not valid UTF-8.
    #[inline]
    pub fn into_string(self) -> Result<String, alloc::ffi::IntoStringError> {
        self.into_c_string().into_string()
    }

    /// Converts into a boxed C string.
    #[inline]
    #[must_use]
    pub fn into_boxed_c_str(self) -> Box<CStr> {
        self.into_c_string().into_boxed_c_str()
    }

    /// Converts into bytes with the NUL terminator, keeping the
    /// representation (no copy).
    #[inline]
    #[must_use]
    pub const fn into_bytes_with_nul(self) -> Hip<Bytes, R> {
        // SAFETY: no invariant on bytes
        unsafe { Hip::from_repr(self.into_repr()) }
    }

    /// Converts into bytes without the NUL terminator.
    ///
    /// O(1) for the 3- and 2-word types (the view is shortened); the 1-word
    /// types copy when shared.
    #[must_use]
    pub fn into_bytes(self) -> Hip<Bytes, R> {
        let mut bytes = self.into_bytes_with_nul();
        bytes.pop();
        bytes
    }

    /// Converts bytes ending with the only NUL into a C string, keeping the
    /// representation (no copy).
    ///
    /// # Errors
    ///
    /// Returns an error if the bytes contain an interior NUL or do not end
    /// with NUL.
    pub fn from_bytes_with_nul(bytes: Hip<Bytes, R>) -> Result<Self, FromBytesWithNulError> {
        CStr::from_bytes_with_nul(bytes.as_inner())?;
        // SAFETY: checked
        Ok(unsafe { Self::from_repr(bytes.into_repr()) })
    }

    /// Converts into a UTF-8 string without the terminator, sharing the
    /// storage when possible (see [`into_bytes`](Self::into_bytes)).
    ///
    /// # Errors
    ///
    /// Returns `Err(self)` if the C string is not valid UTF-8.
    pub fn into_str(self) -> Result<Hip<Utf8, R>, Self> {
        if self.as_inner().to_str().is_ok() {
            // SAFETY: checked UTF-8, terminator removed
            Ok(unsafe { Hip::from_repr(self.into_bytes().into_repr()) })
        } else {
            Err(self)
        }
    }
}

impl<'a, R: Repr<'a>> TryFrom<Vec<u8>> for Hip<enc::CStr, R> {
    type Error = NulError;

    /// Appends the NUL terminator, like `CString::new` (reusing the buffer
    /// when it does not fit inline).
    #[inline]
    fn try_from(bytes: Vec<u8>) -> Result<Self, Self::Error> {
        CString::new(bytes).map(Self::from_owned)
    }
}

impl<'a, R: Repr<'a>> TryFrom<&[u8]> for Hip<enc::CStr, R> {
    type Error = NulError;

    /// Appends the NUL terminator, like `CString::new`.
    fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
        if bytes.contains(&0) {
            // `NulError` has no public constructor: let `CString` report it
            return Err(CString::new(bytes).unwrap_err());
        }
        let mut repr = R::new();
        repr.reserve(bytes.len() + 1);
        repr.extend_from_slice(bytes);
        repr.push(0);
        // SAFETY: NUL-free bytes followed by the only NUL
        Ok(unsafe { Self::from_repr(repr) })
    }
}

impl<'a, R: Repr<'a>> TryFrom<&str> for Hip<enc::CStr, R> {
    type Error = NulError;

    /// Appends the NUL terminator, like `CString::new`.
    #[inline]
    fn try_from(s: &str) -> Result<Self, Self::Error> {
        Self::try_from(s.as_bytes())
    }
}

impl<'a, R: Repr<'a>> TryFrom<String> for Hip<enc::CStr, R> {
    type Error = NulError;

    /// Appends the NUL terminator, like `CString::new`.
    #[inline]
    fn try_from(s: String) -> Result<Self, Self::Error> {
        Self::try_from(s.into_bytes())
    }
}

impl<'a, R: Repr<'a>> From<Hip<enc::CStr, R>> for Hip<Bytes, R> {
    /// The bytes without the NUL terminator (see [`Hip::into_bytes`]).
    #[inline]
    fn from(value: Hip<enc::CStr, R>) -> Self {
        value.into_bytes()
    }
}

impl<'a, R: Repr<'a>> From<Hip<enc::CStr, R>> for Vec<u8> {
    /// The bytes without the NUL terminator, like `CString::into_bytes`.
    #[inline]
    fn from(value: Hip<enc::CStr, R>) -> Self {
        value.into_c_string().into_bytes()
    }
}

#[cfg(test)]
mod tests {
    use alloc::ffi::CString;
    use alloc::vec;

    use crate::{HipCStr, SmallCStr, TinyCStr};

    const LONG: &core::ffi::CStr = c"a C string that is definitely longer than any inline capacity";

    #[test]
    fn empty() {
        for e in [
            HipCStr::new(),
            HipCStr::default(),
            HipCStr::with_capacity(100),
        ] {
            assert!(e.is_empty());
            assert_eq!(e.len(), 0);
            assert_eq!(e.as_bytes_with_nul(), b"\0");
            assert_eq!(e, c"");
        }
        let mut s = TinyCStr::from(c"ab");
        s.clear();
        assert_eq!(s, c"");
        assert_eq!(TinyCStr::inline_capacity(), size_of::<usize>() - 2);
    }

    #[test]
    fn construct_and_read() {
        for c in [c"", c"abc", LONG] {
            let h = SmallCStr::from(c);
            assert_eq!(h.as_c_str(), c);
            assert_eq!(h.len(), c.count_bytes());
            assert_eq!(h.as_bytes(), c.to_bytes());
            assert_eq!(h, CString::from(c));
            assert_eq!(c, h);
            assert_eq!(h.to_str().unwrap(), c.to_str().unwrap());
        }
        assert!(TinyCStr::from(c"ab").is_inline()); // fits on 32-bit too
        assert!(TinyCStr::from(LONG).is_allocated());
    }

    #[test]
    fn c_string_round_trip_is_zero_copy() {
        let c = CString::from(LONG);
        let ptr = c.as_ptr();
        let h = HipCStr::from(c);
        assert_eq!(h.as_ptr().cast(), ptr);
        let back = h.into_c_string();
        assert_eq!(back.as_ptr(), ptr);
    }

    #[test]
    fn borrowing_and_consts() {
        const S: SmallCStr<'static> = SmallCStr::from_static(c"static");
        const I: TinyCStr = TinyCStr::inline(c"in");
        assert!(S.is_borrowed() && S.as_borrowed() == Some(c"static"));
        assert!(I.is_inline() && I.as_c_str() == c"in");
        let h = HipCStr::borrowed(LONG);
        assert_eq!(h.into_borrowed().unwrap().as_ptr(), LONG.as_ptr());
    }

    #[test]
    fn conversions() {
        assert_eq!(HipCStr::try_from("abc").unwrap(), c"abc");
        assert_eq!(HipCStr::try_from(vec![b'x'; 40]).unwrap().len(), 40);
        let err = TinyCStr::try_from(b"a\0b".as_slice()).unwrap_err();
        assert_eq!(err.nul_position(), 1);

        let bytes = crate::HipByt::from(LONG.to_bytes_with_nul());
        let ptr = bytes.as_ptr();
        let c = HipCStr::from_bytes_with_nul(bytes).unwrap();
        assert_eq!(c.as_ptr(), ptr, "no copy");
        assert!(HipCStr::from_bytes_with_nul(crate::HipByt::from(b"no nul")).is_err());

        let b = c.clone().into_bytes();
        assert_eq!(b, LONG.to_bytes());
        assert_eq!(b.as_ptr(), ptr, "the view shrinks, no copy");
        let s = c.into_str().unwrap();
        assert_eq!(s, LONG.to_str().unwrap());
    }

    #[test]
    #[cfg(feature = "std")]
    fn hash_and_borrow_consistency() {
        let mut set = std::collections::HashSet::new();
        set.insert(crate::LocalTinyCStr::from(LONG));
        assert!(set.contains(LONG));
    }
}
