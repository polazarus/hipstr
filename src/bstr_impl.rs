//! `bstr` interoperability, for every size.
//!
//! Strings implement `AsRef<BStr>` and comparisons with `BStr`/`BString`, but
//! not `Borrow<BStr>`: `str` and `BStr` hash differently, which would break
//! `Borrow`'s contract (lookups in hash maps would miss). Byte strings hash
//! like `BStr` and implement `Borrow<BStr>`.

use alloc::borrow::Cow;
use alloc::vec::Vec;
use core::borrow::Borrow;
use core::cmp::Ordering;

use ::bstr::{BStr, BString, ByteSlice, ByteVec};

use super::enc::{Bytes, Utf8};
use super::hip::Hip;
use super::repr::Repr;

/// Comparisons with `BStr`/`&BStr`/`BString` in both directions, on bytes.
macro_rules! bstr_cmp {
    ($enc:ty: $($other:ty),*) => {$(
        impl<'a, R: Repr<'a, u8>> PartialEq<$other> for Hip<$enc, R> {
            #[inline]
            fn eq(&self, other: &$other) -> bool {
                self.bytes() == <$other as AsRef<[u8]>>::as_ref(other)
            }
        }

        impl<'a, R: Repr<'a, u8>> PartialEq<Hip<$enc, R>> for $other {
            #[inline]
            fn eq(&self, other: &Hip<$enc, R>) -> bool {
                <$other as AsRef<[u8]>>::as_ref(self) == other.bytes()
            }
        }

        impl<'a, R: Repr<'a, u8>> PartialOrd<$other> for Hip<$enc, R> {
            #[inline]
            fn partial_cmp(&self, other: &$other) -> Option<Ordering> {
                self.bytes().partial_cmp(<$other as AsRef<[u8]>>::as_ref(other))
            }
        }

        impl<'a, R: Repr<'a, u8>> PartialOrd<Hip<$enc, R>> for $other {
            #[inline]
            fn partial_cmp(&self, other: &Hip<$enc, R>) -> Option<Ordering> {
                <$other as AsRef<[u8]>>::as_ref(self).partial_cmp(other.bytes())
            }
        }
    )*};
}

bstr_cmp!(Bytes: BStr, &BStr, BString);
bstr_cmp!(Utf8: BStr, &BStr, BString);

impl<'a, R: Repr<'a, u8>> AsRef<BStr> for Hip<Bytes, R> {
    #[inline]
    fn as_ref(&self) -> &BStr {
        self.bytes().as_bstr()
    }
}

impl<'a, R: Repr<'a, u8>> AsRef<BStr> for Hip<Utf8, R> {
    #[inline]
    fn as_ref(&self) -> &BStr {
        self.bytes().as_bstr()
    }
}

impl<'a, R: Repr<'a, u8>> Borrow<BStr> for Hip<Bytes, R> {
    #[inline]
    fn borrow(&self) -> &BStr {
        self.bytes().as_bstr()
    }
}

impl<'a, R: Repr<'a, u8>> From<&'a BStr> for Hip<Bytes, R> {
    /// Borrows when the representation supports it, copies otherwise.
    #[inline]
    fn from(value: &'a BStr) -> Self {
        Self::from_inner_borrowed(value.as_bytes())
    }
}

impl<'a, R: Repr<'a, u8>> From<BString> for Hip<Bytes, R> {
    /// Adopts the buffer when it does not fit inline (no copy).
    #[inline]
    fn from(value: BString) -> Self {
        Self::from_owned(value.into())
    }
}

impl<'a, R: Repr<'a, u8>> From<Cow<'a, BStr>> for Hip<Bytes, R> {
    #[inline]
    fn from(value: Cow<'a, BStr>) -> Self {
        match value {
            Cow::Borrowed(b) => Self::from(b),
            Cow::Owned(o) => Self::from(o),
        }
    }
}

impl<'a, R: Repr<'a, u8>> From<Hip<Bytes, R>> for BString {
    /// O(1) when the value uniquely owns an adopted buffer.
    #[inline]
    fn from(value: Hip<Bytes, R>) -> Self {
        Self::from(value.into_owned_std())
    }
}

impl<'a, R: Repr<'a, u8>> TryFrom<&'a BStr> for Hip<Utf8, R> {
    type Error = ::bstr::Utf8Error;

    /// Borrows when the representation supports it, copies otherwise.
    #[inline]
    fn try_from(value: &'a BStr) -> Result<Self, Self::Error> {
        value.to_str().map(Self::from_inner_borrowed)
    }
}

impl<'a, R: Repr<'a, u8>> TryFrom<BString> for Hip<Utf8, R> {
    type Error = ::bstr::FromUtf8Error;

    /// Adopts the buffer when it does not fit inline (no copy).
    #[inline]
    fn try_from(value: BString) -> Result<Self, Self::Error> {
        Vec::<u8>::from(value).into_string().map(Self::from_owned)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{HipStr, SmallByt, TinyStr};

    const LONG: &str = "a string that is definitely longer than any inline capacity";

    #[test]
    fn conversions() {
        let b = SmallByt::from(LONG.as_bytes().as_bstr());
        assert!(b.is_borrowed());
        assert_eq!(b, LONG.as_bytes().as_bstr());
        assert_eq!(BString::from(b.clone()), LONG.as_bytes().as_bstr());
        let s = TinyStr::try_from(BString::from(LONG)).unwrap();
        assert_eq!(s, BString::from(LONG));
        let s = HipStr::try_from(LONG.as_bytes().as_bstr()).unwrap();
        assert!(s.is_borrowed());
        assert!(HipStr::try_from(b"\xff".as_bstr()).is_err());
        let r: &BStr = s.as_ref();
        assert_eq!(r, LONG);
    }

    #[test]
    #[cfg(feature = "std")]
    fn borrow_bstr_hash_consistency() {
        let mut set = std::collections::HashSet::new();
        set.insert(crate::HipByt::from(LONG.as_bytes()));
        assert!(set.contains(LONG.as_bytes().as_bstr()));
    }
}
