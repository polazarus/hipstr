//! Conversion trait implementations for `HipStr`.

use std::borrow::Cow;

use super::HipStr;
use crate::bytes::HipByt;
use crate::Backend;

impl<'borrow, B> AsRef<str> for HipStr<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

// Infallible conversions

impl<'borrow, B> From<&str> for HipStr<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: &str) -> Self {
        Self(HipByt::from(value.as_bytes()))
    }
}

impl<'borrow, B> From<Box<str>> for HipStr<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: Box<str>) -> Self {
        Self(HipByt::from(value.into_boxed_bytes().into_vec()))
    }
}

impl<'borrow, B> From<String> for HipStr<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: String) -> Self {
        Self(HipByt::from(value.into_bytes()))
    }
}

impl<'borrow, B> From<Cow<'borrow, str>> for HipStr<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: Cow<'borrow, str>) -> Self {
        match value {
            Cow::Borrowed(borrow) => Self::borrowed(borrow),
            Cow::Owned(owned) => Self::from(owned),
        }
    }
}

impl<'borrow, B> From<HipStr<'borrow, B>> for String
where
    B: Backend,
{
    #[inline]
    fn from(value: HipStr<B>) -> Self {
        value
            .into_string()
            .unwrap_or_else(|value| value.as_str().into())
    }
}

impl<'borrow, B> From<HipStr<'borrow, B>> for HipByt<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: HipStr<'borrow, B>) -> Self {
        value.0
    }
}

impl<'borrow, B> From<HipStr<'borrow, B>> for Vec<u8>
where
    B: Backend,
{
    #[inline]
    fn from(value: HipStr<B>) -> Self {
        value.0.into()
    }
}

// Fallible conversions

impl<'borrow, B> TryFrom<HipByt<'borrow, B>> for HipStr<'borrow, B>
where
    B: Backend,
{
    type Error = super::FromUtf8Error<'borrow, B>;

    #[inline]
    fn try_from(value: HipByt<'borrow, B>) -> Result<Self, Self::Error> {
        Self::from_utf8(value)
    }
}

impl<'a, 'borrow, B> TryFrom<&'a HipByt<'borrow, B>> for HipStr<'borrow, B>
where
    B: Backend,
{
    type Error = super::FromUtf8Error<'borrow, B>;

    #[inline]
    fn try_from(value: &'a HipByt<'borrow, B>) -> Result<Self, Self::Error> {
        Self::from_utf8(value.clone())
    }
}

impl<'a, 'borrow, B> TryFrom<&'a [u8]> for HipStr<'borrow, B>
where
    B: Backend,
{
    type Error = std::str::Utf8Error;

    #[inline]
    fn try_from(value: &'a [u8]) -> Result<Self, Self::Error> {
        Ok(Self::from(std::str::from_utf8(value)?))
    }
}

impl<'borrow, B> TryFrom<Vec<u8>> for HipStr<'borrow, B>
where
    B: Backend,
{
    type Error = std::string::FromUtf8Error;

    #[inline]
    fn try_from(value: Vec<u8>) -> Result<Self, Self::Error> {
        let s = String::from_utf8(value)?;
        Ok(Self::from(s))
    }
}

#[cfg(test)]
mod tests {
    use std::borrow::Cow;

    use crate::{HipByt, HipStr};

    #[test]
    fn test_as_ref() {
        let a = HipStr::from("abc");
        assert!(std::ptr::eq(a.as_str(), a.as_ref()));
    }

    #[test]
    fn test_from() {
        let slice = "abcdefghijklmnopqrstuvwxyz";
        let string = String::from(slice);
        let ptr_string = string.as_ptr();
        let b: Box<str> = slice.into();
        let ptr_b = b.as_ptr();
        let c1: Cow<str> = Cow::Borrowed(slice);
        let c2: Cow<str> = String::from(slice).into();
        let ptr_c2 = c2.as_ptr();

        let fs = HipStr::from(slice);
        assert_eq!(fs.as_str(), slice);

        let fv = HipStr::from(string);
        assert_eq!(fv.as_str(), slice);
        assert!(std::ptr::eq(fv.as_ptr(), ptr_string));

        let fv = HipStr::from(b);
        assert_eq!(fv.as_str(), slice);
        assert!(std::ptr::eq(fv.as_ptr(), ptr_b));

        let fc1 = HipStr::from(c1);
        assert_eq!(fc1.as_str(), slice);

        let fc2 = HipStr::from(c2);
        assert_eq!(fc2.as_str(), slice);
        assert!(std::ptr::eq(fc2.as_ptr(), ptr_c2));
    }

    #[test]
    fn test_into_string() {
        let v = "a".repeat(42); // string's length > inline capacity
        let p = v.as_ptr();
        let a = HipStr::from(v);
        let v: String = a.into();
        assert_eq!(v.as_ptr(), p);

        let a = HipStr::from("abc");
        let v: String = a.into();
        assert_eq!(v.as_str(), "abc");

        let a = HipStr::borrowed("abc");
        let v: String = a.into();
        assert_eq!(v.as_str(), "abc");
    }

    #[test]
    fn test_into_hipbyt() {
        let v = "a".repeat(42); // string's length > inline capacity
        let p = v.as_ptr();
        let hs = HipStr::from(v);
        let hb: HipByt = hs.into();
        assert_eq!(hb, b"a".repeat(42));
        assert_eq!(hb.as_ptr(), p);

        let a = HipStr::from("abc");
        let v: HipByt = a.into();
        assert_eq!(v, b"abc");

        let a = HipStr::borrowed("abc");
        let v: HipByt = a.into();
        assert_eq!(v, b"abc");
    }

    #[test]
    fn test_into_vec() {
        let v = "a".repeat(42); // string's length > inline capacity
        let p = v.as_ptr();
        let hs = HipStr::from(v);
        let v: Vec<u8> = hs.into();
        assert_eq!(v, b"a".repeat(42));
        assert_eq!(v.as_ptr(), p);
    }

    #[test]
    fn test_try_from() {
        let slice: &[u8] = b"abcdefghijklmnopqrstuvwxyz";

        let hb = HipByt::borrowed(slice);
        let hs: HipStr = hb.try_into().unwrap();
        assert_eq!(hs, "abcdefghijklmnopqrstuvwxyz");
        assert!(hs.is_borrowed());

        let hb = HipByt::from(slice);
        let hs: HipStr = hb.try_into().unwrap();
        assert_eq!(hs, "abcdefghijklmnopqrstuvwxyz");

        let hb = HipByt::borrowed(slice);
        let hs: HipStr = (&hb).try_into().unwrap();
        assert_eq!(hs, "abcdefghijklmnopqrstuvwxyz");

        let hs: HipStr = slice.try_into().unwrap();
        assert_eq!(hs, "abcdefghijklmnopqrstuvwxyz");

        let v = b"a".repeat(42);
        let p = v.as_ptr();
        let hs: HipStr = v.try_into().unwrap();
        assert_eq!(hs, "a".repeat(42));
        assert_eq!(hs.as_ptr(), p);
    }

    #[test]
    fn test_try_from_err() {
        let slice: &[u8] = b"abc\x80";
        let hb = HipByt::borrowed(slice);
        assert!(HipStr::try_from(slice).is_err());
        assert!(HipStr::try_from(slice.to_vec()).is_err());
        assert!(HipStr::try_from(&hb).is_err());
        assert!(HipStr::try_from(hb).is_err());
    }
}
