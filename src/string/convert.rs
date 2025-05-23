//! Conversion trait implementations for `HipStr`.

use alloc::borrow::Cow;
use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;
#[cfg(feature = "std")]
use std::net::ToSocketAddrs;

use super::HipStr;
use crate::backend::Backend;
use crate::bytes::HipByt;

impl<B> AsRef<str> for HipStr<'_, B>
where
    B: Backend,
{
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl<B> AsRef<[u8]> for HipStr<'_, B>
where
    B: Backend,
{
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

#[cfg(feature = "std")]
impl<B> AsRef<std::ffi::OsStr> for HipStr<'_, B>
where
    B: Backend,
{
    fn as_ref(&self) -> &std::ffi::OsStr {
        self.as_str().as_ref()
    }
}

#[cfg(feature = "std")]
impl<B> AsRef<std::path::Path> for HipStr<'_, B>
where
    B: Backend,
{
    fn as_ref(&self) -> &std::path::Path {
        self.as_str().as_ref()
    }
}

// Infallible conversions

impl<B> From<&str> for HipStr<'_, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: &str) -> Self {
        Self(HipByt::from(value.as_bytes()))
    }
}

impl<B> From<Box<str>> for HipStr<'_, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: Box<str>) -> Self {
        Self(HipByt::from(value.into_boxed_bytes().into_vec()))
    }
}

impl<B> From<String> for HipStr<'_, B>
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

impl<B> From<HipStr<'_, B>> for String
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

#[cfg(feature = "std")]
impl<B> From<HipStr<'_, B>> for std::ffi::OsString
where
    B: Backend,
{
    #[inline]
    fn from(value: HipStr<B>) -> Self {
        value
            .into_string()
            .unwrap_or_else(|value| value.as_str().into())
            .into()
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

impl<B> From<HipStr<'_, B>> for Vec<u8>
where
    B: Backend,
{
    #[inline]
    fn from(value: HipStr<B>) -> Self {
        value.0.into()
    }
}

impl<'borrow, B> From<HipStr<'borrow, B>> for Cow<'borrow, str>
where
    B: Backend,
{
    #[inline]
    fn from(value: HipStr<'borrow, B>) -> Self {
        value
            .into_borrowed()
            .map_or_else(|value| Cow::Owned(value.into()), Cow::Borrowed)
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

impl<'borrow, B> TryFrom<&HipByt<'borrow, B>> for HipStr<'borrow, B>
where
    B: Backend,
{
    type Error = super::FromUtf8Error<'borrow, B>;

    #[inline]
    fn try_from(value: &HipByt<'borrow, B>) -> Result<Self, Self::Error> {
        Self::from_utf8(value.clone())
    }
}

impl<B> TryFrom<&[u8]> for HipStr<'_, B>
where
    B: Backend,
{
    type Error = core::str::Utf8Error;

    #[inline]
    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        Ok(Self::from(core::str::from_utf8(value)?))
    }
}

impl<B> TryFrom<Vec<u8>> for HipStr<'_, B>
where
    B: Backend,
{
    type Error = alloc::string::FromUtf8Error;

    #[inline]
    fn try_from(value: Vec<u8>) -> Result<Self, Self::Error> {
        let s = String::from_utf8(value)?;
        Ok(Self::from(s))
    }
}

#[cfg(feature = "std")]
impl<B> ToSocketAddrs for HipStr<'_, B>
where
    B: Backend,
{
    type Iter = <str as ToSocketAddrs>::Iter;

    fn to_socket_addrs(&self) -> std::io::Result<Self::Iter> {
        self.as_str().to_socket_addrs()
    }
}

#[cfg(test)]
mod tests {
    use alloc::borrow::Cow;
    use alloc::boxed::Box;
    use alloc::string::String;
    use alloc::vec::Vec;
    use core::ptr;
    #[cfg(feature = "std")]
    use std::net::ToSocketAddrs;

    use crate::{HipByt, HipStr};

    #[test]
    fn test_as_ref() {
        let a = HipStr::from("abc");
        assert!(ptr::eq(a.as_str(), a.as_ref()));
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
        assert!(ptr::eq(fv.as_ptr(), ptr_string));

        let fv = HipStr::from(b);
        assert_eq!(fv.as_str(), slice);
        assert!(ptr::eq(fv.as_ptr(), ptr_b));

        let fc1 = HipStr::from(c1);
        assert_eq!(fc1.as_str(), slice);

        let fc2 = HipStr::from(c2);
        assert_eq!(fc2.as_str(), slice);
        assert!(ptr::eq(fc2.as_ptr(), ptr_c2));
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
    fn test_into_cow() {
        let h = HipStr::from_static("abc");
        let c: Cow<'static, str> = h.into();
        assert_eq!(c, Cow::Borrowed("abc"));

        let h = HipStr::from("abc");
        let c: Cow<'static, str> = h.into();
        assert_eq!(c, Cow::<'static, str>::Owned("abc".into()));
    }

    #[test]
    #[cfg(feature = "std")]
    fn into_os_string() {
        let h = HipStr::from("abc");
        let os_string: std::ffi::OsString = h.into();
        assert_eq!(os_string, "abc");
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

    #[test]
    fn as_ref_bytes() {
        let h = HipStr::from("abc");
        let b: &[u8] = h.as_ref();
        assert!(ptr::eq(h.as_bytes(), b));
    }

    #[cfg(feature = "std")]
    #[test]
    fn as_ref_os_str() {
        let h = HipStr::from("abc");
        let o: &std::ffi::OsStr = h.as_ref();
        assert_eq!(o, "abc");
        assert!(ptr::eq(h.as_str().as_ref(), o));
    }

    #[cfg(feature = "std")]
    #[test]
    fn as_ref_path() {
        let h = HipStr::from("abc");
        let p: &std::path::Path = h.as_ref();
        assert_eq!(p, std::path::Path::new("abc"));
        assert!(ptr::eq(h.as_str().as_ref(), p));
    }

    #[cfg(feature = "std")]
    #[test]
    fn to_sock_addrs() {
        let h = HipStr::from("0.0.0.0:80");
        let v: Vec<_> = h.to_socket_addrs().unwrap().collect();
        let v2: Vec<_> = "0.0.0.0:80".to_socket_addrs().unwrap().collect();
        assert_eq!(v, v2);
    }
}
