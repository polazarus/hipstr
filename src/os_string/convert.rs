//! Conversion trait implementations for `HipOsStr`.

use alloc::borrow::Cow;
use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;
use core::borrow::Borrow;
use std::ffi::{OsStr, OsString};

use super::HipOsStr;
use crate::backend::Backend;
use crate::bytes::HipByt;
use crate::string::HipStr;

// AsRef

impl<B> AsRef<OsStr> for HipOsStr<'_, B>
where
    B: Backend,
{
    #[inline]
    fn as_ref(&self) -> &OsStr {
        self.as_os_str()
    }
}

impl<B> AsRef<std::path::Path> for HipOsStr<'_, B>
where
    B: Backend,
{
    fn as_ref(&self) -> &std::path::Path {
        self.as_os_str().as_ref()
    }
}

// Borrow

impl<B> Borrow<OsStr> for HipOsStr<'_, B>
where
    B: Backend,
{
    #[inline]
    fn borrow(&self) -> &OsStr {
        self.as_os_str()
    }
}

// Infallible conversions
// From

impl<B> From<&str> for HipOsStr<'_, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: &str) -> Self {
        Self(HipByt::from(value.as_bytes()))
    }
}

impl<B> From<Box<str>> for HipOsStr<'_, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: Box<str>) -> Self {
        Self(HipByt::from(value.into_boxed_bytes().into_vec()))
    }
}

impl<B> From<String> for HipOsStr<'_, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: String) -> Self {
        Self(HipByt::from(value.into_bytes()))
    }
}

impl<B> From<&OsStr> for HipOsStr<'_, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: &OsStr) -> Self {
        Self(HipByt::from(value.as_encoded_bytes()))
    }
}

impl<B> From<OsString> for HipOsStr<'_, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: OsString) -> Self {
        Self(HipByt::from(value.into_encoded_bytes()))
    }
}

impl<'borrow, B> From<Cow<'borrow, str>> for HipOsStr<'borrow, B>
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

impl<'borrow, B> From<HipStr<'borrow, B>> for HipOsStr<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: HipStr<'borrow, B>) -> Self {
        Self(value.into_bytes())
    }
}

impl<'borrow, B> From<&HipStr<'borrow, B>> for HipOsStr<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: &HipStr<'borrow, B>) -> Self {
        Self::from(value.clone())
    }
}

// Into

impl<B> From<HipOsStr<'_, B>> for OsString
where
    B: Backend,
{
    #[inline]
    fn from(value: HipOsStr<B>) -> Self {
        value
            .into_os_string()
            .unwrap_or_else(|value| value.as_os_str().into())
    }
}

impl<'borrow, B> From<HipOsStr<'borrow, B>> for HipByt<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: HipOsStr<'borrow, B>) -> Self {
        value.0
    }
}

impl<B> From<HipOsStr<'_, B>> for Vec<u8>
where
    B: Backend,
{
    #[inline]
    fn from(value: HipOsStr<B>) -> Self {
        value.0.into()
    }
}

impl<'borrow, B> From<HipOsStr<'borrow, B>> for Cow<'borrow, OsStr>
where
    B: Backend,
{
    #[inline]
    fn from(value: HipOsStr<'borrow, B>) -> Self {
        value
            .into_borrowed()
            .map_or_else(|value| Cow::Owned(value.into()), Cow::Borrowed)
    }
}

// Fallible conversions

//?

#[cfg(test)]
mod tests {
    use alloc::borrow::Cow;
    use alloc::boxed::Box;
    use alloc::string::String;
    use alloc::vec::Vec;
    use core::borrow::Borrow;
    use core::ptr;
    use std::ffi::{OsStr, OsString};
    use std::path::Path;

    use crate::{HipByt, HipOsStr, HipStr};

    #[test]
    fn test_as_ref() {
        let a = HipOsStr::from("abc");

        let p: &Path = a.as_ref();
        assert!(ptr::eq(Path::new(a.as_os_str()), p));

        let o: &OsStr = a.as_ref();
        assert!(ptr::eq(a.as_os_str(), o));
    }

    #[test]
    fn test_borrow() {
        let a = HipOsStr::from("abc");

        let p: &OsStr = a.borrow();
        assert!(ptr::eq(a.as_os_str(), p));
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
        let h_string = HipStr::from(slice);
        let h_string_ptr = h_string.as_ptr();

        let fs = HipOsStr::from(slice);
        assert_eq!(fs.as_os_str(), slice);

        let fv = HipOsStr::from(string);
        assert_eq!(fv.as_os_str(), slice);
        assert!(ptr::eq(fv.as_ptr(), ptr_string));

        let fv = HipOsStr::from(b);
        assert_eq!(fv.as_os_str(), slice);
        assert!(ptr::eq(fv.as_ptr(), ptr_b));

        let fc1 = HipOsStr::from(c1);
        assert_eq!(fc1.as_os_str(), slice);

        let fc2 = HipOsStr::from(c2);
        assert_eq!(fc2.as_os_str(), slice);
        assert!(ptr::eq(fc2.as_ptr(), ptr_c2));

        let fhs = HipOsStr::from(&h_string);
        assert_eq!(fhs.as_os_str(), slice);
        assert!(ptr::eq(fhs.as_ptr(), h_string_ptr));

        let fhs = HipOsStr::from(h_string);
        assert_eq!(fhs.as_os_str(), slice);
        assert!(ptr::eq(fhs.as_ptr(), h_string_ptr));
    }

    #[test]
    fn test_into_os_string() {
        let v = "a".repeat(42); // string's length > inline capacity
        let p = v.as_ptr();
        let a = HipOsStr::from(v);
        let v: OsString = a.into();
        assert_eq!(v.as_encoded_bytes().as_ptr(), p);

        let a = HipOsStr::from("abc");
        let v: OsString = a.into();
        assert_eq!(v, "abc");

        let a = HipOsStr::borrowed("abc");
        let v: OsString = a.into();
        assert_eq!(v, "abc");
    }

    #[test]
    fn test_into_cow() {
        let h = HipOsStr::from_static("abc");
        let c: Cow<'static, OsStr> = h.into();
        assert_eq!(c, Cow::Borrowed("abc"));

        let h = HipOsStr::from("abc");
        let c: Cow<'static, OsStr> = h.into();
        assert_eq!(c, Cow::<'static, OsStr>::Owned("abc".into()));
    }

    #[test]
    fn test_into_hipbyt() {
        let v = "a".repeat(42); // string's length > inline capacity
        let p = v.as_ptr();
        let hs = HipOsStr::from(v);
        let hb: HipByt = hs.into();
        assert_eq!(hb, b"a".repeat(42));
        assert_eq!(hb.as_ptr(), p);

        let a = HipOsStr::from("abc");
        let v: HipByt = a.into();
        assert_eq!(v, b"abc");

        let a = HipOsStr::borrowed("abc");
        let v: HipByt = a.into();
        assert_eq!(v, b"abc");
    }

    #[test]
    fn test_into_vec() {
        let v = "a".repeat(42); // string's length > inline capacity
        let p = v.as_ptr();
        let hs = HipOsStr::from(v);
        let v: Vec<u8> = hs.into();
        assert_eq!(v, b"a".repeat(42));
        assert_eq!(v.as_ptr(), p);
    }

    // #[test]
    // fn test_try_from() {
    //     let slice: &[u8] = b"abcdefghijklmnopqrstuvwxyz";

    //     let hb = HipByt::borrowed(slice);
    //     let hs: HipOsStr = hb.try_into().unwrap();
    //     assert_eq!(hs, "abcdefghijklmnopqrstuvwxyz");
    //     assert!(hs.is_borrowed());

    //     let hb = HipByt::from(slice);
    //     let hs: HipOsStr = hb.try_into().unwrap();
    //     assert_eq!(hs, "abcdefghijklmnopqrstuvwxyz");

    //     let hb = HipByt::borrowed(slice);
    //     let hs: HipOsStr = (&hb).try_into().unwrap();
    //     assert_eq!(hs, "abcdefghijklmnopqrstuvwxyz");

    //     let hs: HipOsStr = slice.try_into().unwrap();
    //     assert_eq!(hs, "abcdefghijklmnopqrstuvwxyz");

    //     let v = b"a".repeat(42);
    //     let p = v.as_ptr();
    //     let hs: HipOsStr = v.try_into().unwrap();
    //     assert_eq!(hs, "a".repeat(42));
    //     assert_eq!(hs.as_ptr(), p);
    // }

    // #[test]
    // fn test_try_from_err() {
    //     let slice: &[u8] = b"abc\x80";
    //     let hb = HipByt::borrowed(slice);
    //     assert!(HipOsStr::try_from(slice).is_err());
    //     assert!(HipOsStr::try_from(slice.to_vec()).is_err());
    //     assert!(HipOsStr::try_from(&hb).is_err());
    //     assert!(HipOsStr::try_from(hb).is_err());
    // }
}
