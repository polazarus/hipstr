//! Bstr support for strings.

use alloc::str;
use alloc::string::String;
use alloc::vec::Vec;
use core::borrow::Borrow;

use bstr::{BStr, BString};

use super::HipStr;
use crate::macros::{symmetric_eq, symmetric_ord};
use crate::Backend;

impl<B> Borrow<BStr> for HipStr<'_, B>
where
    B: Backend,
{
    #[inline]
    fn borrow(&self) -> &BStr {
        BStr::new(self.as_bytes())
    }
}

impl<B> AsRef<BStr> for HipStr<'_, B>
where
    B: Backend,
{
    #[inline]
    fn as_ref(&self) -> &BStr {
        BStr::new(self.as_bytes())
    }
}

#[inline]
fn bstr_eq(a: impl AsRef<BStr>, b: impl AsRef<str>) -> bool {
    a.as_ref() == b.as_ref()
}

symmetric_eq! {
    [B] [where B: Backend] (BStr, HipStr<'_, B>) = bstr_eq;
    [B] [where B: Backend] (&BStr, HipStr<'_, B>) = bstr_eq;
    [B] [where B: Backend] (BString, HipStr<'_, B>) = bstr_eq;
    [B] [where B: Backend] (&BString, HipStr<'_, B>) = bstr_eq;
}

#[cfg(feature = "bstr")]
#[inline]
fn bstr_cmp(a: impl AsRef<BStr>, b: impl AsRef<str>) -> Option<core::cmp::Ordering> {
    a.as_ref().partial_cmp(b.as_ref())
}

#[cfg(feature = "bstr")]
symmetric_ord! {
    [B] [where B: Backend] (BStr, HipStr<'_, B>) = bstr_cmp;
    [B] [where B: Backend] (&BStr, HipStr<'_, B>) = bstr_cmp;
    [B] [where B: Backend] (BString, HipStr<'_, B>) = bstr_cmp;
    [B] [where B: Backend] (&BString, HipStr<'_, B>) = bstr_cmp;
}

impl<'a, B> TryFrom<BString> for HipStr<'a, B>
where
    B: Backend,
{
    type Error = alloc::string::FromUtf8Error;

    fn try_from(value: BString) -> Result<Self, Self::Error> {
        let vec = Vec::from(value);
        let string = String::from_utf8(vec)?;
        Ok(Self::from(string))
    }
}

impl<'a, B> TryFrom<&'a BStr> for HipStr<'a, B>
where
    B: Backend,
{
    type Error = alloc::str::Utf8Error;

    fn try_from(value: &'a BStr) -> Result<Self, Self::Error> {
        let slice = <&'a [u8]>::from(value);
        let string = str::from_utf8(slice)?;
        Ok(Self::borrowed(string))
    }
}

#[cfg(test)]
mod tests {
    use core::borrow::Borrow;
    use core::cmp::Ordering;

    use bstr::{BStr, BString};

    use crate::HipStr;

    #[test]
    fn test_borrow() {
        let a = HipStr::from("abc");
        let b: &BStr = a.borrow();
        assert!(core::ptr::eq(b, BStr::new(a.as_str())));
    }

    #[test]
    fn test_as_ref() {
        let a = HipStr::from("abc");
        let b: &BStr = a.as_ref();
        assert!(core::ptr::eq(b, BStr::new(a.as_str())));
    }

    #[test]
    fn test_eq() {
        for (a, b) in [
            ("abc", "abc"),
            ("abc", "def"),
            (&"a".repeat(40), &"a".repeat(40)),
            ("other", &"a".repeat(40)),
        ] {
            let h = HipStr::from(a);
            let bstr: &BStr = b.as_ref();
            let bstring = BString::from(b);

            let expected = a == b;
            assert_eq!(h == *bstr, expected);
            assert_eq!(h != *bstr, !expected);
            assert_eq!(h == bstr, expected);
            assert_eq!(h != bstr, !expected);

            assert_eq!(h == bstring, expected);
            assert_eq!(h != bstring, !expected);
            assert_eq!(h == &bstring, expected);
            assert_eq!(h != &bstring, !expected);
        }
    }

    #[test]
    fn test_cmp() {
        for (a, b) in [
            ("abc", "abc"),
            ("abc", "ab"),
            ("abc", "def"),
            (&"a".repeat(40), &"a".repeat(40)),
            ("other", &"a".repeat(40)),
        ] {
            let a_hipstr = HipStr::from(a);
            let b_bstr: &BStr = b.as_ref();
            let b_bstring = BString::from(b);

            let expected = a.cmp(&b);

            if expected == Ordering::Equal {
                assert_eq!(a_hipstr, b_bstr);
                assert_eq!(a_hipstr, b_bstring);
            }

            assert_eq!(a_hipstr.partial_cmp(b_bstr), Some(expected));
            assert_eq!(a_hipstr.partial_cmp(&b_bstr), Some(expected));

            assert_eq!(a_hipstr.partial_cmp(&b_bstring), Some(expected));
            assert_eq!(a_hipstr.partial_cmp(&&b_bstring), Some(expected));
        }
    }

    #[test]
    fn test_try_from_bstring() {
        let s = "abc".repeat(20);
        let bstring = BString::from(s.as_str());
        let ptr = bstring.as_ptr();
        let hipstr = HipStr::try_from(bstring).unwrap();
        assert_eq!(hipstr, s);
        assert_eq!(hipstr.as_ptr(), ptr);

        let bstring = BString::from("abc");
        let hipstr = HipStr::try_from(bstring).unwrap();
        assert_eq!(hipstr, "abc");

        let bstr = BString::from(b"abc\xFF");
        let e = HipStr::try_from(bstr).unwrap_err();
        assert_eq!(e.utf8_error().valid_up_to(), 3);
    }

    #[test]
    fn test_try_from_bstr() {
        let s = "abc".repeat(20);
        let bstr = BStr::new(s.as_str());
        let hipstr = HipStr::try_from(bstr).unwrap();
        assert!(hipstr.is_borrowed());
        assert_eq!(hipstr, s);

        let bstr = BStr::new("abc");
        let hipstr = HipStr::try_from(bstr).unwrap();
        assert!(hipstr.is_borrowed());
        assert_eq!(hipstr, "abc");

        let bstr = BStr::new(b"abc\xFF");
        let e = HipStr::try_from(bstr).unwrap_err();
        assert_eq!(e.valid_up_to(), 3);
    }
}
