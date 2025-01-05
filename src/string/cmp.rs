//! Comparison trait implementations for `HipStr`

use alloc::borrow::Cow;
use alloc::boxed::Box;
use alloc::string::String;

use super::HipStr;
use crate::macros::{symmetric_eq, symmetric_ord};
use crate::Backend;

// Equality

impl<B> Eq for HipStr<'_, B> where B: Backend {}

impl<B1, B2> PartialEq<HipStr<'_, B1>> for HipStr<'_, B2>
where
    B1: Backend,
    B2: Backend,
{
    #[inline]
    fn eq(&self, other: &HipStr<B1>) -> bool {
        self.0 == other.0
    }
}

#[inline]
fn str_eq(a: impl AsRef<str>, b: impl AsRef<str>) -> bool {
    a.as_ref() == b.as_ref()
}

symmetric_eq! {
    [B] [where B: Backend] (str, HipStr<'_, B>) = str_eq;
    [B] [where B: Backend] (&str, HipStr<'_, B>) = str_eq;
    [B] [where B: Backend] (String, HipStr<'_, B>) = str_eq;
    [B] [where B: Backend] (Box<str>, HipStr<'_, B>) = str_eq;
    [B] [where B: Backend] (Cow<'_, str>, HipStr<'_, B>) = str_eq;
}

#[cfg(feature = "std")]
#[inline]
fn os_str_eq(a: impl AsRef<std::ffi::OsStr>, b: impl AsRef<str>) -> bool {
    a.as_ref() == b.as_ref()
}

#[cfg(feature = "std")]
symmetric_eq! {
    [B] [where B: Backend] (std::ffi::OsStr, HipStr<'_, B>) = os_str_eq;
    [B] [where B: Backend] (&std::ffi::OsStr, HipStr<'_, B>) = os_str_eq;
    [B] [where B: Backend] (std::ffi::OsString, HipStr<'_, B>) = os_str_eq;
    [B] [where B: Backend] (&std::ffi::OsString, HipStr<'_, B>) = os_str_eq;
}

// Order

impl<B> Ord for HipStr<'_, B>
where
    B: Backend,
{
    #[inline]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.as_str().cmp(other.as_str())
    }
}

impl<B1, B2> PartialOrd<HipStr<'_, B1>> for HipStr<'_, B2>
where
    B1: Backend,
    B2: Backend,
{
    #[inline]
    fn partial_cmp(&self, other: &HipStr<'_, B1>) -> Option<core::cmp::Ordering> {
        self.as_str().partial_cmp(other.as_str())
    }
}

#[inline]
fn str_cmp(a: impl AsRef<str>, b: impl AsRef<str>) -> Option<core::cmp::Ordering> {
    a.as_ref().partial_cmp(b.as_ref())
}

symmetric_ord! {
    [B] [where B: Backend] (str, HipStr<'_, B>) = str_cmp;
    [B] [where B: Backend] (&str, HipStr<'_, B>) = str_cmp;
    [B] [where B: Backend] (String, HipStr<'_, B>) = str_cmp;
}

#[cfg(feature = "std")]
#[inline]
fn os_str_cmp(a: impl AsRef<std::ffi::OsStr>, b: impl AsRef<str>) -> Option<core::cmp::Ordering> {
    a.as_ref().partial_cmp(b.as_ref())
}

#[cfg(feature = "std")]
symmetric_ord! {
    [B] [where B: Backend] (std::ffi::OsStr, HipStr<'_, B>) = os_str_cmp;
    [B] [where B: Backend] (&std::ffi::OsStr, HipStr<'_, B>) = os_str_cmp;
    [B] [where B: Backend] (std::ffi::OsString, HipStr<'_, B>) = os_str_cmp;
    [B] [where B: Backend] (&std::ffi::OsString, HipStr<'_, B>) = os_str_cmp;
}

#[cfg(test)]
mod tests {
    use alloc::borrow::Cow;
    use alloc::boxed::Box;
    use core::cmp::Ordering;

    use crate::HipStr;

    #[test]
    fn test_eq() {
        let string = "A".repeat(42);
        let slice: &str = &string;
        let b: Box<str> = Box::from(slice);
        let c: Cow<str> = Cow::Borrowed(slice);
        let h = HipStr::from(slice);
        let h2 = HipStr::borrowed(slice);

        assert_eq!(h, h);
        assert_eq!(h2, h2);
        assert_eq!(h, h2);
        assert_ne!(h2, h2.slice(0..4));

        assert_eq!(h, slice);
        assert_eq!(slice, h);

        assert_eq!(h, *slice);
        assert_eq!(*slice, h);

        assert_eq!(h, string);
        assert_eq!(string, h);

        assert_eq!(h, b);
        assert_eq!(b, h);

        assert_eq!(h, c);
        assert_eq!(c, h);
    }

    #[test]
    #[cfg(feature = "std")]
    fn test_eq_os_str() {
        let s = "abc";
        let os: &std::ffi::OsStr = s.as_ref();
        let h = HipStr::from(s);
        assert_eq!(h, os);
        assert_eq!(os, h);
        assert_eq!(&h, os);
        assert_eq!(os, &h);
    }

    #[test]
    #[cfg(feature = "std")]
    fn test_eq_os_string() {
        let s = "abc";
        let os: &std::ffi::OsStr = s.as_ref();
        let oss = os.to_os_string();
        let h = HipStr::from(s);
        assert_eq!(h, oss);
        assert_eq!(oss, h);
    }

    static BB_H: HipStr = HipStr::borrowed("bb");
    static BC_H: HipStr = HipStr::borrowed("bc");

    #[test]
    fn test_cmp() {
        assert_eq!(BB_H.partial_cmp(&BB_H), Some(Ordering::Equal));
        assert_eq!(BB_H.cmp(&BB_H), Ordering::Equal);

        assert!(BB_H < BC_H);
        assert_eq!(BB_H.cmp(&BC_H), Ordering::Less);
        assert_eq!(BB_H.partial_cmp(&BC_H), Some(Ordering::Less));
        assert_eq!(BC_H.cmp(&BB_H), Ordering::Greater);
        assert_eq!(BC_H.partial_cmp(&BB_H), Some(Ordering::Greater));
    }

    #[test]
    fn test_cmp_str() {
        assert!(&BB_H < "bc");
        assert!(&BB_H > "ba");
        assert!(&BB_H >= "bb");

        assert!("bc" > &BB_H);
        assert!("ba" < &BB_H);
        assert!("bb" <= &BB_H);

        assert!(BB_H < "bc");
        assert!(BB_H > "ba");
        assert!(BB_H >= "bb");

        assert!("bc" > BB_H);
        assert!("ba" < BB_H);
        assert!("bb" <= BB_H);
    }

    #[test]
    fn test_cmp_string() {
        use alloc::string::String;

        assert!(BB_H < String::from("bc"));
        assert!(BB_H > String::from("ba"));
        assert!(BB_H >= String::from("bb"));

        assert!(String::from("bc") > BB_H);
        assert!(String::from("ba") < BB_H);
        assert!(String::from("bb") <= BB_H);
    }

    #[test]
    #[cfg(feature = "std")]
    fn test_cmp_os_str() {
        use std::ffi::OsStr;

        assert!(OsStr::new("bc") > &BB_H);
        assert!(OsStr::new("ba") < &BB_H);
        assert!(OsStr::new("bb") <= &BB_H);

        assert!(&BB_H < OsStr::new("bc"));
        assert!(&BB_H > OsStr::new("ba"));
        assert!(&BB_H >= OsStr::new("bb"));

        assert!(OsStr::new("bc") > BB_H);
        assert!(OsStr::new("ba") < BB_H);
        assert!(OsStr::new("bb") <= BB_H);

        assert!(BB_H < OsStr::new("bc"));
        assert!(BB_H > OsStr::new("ba"));
        assert!(BB_H >= OsStr::new("bb"));
    }

    #[test]
    #[cfg(feature = "std")]
    fn test_cmp_os_string() {
        use std::ffi::OsString;

        assert!(OsString::from("bc") > BB_H);
        assert!(OsString::from("ba") < BB_H);
        assert!(OsString::from("bb") <= BB_H);

        assert!(BB_H < OsString::from("bc"));
        assert!(BB_H > OsString::from("ba"));
        assert!(BB_H >= OsString::from("bb"));
    }
}
