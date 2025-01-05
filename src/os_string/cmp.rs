//! Comparison trait implementations for `HipOsStr`

use std::borrow::Cow;
use std::boxed::Box;
use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};

use super::HipOsStr;
use crate::macros::{symmetric_eq, symmetric_ord};
use crate::Backend;

// Equality

impl<B> Eq for HipOsStr<'_, B> where B: Backend {}

impl<B1, B2> PartialEq<HipOsStr<'_, B1>> for HipOsStr<'_, B2>
where
    B1: Backend,
    B2: Backend,
{
    #[inline]
    fn eq(&self, other: &HipOsStr<B1>) -> bool {
        // compare the encoded bytes.
        self.0 == other.0
    }
}

#[inline]
fn os_str_eq(a: impl AsRef<OsStr>, b: impl AsRef<OsStr>) -> bool {
    a.as_ref() == b.as_ref()
}

#[inline]
fn path_eq(a: impl AsRef<Path>, b: impl AsRef<OsStr>) -> bool {
    a.as_ref() == b.as_ref()
}

symmetric_eq! {

    // OsStr
    [B] [where B: Backend] (OsStr, HipOsStr<'_, B>) = os_str_eq;
    [B] [where B: Backend] (&OsStr, HipOsStr<'_, B>) = os_str_eq;
    [B] [where B: Backend] (Box<OsStr>, HipOsStr<'_, B>) = os_str_eq;
    [B] [where B: Backend] (&Box<OsStr>, HipOsStr<'_, B>) = os_str_eq;
    [B] [where B: Backend] (Cow<'_, OsStr>, HipOsStr<'_, B>) = os_str_eq;
    [B] [where B: Backend] (&Cow<'_, OsStr>, HipOsStr<'_, B>) = os_str_eq;
    [B] [where B: Backend] (OsString, HipOsStr<'_, B>) = os_str_eq;
    [B] [where B: Backend] (&OsString, HipOsStr<'_, B>) = os_str_eq;

    // Path variants
    [B] [where B: Backend] (Path, HipOsStr<'_, B>) = path_eq;
    [B] [where B: Backend] (&Path, HipOsStr<'_, B>) = path_eq;
    [B] [where B: Backend] (Box<Path>, HipOsStr<'_, B>) = path_eq;
    [B] [where B: Backend] (&Box<Path>, HipOsStr<'_, B>) = path_eq;
    [B] [where B: Backend] (Cow<'_, Path>, HipOsStr<'_, B>) = path_eq;
    [B] [where B: Backend] (&Cow<'_, Path>, HipOsStr<'_, B>) = path_eq;
    [B] [where B: Backend] (PathBuf, HipOsStr<'_, B>) = path_eq;
    [B] [where B: Backend] (&PathBuf, HipOsStr<'_, B>) = path_eq;
}

impl<B: Backend> Ord for HipOsStr<'_, B> {
    #[inline]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        OsStr::cmp(self, other)
    }
}

impl<B: Backend> PartialOrd for HipOsStr<'_, B> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[inline]
fn os_str_partial_cmp(a: impl AsRef<OsStr>, b: impl AsRef<OsStr>) -> Option<core::cmp::Ordering> {
    a.as_ref().partial_cmp(b.as_ref())
}

#[inline]
fn path_partial_cmp(a: impl AsRef<Path>, b: impl AsRef<OsStr>) -> Option<core::cmp::Ordering> {
    a.as_ref().partial_cmp(b.as_ref())
}

symmetric_ord! {
    [B] [where B: Backend] (OsStr, HipOsStr<'_, B>) = os_str_partial_cmp;
    [B] [where B: Backend] (&OsStr, HipOsStr<'_, B>) = os_str_partial_cmp;

    [B] [where B: Backend] (Box<OsStr>, HipOsStr<'_, B>) = os_str_partial_cmp;
    [B] [where B: Backend] (&Box<OsStr>, HipOsStr<'_, B>) = os_str_partial_cmp;

    [B] [where B: Backend] (Cow<'_, OsStr>, HipOsStr<'_, B>) = os_str_partial_cmp;
    [B] [where B: Backend] (&Cow<'_, OsStr>, HipOsStr<'_, B>) = os_str_partial_cmp;

    [B] [where B: Backend] (OsString, HipOsStr<'_, B>) = os_str_partial_cmp;
    [B] [where B: Backend] (&OsString, HipOsStr<'_, B>) = os_str_partial_cmp;

    [B] [where B: Backend] (Path, HipOsStr<'_, B>) = path_partial_cmp;
    [B] [where B: Backend] (&Path, HipOsStr<'_, B>) = path_partial_cmp;

    [B] [where B: Backend] (Cow<'_, Path>, HipOsStr<'_, B>) = path_partial_cmp;
    [B] [where B: Backend] (&Cow<'_, Path>, HipOsStr<'_, B>) = path_partial_cmp;

    [B] [where B: Backend] (PathBuf, HipOsStr<'_, B>) = path_partial_cmp;
    [B] [where B: Backend] (&PathBuf, HipOsStr<'_, B>) = path_partial_cmp;
}

#[cfg(test)]
mod tests {
    use alloc::borrow::Cow;
    use alloc::boxed::Box;
    use core::cmp::Ordering;
    use std::ffi::OsStr;

    use crate::HipOsStr;

    #[test]
    fn test_eq() {
        let string = "A".repeat(42);
        let slice = OsStr::new(&string);
        let b: Box<OsStr> = Box::from(slice);
        let c: Cow<OsStr> = Cow::Borrowed(slice);
        let h = HipOsStr::from(slice);

        assert_eq!(h, slice);
        assert_eq!(slice, h);

        assert_eq!(h, *slice);
        assert_eq!(*slice, h);

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
        let h = HipOsStr::from(s);
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
        let h = HipOsStr::from(s);
        assert_eq!(h, oss);
        assert_eq!(oss, h);
    }

    #[test]
    fn test_ord() {
        let h1 = HipOsStr::borrowed("abc");
        let h2 = HipOsStr::from("abd");

        assert_eq!(h1.partial_cmp(&h1), Some(Ordering::Equal));
        assert_eq!(h1.cmp(&h1), Ordering::Equal);

        assert!(h1 < h2);
        assert_eq!(h1.cmp(&h2), Ordering::Less);
        assert_eq!(h1.partial_cmp(&h2), Some(Ordering::Less));
        assert_eq!(h2.cmp(&h1), Ordering::Greater);
        assert_eq!(h2.partial_cmp(&h1), Some(Ordering::Greater));

        assert_eq!(
            OsStr::partial_cmp(h1.as_os_str(), &h2),
            Some(Ordering::Less)
        );
        assert_eq!(
            OsStr::partial_cmp(h2.as_os_str(), &h1),
            Some(Ordering::Greater)
        );
        assert!(h1 < h2.as_os_str());
    }
}
