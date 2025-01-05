//! Comparison trait implementations for `HipOsStr`

use std::borrow::Cow;
use std::boxed::Box;
use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};

use super::HipOsStr;
use crate::macros::{symmetric_eq, symmetric_ord};
use crate::path::HipPath;
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

    [B1: Backend, B2: Backend] (HipPath<'_, B1>, HipOsStr<'_, B2>) = path_eq;
}

impl<B: Backend> Ord for HipOsStr<'_, B> {
    #[inline]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.as_os_str().cmp(other.as_os_str())
    }
}

impl<B1, B2> PartialOrd<HipOsStr<'_, B1>> for HipOsStr<'_, B2>
where
    B1: Backend,
    B2: Backend,
{
    #[inline]
    fn partial_cmp(&self, other: &HipOsStr<'_, B1>) -> Option<core::cmp::Ordering> {
        self.as_os_str().partial_cmp(other.as_os_str())
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

    [B] [where B: Backend] (Box<Path>, HipOsStr<'_, B>) = path_partial_cmp;
    [B] [where B: Backend] (&Box<Path>, HipOsStr<'_, B>) = path_partial_cmp;

    [B] [where B: Backend] (Cow<'_, Path>, HipOsStr<'_, B>) = path_partial_cmp;
    [B] [where B: Backend] (&Cow<'_, Path>, HipOsStr<'_, B>) = path_partial_cmp;

    [B] [where B: Backend] (PathBuf, HipOsStr<'_, B>) = path_partial_cmp;
    [B] [where B: Backend] (&PathBuf, HipOsStr<'_, B>) = path_partial_cmp;

    [B1: Backend, B2: Backend] (HipPath<'_, B1>, HipOsStr<'_, B2>) = path_partial_cmp;
}

#[cfg(test)]
mod tests {
    use alloc::borrow::Cow;
    use alloc::boxed::Box;
    use core::cmp::Ordering;
    use std::ffi::OsStr;
    use std::path::Path;

    use crate::HipOsStr;

    #[test]
    fn test_eq() {
        let string = "A".repeat(42);

        let os_str = OsStr::new(&string);
        let box_os_str: Box<OsStr> = Box::from(os_str);
        let cow_os_str: Cow<OsStr> = Cow::Borrowed(os_str);
        let os_string = os_str.to_os_string();

        let path = Path::new(&string);
        let box_path: Box<Path> = Box::from(path);
        let cow_path = Cow::Borrowed(path);
        let path_buf = path.to_path_buf();

        let hip_os_str = HipOsStr::from(os_str);

        assert_eq!(hip_os_str, os_str);
        assert_eq!(os_str, hip_os_str);

        assert_eq!(hip_os_str, *os_str);
        assert_eq!(*os_str, hip_os_str);

        assert_eq!(hip_os_str, box_os_str);
        assert_eq!(box_os_str, hip_os_str);

        assert_eq!(hip_os_str, cow_os_str);
        assert_eq!(cow_os_str, hip_os_str);

        assert_eq!(hip_os_str, os_string);
        assert_eq!(os_string, hip_os_str);

        assert_eq!(hip_os_str, path);
        assert_eq!(path, hip_os_str);

        assert_eq!(hip_os_str, *path);
        assert_eq!(*path, hip_os_str);

        assert_eq!(hip_os_str, box_path);
        assert_eq!(box_path, hip_os_str);

        assert_eq!(hip_os_str, cow_path);
        assert_eq!(cow_path, hip_os_str);

        assert_eq!(hip_os_str, path_buf);
        assert_eq!(path_buf, hip_os_str);
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
