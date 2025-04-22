//! Comparison trait implementations for `HipOsStr`

use std::borrow::Cow;
use std::boxed::Box;
use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};

use super::HipOsStr;
use crate::backend::Backend;
use crate::macros::{symmetric_eq, symmetric_ord};
use crate::path::HipPath;

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
    use std::ffi::OsStr;
    use std::path::Path;

    use crate::{HipOsStr, HipPath};

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
        for (a, b) in [("abc", "abd"), ("abc", "abc"), ("ab", "abc")] {
            let a_os_str = OsStr::new(a);
            let a_cow_os_str = Cow::Borrowed(a_os_str);
            let a_box_os_str: Box<OsStr> = Box::from(a_os_str);
            let a_os_string = a_os_str.to_os_string();

            let b_os_str = OsStr::new(b);
            let b_cow_os_str = Cow::Borrowed(b_os_str);
            let b_box_os_str: Box<OsStr> = Box::from(b_os_str);
            let b_os_string = b_os_str.to_os_string();

            let a_hip_os_str = HipOsStr::from(a_os_str);
            let a_hip_os_str_borrow = HipOsStr::borrowed(a_os_str);
            let b_hip_os_str = HipOsStr::from(b_os_str);
            let a_hip_path = HipPath::from(a_os_str);
            let b_hip_path = HipPath::from(b_os_str);

            let a_path = Path::new(a);
            let a_box_path: Box<Path> = Box::from(a_path);
            let a_cow_path = Cow::Borrowed(a_path);
            let a_path_buf = a_path.to_path_buf();

            let b_path = Path::new(b);
            let b_box_path: Box<Path> = Box::from(b_path);
            let b_cow_path = Cow::Borrowed(b_path);
            let b_path_buf = b_path.to_path_buf();

            let expected = a_os_str.cmp(b_os_str);

            assert_eq!(a_hip_os_str.cmp(&b_hip_os_str), expected);

            assert_eq!(a_hip_os_str.partial_cmp(&b_hip_os_str), Some(expected));

            assert_eq!(a_hip_os_str_borrow.cmp(&b_hip_os_str), expected);

            assert_eq!(a_hip_path.partial_cmp(&b_hip_os_str), Some(expected));
            assert_eq!(a_hip_os_str.partial_cmp(&b_hip_path), Some(expected));

            assert_eq!(a_os_str.partial_cmp(&b_hip_os_str), Some(expected));
            assert_eq!(a_hip_os_str.partial_cmp(&b_os_str), Some(expected));

            assert_eq!(a_box_os_str.partial_cmp(&b_hip_os_str), Some(expected));
            assert_eq!(a_hip_os_str.partial_cmp(&b_box_os_str), Some(expected));

            assert_eq!(a_cow_os_str.partial_cmp(&b_hip_os_str), Some(expected));
            assert_eq!(a_hip_os_str.partial_cmp(&b_cow_os_str), Some(expected));

            assert_eq!(a_os_string.partial_cmp(&b_hip_os_str), Some(expected));
            assert_eq!(a_hip_os_str.partial_cmp(&b_os_string), Some(expected));

            assert_eq!(a_path.partial_cmp(&b_hip_os_str), Some(expected));
            assert_eq!(a_hip_os_str.partial_cmp(b_path), Some(expected));

            assert_eq!((&a_path).partial_cmp(&b_hip_os_str), Some(expected));
            assert_eq!(a_hip_os_str.partial_cmp(&b_path), Some(expected));

            assert_eq!(a_box_path.partial_cmp(&b_hip_os_str), Some(expected));
            assert_eq!(a_hip_os_str.partial_cmp(&b_box_path), Some(expected));

            assert_eq!(a_cow_path.partial_cmp(&b_hip_os_str), Some(expected));
            assert_eq!(a_hip_os_str.partial_cmp(&b_cow_path), Some(expected));

            assert_eq!(a_path_buf.partial_cmp(&b_hip_os_str), Some(expected));
            assert_eq!(a_hip_os_str.partial_cmp(&b_path_buf), Some(expected));
        }
    }
}
