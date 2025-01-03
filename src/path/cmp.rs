//! Comparison trait implementations for `HipPath`

use alloc::borrow::Cow;
use alloc::boxed::Box;
use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};
use std::ptr;

use super::HipPath;
use crate::macros::symmetric_eq;
use crate::Backend;

// Equality

impl<B> Eq for HipPath<'_, B> where B: Backend {}

impl<B1, B2> PartialEq<HipPath<'_, B1>> for HipPath<'_, B2>
where
    B1: Backend,
    B2: Backend,
{
    #[inline]
    fn eq(&self, other: &HipPath<B1>) -> bool {
        ptr::eq(self.0.as_encoded_bytes(), other.0.as_encoded_bytes())
            || self.as_path() == other.as_path()
    }
}

symmetric_eq! {

    // Path*
    <> <B> <> [where B: Backend] (a : Path, b : HipPath<'_, B>) {
        a == b.as_path()
    }

    <> <B> <> [where B: Backend] (a : &Path, b : HipPath<'_, B>) {
        *a == b.as_path()
    }

    <> <B> <> [where B: Backend] (a: PathBuf, b: HipPath<'_, B>) {
        a.as_path() == b.as_path()
    }

    <> <B> <> [where B: Backend] (a: &PathBuf, b: HipPath<'_, B>) {
        a.as_path() == b.as_path()
    }

    <> <B> <> [where B: Backend] (a: Box<Path>, b: HipPath<'_, B>) {
        a.as_ref() == b.as_path()
    }

    <> <B> <> [where B: Backend] (a: &Box<Path>, b: HipPath<'_, B>) {
        a.as_ref() == b.as_path()
    }

    <> <B> <> [where B: Backend] (a: Cow<'_, Path>, b: HipPath<'_, B>) {
        a.as_ref() == b.as_path()
    }

    <> <B> <> [where B: Backend] (a: &Cow<'_, Path>, b: HipPath<'_, B>) {
        a.as_ref() == b.as_path()
    }

    // OsStr*
    <> <B> <> [where B: Backend] (a: OsStr, b: HipPath<'_, B>) {
        a == b.as_os_str()
    }

    <> <B> <> [where B: Backend] (a: &OsStr, b: HipPath<'_, B>) {
        *a == b.as_os_str()
    }

    <> <B> <> [where B: Backend] (a: OsString, b: HipPath<'_, B>) {
        a.as_os_str() == b.as_os_str()
    }

    <> <B> <> [where B: Backend] (a: &OsString, b: HipPath<'_, B>) {
        a.as_os_str() == b.as_os_str()
    }

    <> <B> <> [where B: Backend] (a: Box<OsStr>, b: HipPath<'_, B>) {
        a.as_ref() == b.as_os_str()
    }

    <> <B> <> [where B: Backend] (a: &Box<OsStr>, b: HipPath<'_, B>) {
        a.as_ref() == b.as_os_str()
    }
    <> <B> <> [where B: Backend] (a: Cow<'_, OsStr>, b: HipPath<'_, B>) {
        *a == b.as_os_str()
    }

    <> <B> <> [where B: Backend] (a: &Cow<'_, OsStr>, b: HipPath<'_, B>) {
        **a == b.as_os_str()
    }
}

impl<B> Ord for HipPath<'_, B>
where
    B: Backend,
{
    #[inline]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.as_os_str().cmp(other.as_os_str())
    }
}

impl<B> PartialOrd for HipPath<'_, B>
where
    B: Backend,
{
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[cfg(test)]
mod tests {
    use alloc::borrow::Cow;
    use alloc::boxed::Box;
    use core::cmp::Ordering;
    use std::ffi::OsStr;
    use std::path::Path;

    use crate::HipPath;

    #[test]
    fn test_eq() {
        let string = "A".repeat(42);
        let os_slice: &OsStr = string.as_ref();
        let path_slice: &Path = string.as_ref();
        let path_boxed: Box<Path> = Box::from(path_slice);
        let os_boxed: Box<OsStr> = Box::from(os_slice);
        let path_cow: Cow<Path> = Cow::Borrowed(path_slice);
        let os_cow: Cow<OsStr> = Cow::Borrowed(os_slice);
        let h = HipPath::from(path_slice);

        assert_eq!(h, path_slice);
        assert_eq!(path_slice, h);

        assert_eq!(h, os_slice);
        assert_eq!(os_slice, h);

        assert_eq!(h, *path_slice);
        assert_eq!(*path_slice, h);

        assert_eq!(h, *os_slice);
        assert_eq!(*os_slice, h);

        assert_eq!(h, path_boxed);
        assert_eq!(path_boxed, h);

        assert_eq!(h, os_boxed);
        assert_eq!(os_boxed, h);

        assert_eq!(h, path_cow);
        assert_eq!(path_cow, h);

        assert_eq!(h, os_cow);
        assert_eq!(os_cow, h);
    }

    #[test]
    #[cfg(feature = "std")]
    fn test_eq_os_str() {
        let s = "abc";
        let os: &std::ffi::OsStr = s.as_ref();
        let h = HipPath::from(s);
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
        let h = HipPath::from(s);
        assert_eq!(h, oss);
        assert_eq!(oss, h);
    }

    #[test]
    fn test_ord() {
        let h1 = HipPath::borrowed("abc");
        let h2 = HipPath::from("abd");

        assert_eq!(h1.partial_cmp(&h1), Some(Ordering::Equal));
        assert_eq!(h1.cmp(&h1), Ordering::Equal);

        assert!(h1 < h2);
        assert_eq!(h1.cmp(&h2), Ordering::Less);
        assert_eq!(h1.partial_cmp(&h2), Some(Ordering::Less));
        assert_eq!(h2.cmp(&h1), Ordering::Greater);
        assert_eq!(h2.partial_cmp(&h1), Some(Ordering::Greater));
    }
}
