//! Comparison trait implementations for `HipPath`

use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};
use std::ptr;

use super::HipPath;
use crate::alloc::borrow::Cow;
use crate::alloc::boxed::Box;
use crate::macros::symmetric_eq;
use crate::Backend;

// Equality

impl<'borrow, B> Eq for HipPath<'borrow, B> where B: Backend {}

impl<'b1, 'b2, B1, B2> PartialEq<HipPath<'b1, B1>> for HipPath<'b2, B2>
where
    B1: Backend,
    B2: Backend,
{
    #[inline]
    fn eq(&self, other: &HipPath<B1>) -> bool {
        // TODO optimize is same pointer
        ptr::eq(self.0.as_encoded_bytes(), other.0.as_encoded_bytes())
            || self.as_path() == other.as_path()
    }
}

symmetric_eq! {

    // Path*
    <'borrow> <B> <> [where B: Backend] (a : Path, b : HipPath<'borrow, B>) {
        a == b.as_path()
    }

    <'a, 'borrow> <B> <> [where B: Backend] (a : &'a Path, b : HipPath<'borrow, B>) {
        *a == b.as_path()
    }

    <'borrow> <B> <> [where B: Backend] (a: PathBuf, b: HipPath<'borrow, B>) {
        a.as_path() == b.as_path()
    }

    <'a, 'borrow> <B> <> [where B: Backend] (a: &'a PathBuf, b: HipPath<'borrow, B>) {
        a.as_path() == b.as_path()
    }

    <'borrow> <B> <> [where B: Backend] (a: Box<Path>, b: HipPath<'borrow, B>) {
        a.as_ref() == b.as_path()
    }

    <'a, 'borrow> <B> <> [where B: Backend] (a: &'a Box<Path>, b: HipPath<'borrow, B>) {
        a.as_ref() == b.as_path()
    }

    <'a, 'b> <B> <> [where B: Backend] (a: Cow<'a, Path>, b: HipPath<'b, B>) {
        a.as_ref() == b.as_path()
    }

    <'a, 'b> <B> <> [where B: Backend] (a: &'a Cow<'a, Path>, b: HipPath<'b, B>) {
        a.as_ref() == b.as_path()
    }

    // OsStr*
    <'borrow> <B> <> [where B: Backend] (a: OsStr, b: HipPath<'borrow, B>) {
        a == b.as_os_str()
    }

    <'a, 'borrow> <B> <> [where B: Backend] (a: &'a OsStr, b: HipPath<'borrow, B>) {
        *a == b.as_os_str()
    }

    <'borrow> <B> <> [where B: Backend] (a: OsString, b: HipPath<'borrow, B>) {
        a.as_os_str() == b.as_os_str()
    }

    <'a, 'borrow> <B> <> [where B: Backend] (a: &'a OsString, b: HipPath<'borrow, B>) {
        a.as_os_str() == b.as_os_str()
    }

    <'borrow> <B> <> [where B: Backend] (a: Box<OsStr>, b: HipPath<'borrow, B>) {
        a.as_ref() == b.as_os_str()
    }

    <'a, 'borrow> <B> <> [where B: Backend] (a: &'a Box<OsStr>, b: HipPath<'borrow, B>) {
        a.as_ref() == b.as_os_str()
    }
    <'a, 'b> <B> <> [where B: Backend] (a: Cow<'a, OsStr>, b: HipPath<'b, B>) {
        *a == b.as_os_str()
    }

    <'a, 'b> <B> <> [where B: Backend] (a: &'a Cow<'a, OsStr>, b: HipPath<'b, B>) {
        **a == b.as_os_str()
    }
}

impl<'borrow, B> Ord for HipPath<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.as_os_str().cmp(other.as_os_str())
    }
}

impl<'borrow, B> PartialOrd for HipPath<'borrow, B>
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
    use core::cmp::Ordering;
    use std::ffi::OsStr;
    use std::path::Path;

    use crate::alloc::borrow::Cow;
    use crate::alloc::boxed::Box;
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
