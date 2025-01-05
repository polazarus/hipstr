//! Comparison trait implementations for `HipPath`

use alloc::borrow::Cow;
use alloc::boxed::Box;
use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};
use std::ptr;

use super::HipPath;
use crate::macros::{symmetric_eq, symmetric_ord};
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
#[inline]
fn path_eq(a: impl AsRef<Path>, b: impl AsRef<Path>) -> bool {
    a.as_ref() == b.as_ref()
}

#[inline]
fn os_str_eq(a: impl AsRef<OsStr>, b: impl AsRef<OsStr>) -> bool {
    a.as_ref() == b.as_ref()
}

symmetric_eq! {

    // Path*
    [B] [where B: Backend] (Path, HipPath<'_, B>) = path_eq;
    [B] [where B: Backend] (&Path, HipPath<'_, B>) = path_eq;
    [B] [where B: Backend] (PathBuf, HipPath<'_, B>) = path_eq;
    [B] [where B: Backend] (&PathBuf, HipPath<'_, B>) = path_eq;
    [B] [where B: Backend] (Box<Path>, HipPath<'_, B>) = path_eq;
    [B] [where B: Backend] (&Box<Path>, HipPath<'_, B>) = path_eq;
    [B] [where B: Backend] (Cow<'_, Path>, HipPath<'_, B>) = path_eq;
    [B] [where B: Backend] (&Cow<'_, Path>, HipPath<'_, B>) = path_eq;

    // OsStr*
    [B] [where B: Backend] (OsStr, HipPath<'_, B>) = os_str_eq;
    [B] [where B: Backend] (&OsStr, HipPath<'_, B>) = os_str_eq;
    [B] [where B: Backend] (OsString, HipPath<'_, B>) = os_str_eq;
    [B] [where B: Backend] (&OsString, HipPath<'_, B>) = os_str_eq;
    [B] [where B: Backend] (Box<OsStr>, HipPath<'_, B>) = os_str_eq;
    [B] [where B: Backend] (&Box<OsStr>, HipPath<'_, B>) = os_str_eq;
    [B] [where B: Backend] (Cow<'_, OsStr>, HipPath<'_, B>) = os_str_eq;
    [B] [where B: Backend] (&Cow<'_, OsStr>, HipPath<'_, B>) = os_str_eq;
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

impl<B1: Backend, B2: Backend> PartialOrd<HipPath<'_, B1>> for HipPath<'_, B2> {
    #[inline]
    fn partial_cmp(&self, other: &HipPath<'_, B1>) -> Option<core::cmp::Ordering> {
        self.as_os_str().partial_cmp(other.as_os_str())
    }
}

#[inline]
fn os_str_partial_cmp(a: impl AsRef<OsStr>, b: impl AsRef<Path>) -> Option<core::cmp::Ordering> {
    a.as_ref().partial_cmp(b.as_ref())
}

#[inline]
fn path_partial_cmp(a: impl AsRef<Path>, b: impl AsRef<Path>) -> Option<core::cmp::Ordering> {
    a.as_ref().partial_cmp(b.as_ref())
}

symmetric_ord! {
    // Path variants
    [B] [where B: Backend] (Path, HipPath<'_, B>) = path_partial_cmp;
    [B] [where B: Backend] (&Path, HipPath<'_, B>) = path_partial_cmp;
    [B] [where B: Backend] (PathBuf, HipPath<'_, B>) = path_partial_cmp;
    [B] [where B: Backend] (&PathBuf, HipPath<'_, B>) = path_partial_cmp;
    [B] [where B: Backend] (Box<Path>, HipPath<'_, B>) = path_partial_cmp;
    [B] [where B: Backend] (&Box<Path>, HipPath<'_, B>) = path_partial_cmp;
    [B] [where B: Backend] (Cow<'_, Path>, HipPath<'_, B>) = path_partial_cmp;
    [B] [where B: Backend] (&Cow<'_, Path>, HipPath<'_, B>) = path_partial_cmp;

    // OsStr variants
    [B] [where B: Backend] (OsStr, HipPath<'_, B>) = os_str_partial_cmp;
    [B] [where B: Backend] (&OsStr, HipPath<'_, B>) = os_str_partial_cmp;
    [B] [where B: Backend] (OsString, HipPath<'_, B>) = os_str_partial_cmp;
    [B] [where B: Backend] (&OsString, HipPath<'_, B>) = os_str_partial_cmp;
    [B] [where B: Backend] (Box<OsStr>, HipPath<'_, B>) = os_str_partial_cmp;
    [B] [where B: Backend] (&Box<OsStr>, HipPath<'_, B>) = os_str_partial_cmp;
    [B] [where B: Backend] (Cow<'_, OsStr>, HipPath<'_, B>) = os_str_partial_cmp;
    [B] [where B: Backend] (&Cow<'_, OsStr>, HipPath<'_, B>) = os_str_partial_cmp;
}

#[cfg(test)]
mod tests {
    use alloc::borrow::Cow;
    use alloc::boxed::Box;
    use core::cmp::Ordering;
    use std::ffi::{OsStr, OsString};
    use std::path::{Path, PathBuf};

    use crate::HipPath;

    #[test]
    fn test_eq() {
        let string = "A".repeat(42);

        let path_slice: &Path = string.as_ref();
        let path_boxed: Box<Path> = Box::from(path_slice);
        let path_cow: Cow<Path> = Cow::Borrowed(path_slice);
        let path_buf = PathBuf::from(path_slice);

        let os_slice: &OsStr = string.as_ref();
        let os_boxed: Box<OsStr> = Box::from(os_slice);
        let os_cow: Cow<OsStr> = Cow::Borrowed(os_slice);
        let os_string = OsString::from(os_slice);

        let h = HipPath::from(path_slice);
        let h2 = HipPath::from(path_slice);

        assert_eq!(h, h2);
        assert_eq!(h2, h);

        assert_eq!(h, path_slice);
        assert_eq!(path_slice, h);

        assert_eq!(h, *path_slice);
        assert_eq!(*path_slice, h);

        assert_eq!(h, path_boxed);
        assert_eq!(path_boxed, h);

        assert_eq!(h, path_cow);
        assert_eq!(path_cow, h);

        assert_eq!(h, path_buf);
        assert_eq!(path_buf, h);

        assert_eq!(h, os_slice);
        assert_eq!(os_slice, h);

        assert_eq!(h, *os_slice);
        assert_eq!(*os_slice, h);

        assert_eq!(h, os_boxed);
        assert_eq!(os_boxed, h);

        assert_eq!(h, os_cow);
        assert_eq!(os_cow, h);

        assert_eq!(h, os_string);
        assert_eq!(os_string, h);
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
