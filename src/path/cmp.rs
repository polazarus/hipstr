//! Comparison trait implementations for `HipPath`

use alloc::borrow::Cow;
use alloc::boxed::Box;
use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};
use std::ptr;

use super::HipPath;
use crate::backend::Backend;
use crate::macros::{symmetric_eq, symmetric_ord};

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
        self.as_path().cmp(other.as_path())
    }
}

impl<B1: Backend, B2: Backend> PartialOrd<HipPath<'_, B1>> for HipPath<'_, B2> {
    #[inline]
    fn partial_cmp(&self, other: &HipPath<'_, B1>) -> Option<core::cmp::Ordering> {
        self.as_path().partial_cmp(other.as_path())
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
        for (a, b) in [
            ("abc", "abd"),
            ("abc", "abc"),
            ("ab", "abc"),
            ("a//", "a/"),
            ("/a//b/", "/a/b/c"),
        ] {
            let a_os_str = OsStr::new(a);
            let a_cow_os_str = Cow::Borrowed(a_os_str);
            let a_box_os_str: Box<OsStr> = Box::from(a_os_str);
            let a_os_string = a_os_str.to_os_string();

            let b_os_str = OsStr::new(b);
            let b_cow_os_str = Cow::Borrowed(b_os_str);
            let b_box_os_str: Box<OsStr> = Box::from(b_os_str);
            let b_os_string = b_os_str.to_os_string();

            let a_hip_path = HipPath::from(a_os_str);
            let a_hip_path_borrow = HipPath::borrowed(a_os_str);
            let b_hip_path = HipPath::from(b_os_str);

            let a_path = Path::new(a);
            let a_box_path: Box<Path> = Box::from(a_path);
            let a_cow_path = Cow::Borrowed(a_path);
            let a_path_buf = a_path.to_path_buf();

            let b_path = Path::new(b);
            let b_box_path: Box<Path> = Box::from(b_path);
            let b_cow_path = Cow::Borrowed(b_path);
            let b_path_buf = b_path.to_path_buf();

            let expected = a_path.cmp(b_path);
            assert_eq!(Some(expected), a_path.partial_cmp(b_os_str));
            let expected_os_str = expected;

            if expected == core::cmp::Ordering::Equal {
                assert_eq!(a_hip_path, b_hip_path);
            } else {
                assert_ne!(a_hip_path, b_hip_path);
            }

            assert_eq!(a_hip_path.cmp(&b_hip_path), expected);

            assert_eq!(a_hip_path.partial_cmp(&b_hip_path), Some(expected));

            assert_eq!(a_hip_path_borrow.cmp(&b_hip_path), expected);

            assert_eq!(a_hip_path.partial_cmp(&b_hip_path), Some(expected));
            assert_eq!(a_hip_path.partial_cmp(&b_hip_path), Some(expected));

            assert_eq!(a_os_str.partial_cmp(&b_hip_path), Some(expected_os_str));
            assert_eq!(a_hip_path.partial_cmp(b_os_str), Some(expected_os_str));

            assert_eq!((&a_os_str).partial_cmp(&b_hip_path), Some(expected_os_str));
            assert_eq!(a_hip_path.partial_cmp(&b_os_str), Some(expected_os_str));

            assert_eq!(a_box_os_str.partial_cmp(&b_hip_path), Some(expected_os_str));
            assert_eq!(a_hip_path.partial_cmp(&b_box_os_str), Some(expected_os_str));

            assert_eq!(a_cow_os_str.partial_cmp(&b_hip_path), Some(expected_os_str));
            assert_eq!(a_hip_path.partial_cmp(&b_cow_os_str), Some(expected_os_str));

            assert_eq!(a_os_string.partial_cmp(&b_hip_path), Some(expected_os_str));
            assert_eq!(a_hip_path.partial_cmp(&b_os_string), Some(expected_os_str));

            assert_eq!(a_path.partial_cmp(&b_hip_path), Some(expected));
            assert_eq!(a_hip_path.partial_cmp(b_path), Some(expected));

            assert_eq!((&a_path).partial_cmp(&b_hip_path), Some(expected));
            assert_eq!(a_hip_path.partial_cmp(&b_path), Some(expected));

            assert_eq!(a_box_path.partial_cmp(&b_hip_path), Some(expected));
            assert_eq!(a_hip_path.partial_cmp(&b_box_path), Some(expected));

            assert_eq!(a_cow_path.partial_cmp(&b_hip_path), Some(expected));
            assert_eq!(a_hip_path.partial_cmp(&b_cow_path), Some(expected));

            assert_eq!(a_path_buf.partial_cmp(&b_hip_path), Some(expected));
            assert_eq!(a_hip_path.partial_cmp(&b_path_buf), Some(expected));
        }
    }
}
