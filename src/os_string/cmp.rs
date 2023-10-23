//! Comparison trait implementations for `HipOsStr`

use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};

use super::HipOsStr;
use crate::alloc::borrow::Cow;
use crate::alloc::boxed::Box;
use crate::macros::{symmetric_eq, symmetric_ord};
use crate::Backend;

// Equality

impl<'borrow, B> Eq for HipOsStr<'borrow, B> where B: Backend {}

impl<'b1, 'b2, B1, B2> PartialEq<HipOsStr<'b1, B1>> for HipOsStr<'b2, B2>
where
    B1: Backend,
    B2: Backend,
{
    #[inline]
    fn eq(&self, other: &HipOsStr<B1>) -> bool {
        // TODO optimize if same
        self.as_os_str() == other.as_os_str()
    }
}

symmetric_eq! {

    // str
    <'borrow, B, > [where B: Backend] (a: str, b: HipOsStr<'borrow, B>) {
        a == b.as_os_str()
    }

    <'a, 'borrow, B, > [where B: Backend] (a: &'a str, b: HipOsStr<'borrow, B>) {
        *a == b.as_os_str()
    }

    <'borrow, B, > [where B: Backend] (a: Box<str>, b: HipOsStr<'borrow, B>) {
        **a == *b.as_os_str()
    }

    <'a, 'borrow, B, > [where B: Backend] (a: Cow<'a, str>, b: HipOsStr<'borrow, B>) {
        **a == *b.as_os_str()
    }

    // OsStr
    <'borrow, B, > [where B: Backend] (a: OsStr, b: HipOsStr<'borrow, B>) {
        a == b.as_os_str()
    }

    <'a, 'borrow, B, > [where B: Backend] (a: &'a OsStr, b: HipOsStr<'borrow, B>) {
        *a == b.as_os_str()
    }

    <'a, 'borrow, B, > [where B: Backend] (a: OsStr, b: &'a HipOsStr<'borrow, B>) {
        a == b.as_os_str()
    }

    <'a, 'borrow, B, > [where B: Backend] (a: Cow<'a, OsStr>, b: HipOsStr<'borrow, B>) {
        &**a == b.as_os_str()
    }

    // OsString
    <'borrow, B, > [where B: Backend] (a: OsString, b: HipOsStr<'borrow, B>) {
        a.as_os_str() == b.as_os_str()
    }

    // Path
    <'borrow, B, > [where B: Backend] (a: Path, b: HipOsStr<'borrow, B>) {
        a.as_os_str() == b.as_os_str()
    }

    <'a, 'borrow, B, > [where B: Backend] (a: &'a Path, b: HipOsStr<'borrow, B>) {
        a.as_os_str() == b.as_os_str()
    }

    <'b, 'borrow, B, > [where B: Backend] (a: Path, b: &'b HipOsStr<'borrow, B>) {
        a.as_os_str() == b.as_os_str()
    }

    <'a, 'borrow, B, > [where B: Backend] (a: Cow<'a, Path>, b: HipOsStr<'borrow, B>) {
        a.as_os_str() == b.as_os_str()
    }

    // PathBuf
    <'borrow, B, > [where B: Backend] (a: PathBuf, b: HipOsStr<'borrow, B>) {
        a.as_os_str() == b.as_os_str()
    }
}

impl<'borrow, B: Backend> Ord for HipOsStr<'borrow, B> {
    #[inline]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        OsStr::cmp(self, other)
    }
}

impl<'borrow, B: Backend> PartialOrd for HipOsStr<'borrow, B> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

symmetric_ord! {
    <'borrow, B, > [where B: Backend] (a: OsStr, b: HipOsStr<'borrow, B>) {
        <OsStr as PartialOrd<OsStr>>::partial_cmp(a, b)
    }

    <'a, 'borrow, B, > [where B: Backend] (a: &'a OsStr, b: HipOsStr<'borrow, B>) {
        <OsStr as PartialOrd>::partial_cmp(a, b)
    }

    <'a, 'borrow, B, > [where B: Backend] (a: Cow<'a, OsStr>, b: HipOsStr<'borrow, B>) {
        <OsStr as PartialOrd>::partial_cmp(a, b)
    }

    <'borrow, B, > [where B: Backend] (a: OsString, b: HipOsStr<'borrow, B>) {
        <OsStr as PartialOrd>::partial_cmp(a, b)
    }

    <'borrow, B, > [where B: Backend] (a: Path, b: HipOsStr<'borrow, B>) {
        <Path as PartialOrd<OsStr>>::partial_cmp(a, b)
    }

    <'a, 'borrow, B, > [where B: Backend] (a: &'a Path, b: HipOsStr<'borrow, B>) {
        <Path as PartialOrd<OsStr>>::partial_cmp(a, b)
    }

    <'a, 'borrow, B, > [where B: Backend] (a: Cow<'a, Path>, b: HipOsStr<'borrow, B>) {
        <Path as PartialOrd<OsStr>>::partial_cmp(a, b)
    }

    <'borrow, B, > [where B: Backend] (a: PathBuf, b: HipOsStr<'borrow, B>) {
        <Path as PartialOrd<OsStr>>::partial_cmp(a, b)
    }
}

#[cfg(test)]
mod tests {
    use core::cmp::Ordering;
    use std::ffi::OsStr;

    use crate::alloc::borrow::Cow;
    use crate::alloc::boxed::Box;
    use crate::HipOsStr;

    #[test]
    fn test_eq() {
        let string = "A".repeat(42);
        let slice: &str = &string;
        let b: Box<str> = Box::from(slice);
        let c: Cow<str> = Cow::Borrowed(slice);
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
