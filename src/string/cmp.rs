//! Comparison trait implementations for `HipStr`

use super::HipStr;
use crate::alloc::borrow::Cow;
use crate::alloc::boxed::Box;
use crate::alloc::string::String;
use crate::Backend;

// Equality

impl<'borrow, B> Eq for HipStr<'borrow, B> where B: Backend {}

impl<'b1, 'b2, B1, B2> PartialEq<HipStr<'b1, B1>> for HipStr<'b2, B2>
where
    B1: Backend,
    B2: Backend,
{
    #[inline]
    fn eq(&self, other: &HipStr<B1>) -> bool {
        let a = self.as_str();
        let b = other.as_str();
        core::ptr::eq(a, b) || a == b
    }
}

impl<'borrow, B> PartialEq<str> for HipStr<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &str) -> bool {
        self.as_str() == other
    }
}

impl<'borrow, B> PartialEq<HipStr<'borrow, B>> for str
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &HipStr<B>) -> bool {
        self == other.as_str()
    }
}

impl<'a, 'borrow, B> PartialEq<&'a str> for HipStr<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &&'a str) -> bool {
        self.as_str() == *other
    }
}

impl<'a, 'borrow, B> PartialEq<HipStr<'borrow, B>> for &'a str
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &HipStr<B>) -> bool {
        *self == other.as_str()
    }
}

impl<'borrow, B> PartialEq<String> for HipStr<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &String) -> bool {
        self.as_str() == other.as_str()
    }
}

impl<'borrow, B> PartialEq<HipStr<'borrow, B>> for String
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &HipStr<B>) -> bool {
        self.as_str() == other.as_str()
    }
}

impl<'borrow, B> PartialEq<Box<str>> for HipStr<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &Box<str>) -> bool {
        self.as_str() == other.as_ref()
    }
}

impl<'borrow, B> PartialEq<HipStr<'borrow, B>> for Box<str>
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &HipStr<B>) -> bool {
        self.as_ref() == other.as_str()
    }
}

impl<'a, 'b, B> PartialEq<Cow<'a, str>> for HipStr<'b, B>
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &Cow<'a, str>) -> bool {
        self.as_str() == other.as_ref()
    }
}

impl<'a, 'b, B> PartialEq<HipStr<'a, B>> for Cow<'b, str>
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &HipStr<B>) -> bool {
        self.as_ref() == other.as_str()
    }
}

#[cfg(feature = "std")]
impl<'borrow, B> PartialEq<std::ffi::OsStr> for HipStr<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &std::ffi::OsStr) -> bool {
        self.as_str().eq(other)
    }
}

#[cfg(feature = "std")]
impl<'borrow, B> PartialEq<HipStr<'borrow, B>> for std::ffi::OsStr
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &HipStr<'borrow, B>) -> bool {
        self.eq(other.as_str())
    }
}

#[cfg(feature = "std")]
impl<'a, 'borrow, B> PartialEq<&'a std::ffi::OsStr> for HipStr<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &&'a std::ffi::OsStr) -> bool {
        self.as_str().eq(*other)
    }
}

#[cfg(feature = "std")]
impl<'a, 'borrow, B> PartialEq<HipStr<'borrow, B>> for &'a std::ffi::OsStr
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &HipStr<'borrow, B>) -> bool {
        (*self).eq(other.as_str())
    }
}

#[cfg(feature = "std")]
impl<'borrow, B> PartialEq<std::ffi::OsString> for HipStr<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &std::ffi::OsString) -> bool {
        self.as_str().eq(other)
    }
}

#[cfg(feature = "std")]
impl<'borrow, B> PartialEq<HipStr<'borrow, B>> for std::ffi::OsString
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &HipStr<'borrow, B>) -> bool {
        self.eq(other.as_str())
    }
}

impl<'borrow, B> Ord for HipStr<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.as_str().cmp(other.as_str())
    }
}

impl<'borrow, B> PartialOrd for HipStr<'borrow, B>
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

    use crate::alloc::borrow::Cow;
    use crate::alloc::boxed::Box;
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

    #[test]
    fn test_ord() {
        let h1 = HipStr::borrowed("abc");
        let h2 = HipStr::from("abd");

        assert_eq!(h1.partial_cmp(&h1), Some(Ordering::Equal));
        assert_eq!(h1.cmp(&h1), Ordering::Equal);

        assert!(h1 < h2);
        assert_eq!(h1.cmp(&h2), Ordering::Less);
        assert_eq!(h1.partial_cmp(&h2), Some(Ordering::Less));
        assert_eq!(h2.cmp(&h1), Ordering::Greater);
        assert_eq!(h2.partial_cmp(&h1), Some(Ordering::Greater));
    }
}
