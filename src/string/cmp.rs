//! Comparison trait implementations for `HipStr`

use std::borrow::Cow;

use super::HipStr;
use crate::Backend;

// Equality

impl<B> Eq for HipStr<B> where B: Backend {}

impl<B1, B2> PartialEq<HipStr<B1>> for HipStr<B2>
where
    B1: Backend,
    B2: Backend,
{
    #[inline]
    fn eq(&self, other: &HipStr<B1>) -> bool {
        self.as_str() == other.as_str()
    }
}

impl<B> PartialEq<str> for HipStr<B>
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &str) -> bool {
        self.as_str() == other
    }
}

impl<B> PartialEq<HipStr<B>> for str
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &HipStr<B>) -> bool {
        self == other.as_str()
    }
}

impl<'a, B> PartialEq<&'a str> for HipStr<B>
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &&'a str) -> bool {
        self.as_str() == *other
    }
}

impl<'a, B> PartialEq<HipStr<B>> for &'a str
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &HipStr<B>) -> bool {
        *self == other.as_str()
    }
}

impl<B> PartialEq<String> for HipStr<B>
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &String) -> bool {
        self.as_str() == other.as_str()
    }
}

impl<B> PartialEq<HipStr<B>> for String
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &HipStr<B>) -> bool {
        self.as_str() == other.as_str()
    }
}

impl<B> PartialEq<Box<str>> for HipStr<B>
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &Box<str>) -> bool {
        self.as_str() == other.as_ref()
    }
}

impl<B> PartialEq<HipStr<B>> for Box<str>
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &HipStr<B>) -> bool {
        self.as_ref() == other.as_str()
    }
}

impl<'a, B> PartialEq<Cow<'a, str>> for HipStr<B>
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &Cow<'a, str>) -> bool {
        self.as_str() == other.as_ref()
    }
}

impl<'a, B> PartialEq<HipStr<B>> for Cow<'a, str>
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &HipStr<B>) -> bool {
        self.as_ref() == other.as_str()
    }
}

impl<B> Ord for HipStr<B>
where
    B: Backend,
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.as_str().cmp(other.as_str())
    }
}

impl<B> PartialOrd for HipStr<B>
where
    B: Backend,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.as_str().partial_cmp(other.as_str())
    }
}

#[cfg(test)]
mod tests {
    use std::borrow::Cow;
    use std::cmp::Ordering;

    use crate::HipStr;

    #[test]
    fn test_eq() {
        let string = "A".repeat(42);
        let slice: &str = &string;
        let b: Box<str> = Box::from(slice);
        let c: Cow<str> = Cow::Borrowed(slice);
        let h = HipStr::from(slice);

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
    fn test_ord() {
        let h1 = HipStr::from_static("abc");
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
