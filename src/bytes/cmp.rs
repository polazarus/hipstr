//! Comparison trait implementations for `HipByt`

use std::borrow::Cow;

use super::HipByt;
use crate::Backend;

// Equality

impl<'borrow, B> Eq for HipByt<'borrow, B> where B: Backend {}

impl<'b1, 'b2, B1, B2> PartialEq<HipByt<'b1, B1>> for HipByt<'b2, B2>
where
    B1: Backend,
    B2: Backend,
{
    #[inline]
    fn eq(&self, other: &HipByt<B1>) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<'borrow, B> PartialEq<[u8]> for HipByt<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &[u8]) -> bool {
        self.as_slice() == other
    }
}

impl<'borrow, B> PartialEq<HipByt<'borrow, B>> for [u8]
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &HipByt<B>) -> bool {
        self == other.as_slice()
    }
}

impl<'a, 'borrow, B> PartialEq<&'a [u8]> for HipByt<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &&'a [u8]) -> bool {
        self.as_slice() == *other
    }
}

impl<'a, 'borrow, B> PartialEq<HipByt<'borrow, B>> for &'a [u8]
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &HipByt<B>) -> bool {
        *self == other.as_slice()
    }
}

impl<'borrow, B> PartialEq<Vec<u8>> for HipByt<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &Vec<u8>) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<'borrow, B> PartialEq<HipByt<'borrow, B>> for Vec<u8>
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &HipByt<B>) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<'borrow, B> PartialEq<Box<[u8]>> for HipByt<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &Box<[u8]>) -> bool {
        self.as_slice() == other.as_ref()
    }
}

impl<'borrow, B> PartialEq<HipByt<'borrow, B>> for Box<[u8]>
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &HipByt<B>) -> bool {
        self.as_ref() == other.as_slice()
    }
}

impl<'a, 'borrow, B> PartialEq<Cow<'a, [u8]>> for HipByt<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &Cow<'a, [u8]>) -> bool {
        self.as_slice() == other.as_ref()
    }
}

impl<'a, 'borrow, B> PartialEq<HipByt<'borrow, B>> for Cow<'a, [u8]>
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &HipByt<B>) -> bool {
        self.as_ref() == other.as_slice()
    }
}

impl<'borrow, B, const N: usize> PartialEq<[u8; N]> for HipByt<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &[u8; N]) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<'borrow, B, const N: usize> PartialEq<HipByt<'borrow, B>> for [u8; N]
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &HipByt<B>) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<'a, 'borrow, B, const N: usize> PartialEq<&'a [u8; N]> for HipByt<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &&'a [u8; N]) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<'a, 'borrow, B, const N: usize> PartialEq<HipByt<'borrow, B>> for &'a [u8; N]
where
    B: Backend,
{
    #[inline]
    fn eq(&self, other: &HipByt<B>) -> bool {
        self.as_slice() == other.as_slice()
    }
}

// Order

impl<'borrow, B> Ord for HipByt<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.as_slice().cmp(other.as_slice())
    }
}

impl<'borrow, B> PartialOrd for HipByt<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.as_slice().partial_cmp(other.as_slice())
    }
}

#[cfg(test)]
mod tests {
    use std::borrow::Cow;
    use std::cmp::Ordering;

    use crate::HipByt;

    #[test]
    fn test_eq() {
        let arr = [32; 32];
        let s: &[u8] = &arr;
        let v = Vec::from(arr);
        let b: Box<[u8]> = Box::from(arr);
        let c: Cow<[u8]> = Cow::Borrowed(&arr);
        let h = HipByt::from(arr.as_slice());

        assert_eq!(h, arr);
        assert_eq!(arr, h);

        assert_eq!(h, s);
        assert_eq!(s, h);
        assert!(<[u8] as PartialEq<HipByt>>::eq(arr.as_slice(), &h));

        assert_eq!(h, &arr);
        assert_eq!(&arr, h);

        assert_eq!(h, v);
        assert_eq!(v, h);

        assert_eq!(h, b);
        assert_eq!(b, h);

        assert_eq!(h, c);
        assert_eq!(c, h);
    }

    #[test]
    fn test_ord() {
        let h1 = HipByt::with_borrow(b"abc");
        let h2 = HipByt::from(b"abd");

        assert_eq!(h1.partial_cmp(&h1), Some(Ordering::Equal));
        assert_eq!(h1.cmp(&h1), Ordering::Equal);

        assert!(h1 < h2);
        assert_eq!(h1.cmp(&h2), Ordering::Less);
        assert_eq!(h1.partial_cmp(&h2), Some(Ordering::Less));
        assert_eq!(h2.cmp(&h1), Ordering::Greater);
        assert_eq!(h2.partial_cmp(&h1), Some(Ordering::Greater));
    }
}
