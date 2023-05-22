//! Comparison trait implementations for `HipByt`

use std::borrow::Cow;

use super::HipByt;
use crate::AllocatedBackend;

// Equality

impl<B> Eq for HipByt<B> where B: AllocatedBackend {}

impl<B1, B2> PartialEq<HipByt<B1>> for HipByt<B2>
where
    B1: AllocatedBackend,
    B2: AllocatedBackend,
{
    #[inline]
    fn eq(&self, other: &HipByt<B1>) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<B> PartialEq<[u8]> for HipByt<B>
where
    B: AllocatedBackend,
{
    #[inline]
    fn eq(&self, other: &[u8]) -> bool {
        self.as_slice() == other
    }
}

impl<B> PartialEq<HipByt<B>> for [u8]
where
    B: AllocatedBackend,
{
    #[inline]
    fn eq(&self, other: &HipByt<B>) -> bool {
        self == other.as_slice()
    }
}

impl<'a, B> PartialEq<&'a [u8]> for HipByt<B>
where
    B: AllocatedBackend,
{
    #[inline]
    fn eq(&self, other: &&'a [u8]) -> bool {
        self.as_slice() == *other
    }
}

impl<'a, B> PartialEq<HipByt<B>> for &'a [u8]
where
    B: AllocatedBackend,
{
    #[inline]
    fn eq(&self, other: &HipByt<B>) -> bool {
        *self == other.as_slice()
    }
}

impl<B> PartialEq<Vec<u8>> for HipByt<B>
where
    B: AllocatedBackend,
{
    #[inline]
    fn eq(&self, other: &Vec<u8>) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<B> PartialEq<HipByt<B>> for Vec<u8>
where
    B: AllocatedBackend,
{
    #[inline]
    fn eq(&self, other: &HipByt<B>) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<B> PartialEq<Box<[u8]>> for HipByt<B>
where
    B: AllocatedBackend,
{
    #[inline]
    fn eq(&self, other: &Box<[u8]>) -> bool {
        self.as_slice() == other.as_ref()
    }
}

impl<B> PartialEq<HipByt<B>> for Box<[u8]>
where
    B: AllocatedBackend,
{
    #[inline]
    fn eq(&self, other: &HipByt<B>) -> bool {
        self.as_ref() == other.as_slice()
    }
}

impl<'a, B> PartialEq<Cow<'a, [u8]>> for HipByt<B>
where
    B: AllocatedBackend,
{
    #[inline]
    fn eq(&self, other: &Cow<'a, [u8]>) -> bool {
        self.as_slice() == other.as_ref()
    }
}

impl<'a, B> PartialEq<HipByt<B>> for Cow<'a, [u8]>
where
    B: AllocatedBackend,
{
    #[inline]
    fn eq(&self, other: &HipByt<B>) -> bool {
        self.as_ref() == other.as_slice()
    }
}

impl<B, const N: usize> PartialEq<[u8; N]> for HipByt<B>
where
    B: AllocatedBackend,
{
    #[inline]
    fn eq(&self, other: &[u8; N]) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<B, const N: usize> PartialEq<HipByt<B>> for [u8; N]
where
    B: AllocatedBackend,
{
    #[inline]
    fn eq(&self, other: &HipByt<B>) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<'a, B, const N: usize> PartialEq<&'a [u8; N]> for HipByt<B>
where
    B: AllocatedBackend,
{
    #[inline]
    fn eq(&self, other: &&'a [u8; N]) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<'a, B, const N: usize> PartialEq<HipByt<B>> for &'a [u8; N]
where
    B: AllocatedBackend,
{
    #[inline]
    fn eq(&self, other: &HipByt<B>) -> bool {
        self.as_slice() == other.as_slice()
    }
}

// Order

impl<B> Ord for HipByt<B>
where
    B: AllocatedBackend,
{
    #[inline]
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.as_slice().cmp(other.as_slice())
    }
}

impl<B> PartialOrd for HipByt<B>
where
    B: AllocatedBackend,
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
        let h1 = HipByt::from_static(b"abc");
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
