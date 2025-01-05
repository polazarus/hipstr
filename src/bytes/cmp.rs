//! Comparison trait implementations for `HipByt`

use alloc::borrow::Cow;
use alloc::boxed::Box;
use alloc::vec::Vec;

use super::HipByt;
use crate::macros::{symmetric_eq, symmetric_ord};
use crate::Backend;

// Equality

impl<B> Eq for HipByt<'_, B> where B: Backend {}

impl<'b1, B1, B2> PartialEq<HipByt<'b1, B1>> for HipByt<'_, B2>
where
    B1: Backend,
    B2: Backend,
{
    #[inline]
    fn eq(&self, other: &HipByt<'b1, B1>) -> bool {
        self.inherent_eq(other)
    }
}

#[inline]
pub(super) fn eq_slice(a: impl AsRef<[u8]>, b: impl AsRef<[u8]>) -> bool {
    a.as_ref() == b.as_ref()
}

symmetric_eq! {
    [B] [where B: Backend] ([u8], HipByt<'_, B>) = eq_slice;
    [B] [where B: Backend] (&[u8], HipByt<'_, B>) = eq_slice;

    [B, const N: usize] [where B: Backend] ([u8; N], HipByt<'_, B>) = eq_slice;
    [B, const N: usize] [where B: Backend] (&[u8; N], HipByt<'_, B>) = eq_slice;

    [B] [where B: Backend] (Vec<u8>, HipByt<'_, B>) = eq_slice;
    [B] [where B: Backend] (&Vec<u8>, HipByt<'_, B>) = eq_slice;

    [B] [where B: Backend] (Box<[u8]>, HipByt<'_, B>) = eq_slice;
    [B] [where B: Backend] (&Box<[u8]>, HipByt<'_, B>) = eq_slice;

    [B] [where B: Backend] (Cow<'_, [u8]>, HipByt<'_, B>) = eq_slice;
    [B] [where B: Backend] (&Cow<'_, [u8]>, HipByt<'_, B>) = eq_slice;

}

// Order

impl<B> Ord for HipByt<'_, B>
where
    B: Backend,
{
    #[inline]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.as_slice().cmp(other.as_slice())
    }
}

impl<B> PartialOrd for HipByt<'_, B>
where
    B: Backend,
{
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[inline]
pub(super) fn cmp_slice(a: impl AsRef<[u8]>, b: impl AsRef<[u8]>) -> Option<core::cmp::Ordering> {
    a.as_ref().partial_cmp(b.as_ref())
}

symmetric_ord! {
    [B] [where B: Backend] ([u8], HipByt<'_, B>) = cmp_slice;
    [B] [where B: Backend] (&[u8], HipByt<'_, B>) = cmp_slice;

    [B, const N: usize] [where B: Backend] ([u8; N], HipByt<'_, B>) = cmp_slice;
    [B, const N: usize] [where B: Backend] (&[u8; N], HipByt<'_, B>) = cmp_slice;

    [B] [where B: Backend] (Vec<u8>, HipByt<'_, B>) = cmp_slice;
    [B] [where B: Backend] (&Vec<u8>, HipByt<'_, B>) = cmp_slice;

    [B] [where B: Backend] (Box<[u8]>, HipByt<'_, B>) = cmp_slice;
    [B] [where B: Backend] (&Box<[u8]>, HipByt<'_, B>) = cmp_slice;

    [B] [where B: Backend] (Cow<'_, [u8]>, HipByt<'_, B>) = cmp_slice;
    [B] [where B: Backend] (&Cow<'_, [u8]>, HipByt<'_, B>) = cmp_slice;
}

#[cfg(test)]
mod tests {
    use alloc::borrow::Cow;
    use alloc::boxed::Box;
    use alloc::vec::Vec;
    use core::cmp::Ordering;

    use crate::HipByt;

    #[test]
    fn test_eq() {
        let arr = [32; 32];
        let s: &[u8] = &arr;
        let v = Vec::from(arr);
        let b: Box<[u8]> = Box::from(arr);
        let c: Cow<[u8]> = Cow::Borrowed(&arr);
        let h = HipByt::from(arr.as_slice());
        let h2 = HipByt::borrowed(arr.as_slice());

        assert_eq!(h, h);
        assert_eq!(h, h2);
        assert_ne!(h2, h2.slice(0..4));

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
        let h1 = HipByt::borrowed(b"abc");
        let h2 = HipByt::from(b"abd");

        assert_eq!(h1.partial_cmp(&h1), Some(Ordering::Equal));
        assert_eq!(h1.cmp(&h1), Ordering::Equal);

        assert!(h1 < h2);
        assert_eq!(h1.cmp(&h2), Ordering::Less);
        assert_eq!(h1.partial_cmp(&h2), Some(Ordering::Less));
        assert_eq!(h2.cmp(&h1), Ordering::Greater);
        assert_eq!(h2.partial_cmp(&h1), Some(Ordering::Greater));
    }

    static H: HipByt = HipByt::from_static(b"abc");

    #[test]
    fn test_ord_other() {
        assert_eq!(H.partial_cmp(b"abc".as_slice()), Some(Ordering::Equal));
        assert_eq!(H.partial_cmp(b"abc"), Some(Ordering::Equal));
        assert!(H < b"abd");
        assert!(&H < b"abd");
        assert!(H < b"abd".as_slice());
        assert!(&H < b"abd".as_slice());
        assert!(H < Vec::from(b"abd"));
        assert!(H < Cow::Borrowed(b"abd".as_slice()));
    }
}
