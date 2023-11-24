//! Comparison trait implementations for `HipByt`

use super::HipByt;
use crate::alloc::borrow::Cow;
use crate::alloc::boxed::Box;
use crate::alloc::vec::Vec;
use crate::macros::{symmetric_eq, symmetric_ord};
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
        let a = self.as_slice();
        let b = other.as_slice();
        core::ptr::eq(a, b) || a == b
    }
}

symmetric_eq! {
    <'borrow> <B> <> [where B: Backend] (a : [u8], b : HipByt<'borrow, B>) {
        a == b.as_slice()
    }

    <'a, 'borrow> <B> <> [where B: Backend] (a : &'a [u8], b : HipByt<'borrow, B>) {
        *a == b.as_slice()
    }

    <'borrow> <B> <> [where B: Backend] (a : Vec<u8>, b : HipByt<'borrow, B>) {
        a.as_slice() == b.as_slice()
    }

    <'borrow> <B> <> [where B: Backend] (a : Box<[u8]>, b : HipByt<'borrow, B>) {
        a.as_ref() == b.as_slice()
    }

    <'a, 'borrow> <B> <> [where B: Backend] (a : Cow<'a, [u8]>, b : HipByt<'borrow, B>) {
        a.as_ref() == b.as_slice()
    }
}
symmetric_eq! {
    <'borrow> <B> <const N: usize> [where B: Backend] (a : [u8; N], b : HipByt<'borrow, B>) {
        a == b.as_slice()
    }
    <'a, 'borrow> <B> <const N: usize> [where B: Backend] (a : &'a [u8; N], b : HipByt<'borrow, B>) {
        a.as_slice() == b.as_slice()
    }
}

// Order

impl<'borrow, B> Ord for HipByt<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.as_slice().cmp(other.as_slice())
    }
}

impl<'borrow, B> PartialOrd for HipByt<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

symmetric_ord! {
    <'borrow> <B> <> [where B: Backend] (a: [u8], b: HipByt<'borrow, B>) {
        <[u8] as PartialOrd>::partial_cmp(a, b.as_slice())
    }

    <'a, 'borrow> <B> <> [where B: Backend] (a: &'a [u8], b: HipByt<'borrow, B>) {
        <[u8] as PartialOrd>::partial_cmp(a, b.as_slice())
    }

    <'borrow> <B> <const N: usize> [where B: Backend] (a: [u8; N], b: HipByt<'borrow, B>) {
        <[u8] as PartialOrd>::partial_cmp(a, b.as_slice())
    }

    <'a, 'borrow> <B> <const N: usize> [where B: Backend] (a: &'a [u8; N], b: HipByt<'borrow, B>) {
        <[u8] as PartialOrd>::partial_cmp(*a, b.as_slice())
    }

    <'borrow> <B> <> [where B: Backend] (a: Vec<u8>, b: HipByt<'borrow, B>) {
        <[u8] as PartialOrd>::partial_cmp(a, b.as_slice())
    }
    <'a, 'borrow> <B> <> [where B: Backend] (a: Cow<'a, [u8]>, b: HipByt<'borrow, B>) {
        <[u8] as PartialOrd>::partial_cmp(a, b.as_slice())
    }
}

#[cfg(test)]
mod tests {
    use core::cmp::Ordering;

    use crate::alloc::borrow::Cow;
    use crate::alloc::boxed::Box;
    use crate::alloc::vec::Vec;
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
