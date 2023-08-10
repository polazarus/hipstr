//! Conversion trait implementations for `HipByt`.

use std::borrow::Cow;

use super::HipByt;
use crate::raw::Raw;
use crate::Backend;

impl<'borrow, B> AsRef<[u8]> for HipByt<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_slice()
    }
}

// Infallible conversions

impl<'borrow, B> From<&[u8]> for HipByt<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: &[u8]) -> Self {
        Self(Raw::from_slice(value))
    }
}

impl<'borrow, B, const N: usize> From<&[u8; N]> for HipByt<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: &[u8; N]) -> Self {
        Self(Raw::from_slice(value))
    }
}

impl<'borrow, B> From<Box<[u8]>> for HipByt<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: Box<[u8]>) -> Self {
        Self(Raw::from_vec(value.into_vec()))
    }
}

impl<'borrow, B> From<Vec<u8>> for HipByt<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: Vec<u8>) -> Self {
        Self(Raw::from_vec(value))
    }
}

impl<'borrow, B> From<Cow<'borrow, [u8]>> for HipByt<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: Cow<'borrow, [u8]>) -> Self {
        match value {
            Cow::Borrowed(borrow) => Self::borrowed(borrow),
            Cow::Owned(owned) => Self::from(owned),
        }
    }
}

impl<'borrow, B> From<HipByt<'borrow, B>> for Vec<u8>
where
    B: Backend,
{
    #[inline]
    fn from(value: HipByt<B>) -> Self {
        value
            .into_vec()
            .unwrap_or_else(|err| err.as_slice().to_vec())
    }
}

// Fallible conversions

// => none for now

#[cfg(test)]
mod tests {
    use std::borrow::Cow;

    use crate::{HipByt, ThreadSafe};

    #[test]
    fn test_as_ref() {
        let a = HipByt::from(b"abc");
        assert!(std::ptr::eq(a.as_slice(), a.as_ref()));
    }

    #[test]
    fn test_from() {
        let a = [32; 32];
        let v = Vec::from(a);
        let ptr_v = v.as_ptr();
        let b: Box<[u8]> = a.into();
        let ptr_b = b.as_ptr();
        let c1: Cow<[u8]> = a.as_slice().into();
        let c2: Cow<[u8]> = Vec::from(a).into();
        let ptr_c2 = c2.as_ptr();

        let fa = HipByt::from(&a);
        assert_eq!(fa.as_slice(), &a);

        let fs = HipByt::from(a.as_slice());
        assert_eq!(fs.as_slice(), &a);

        let fv = HipByt::from(v);
        assert_eq!(fv.as_slice(), &a);
        assert!(std::ptr::eq(fv.as_ptr(), ptr_v));

        let fv = HipByt::from(b);
        assert_eq!(fv.as_slice(), &a);
        assert!(std::ptr::eq(fv.as_ptr(), ptr_b));

        type H<'a> = crate::bytes::HipByt<'a, ThreadSafe>;
        let fc1 = H::from(c1);
        assert_eq!(fc1.as_slice(), &a);

        let fc2 = H::from(c2);
        assert_eq!(fc2.as_slice(), &a);
        assert!(std::ptr::eq(fc2.as_ptr(), ptr_c2));
    }

    #[test]
    fn test_into() {
        let v = vec![1, 2, 3];
        let p = v.as_ptr();
        let a = HipByt::from(v);
        let v: Vec<_> = a.into();
        assert_eq!(v.as_ptr(), p);

        let arr = [1, 2, 3];
        let a = HipByt::from(&arr);
        let v: Vec<_> = a.into();
        assert_eq!(v.as_slice(), &arr);
    }
}
