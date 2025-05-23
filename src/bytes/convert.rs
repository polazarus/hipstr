//! Conversion trait implementations for `HipByt`.

use alloc::borrow::Cow;
use alloc::boxed::Box;
use alloc::vec::Vec;

use super::HipByt;
use crate::backend::Backend;

impl<B> AsRef<[u8]> for HipByt<'_, B>
where
    B: Backend,
{
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_slice()
    }
}

// Infallible conversions

impl<B> From<&[u8]> for HipByt<'_, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: &[u8]) -> Self {
        Self::from_slice(value)
    }
}

impl<B, const N: usize> From<&[u8; N]> for HipByt<'_, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: &[u8; N]) -> Self {
        Self::from_slice(value)
    }
}

impl<B> From<Box<[u8]>> for HipByt<'_, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: Box<[u8]>) -> Self {
        Self::normalized_from_vec(value.into_vec())
    }
}

impl<B> From<Vec<u8>> for HipByt<'_, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: Vec<u8>) -> Self {
        Self::normalized_from_vec(value)
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

impl<B> From<HipByt<'_, B>> for Vec<u8>
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

impl<'borrow, B> From<HipByt<'borrow, B>> for Cow<'borrow, [u8]>
where
    B: Backend,
{
    #[inline]
    fn from(value: HipByt<'borrow, B>) -> Self {
        value
            .into_borrowed()
            .map_or_else(|value| Cow::Owned(value.into()), Cow::Borrowed)
    }
}

// Fallible conversions

// => none for now

#[cfg(test)]
mod tests {
    use alloc::borrow::Cow;
    use alloc::vec;
    use core::ptr;

    use super::*;
    use crate::{Arc, HipByt};

    #[test]
    fn test_as_ref() {
        let a = HipByt::from(b"abc");
        assert!(ptr::eq(a.as_slice(), a.as_ref()));
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
        assert!(ptr::eq(fv.as_ptr(), ptr_v));

        let fv = HipByt::from(b);
        assert_eq!(fv.as_slice(), &a);
        assert!(ptr::eq(fv.as_ptr(), ptr_b));

        type H<'a> = crate::bytes::HipByt<'a, Arc>;
        let fc1 = H::from(c1);
        assert_eq!(fc1.as_slice(), &a);

        let fc2 = H::from(c2);
        assert_eq!(fc2.as_slice(), &a);
        assert!(ptr::eq(fc2.as_ptr(), ptr_c2));
    }

    #[test]
    fn test_into() {
        let v = vec![42; 42];
        let p = v.as_ptr();
        let a = HipByt::from(v);
        let v: Vec<_> = a.into();
        assert_eq!(v.as_ptr(), p);

        let arr = [1, 2, 3];
        let a = HipByt::from(&arr);
        let v: Vec<_> = a.into();
        assert_eq!(v.as_slice(), &arr);
    }

    #[test]
    fn test_into_cow() {
        let h = HipByt::from_static(b"abc");
        let c: Cow<'static, [u8]> = h.into();
        assert_eq!(c, Cow::Borrowed(b"abc"));

        let h = HipByt::from(b"abc");
        let c: Cow<'static, [u8]> = h.into();
        assert_eq!(c, Cow::<'static, [u8]>::Owned(b"abc".into()));
    }
}
