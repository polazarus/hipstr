use alloc::borrow::Cow;
use core::borrow::Borrow;

use bstr::{BStr, BString};

use super::HipByt;
use crate::Backend;

impl<B> Borrow<BStr> for HipByt<'_, B>
where
    B: Backend,
{
    #[inline]
    fn borrow(&self) -> &BStr {
        BStr::new(self.as_slice())
    }
}

impl<B> AsRef<BStr> for HipByt<'_, B>
where
    B: Backend,
{
    #[inline]
    fn as_ref(&self) -> &BStr {
        BStr::new(self.as_slice())
    }
}

impl<'borrow, B> From<&'borrow BStr> for HipByt<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: &'borrow BStr) -> Self {
        HipByt::borrowed(value.as_ref())
    }
}

impl<B> From<BString> for HipByt<'_, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: BString) -> Self {
        HipByt::from(Vec::from(value))
    }
}

impl<'borrow, B> From<Cow<'borrow, BStr>> for HipByt<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: Cow<'borrow, BStr>) -> Self {
        match value {
            Cow::Borrowed(b) => Self::from(b),
            Cow::Owned(o) => Self::from(o),
        }
    }
}

impl<B> From<HipByt<'_, B>> for BString
where
    B: Backend,
{
    #[inline]
    fn from(value: HipByt<'_, B>) -> Self {
        value
            .into_vec()
            .map_or_else(|h| Self::from(h.as_slice()), Self::from)
    }
}

#[cfg(test)]
mod tests {
    use bstr::{ByteSlice, ByteVec};

    use super::*;
    use crate::HipByt;

    #[test]
    fn test_borrow_bstr() {
        let b = HipByt::from(b"Hello, World!");
        let s: &BStr = b.borrow();
        assert_eq!(s, "Hello, World!");
        assert!(s.contains_str("World"));
    }

    #[test]
    fn test_as_ref_bstr() {
        let b = HipByt::from(b"Hello, World!");
        let s: &BStr = b.as_ref();
        assert_eq!(s, "Hello, World!");
        assert!(s.contains_str("World"));
    }

    #[test]
    fn test_from_bstr() {
        let b = HipByt::from(BStr::new("Hello, World!"));
        assert_eq!(&*b, "Hello, World!");
    }

    #[test]
    fn test_from_bstring() {
        let b = HipByt::from(BString::from("Hello, World!"));
        assert_eq!(&*b, "Hello, World!");
    }

    #[test]
    fn test_from_cow() {
        let b = HipByt::from(Cow::Borrowed(BStr::new(b"Hello, World!")));
        assert_eq!(&*b, "Hello, World!");
        let b: HipByt = HipByt::from(Cow::<BStr>::Owned(BString::from(b"Hello, World!")));
        assert_eq!(&*b, "Hello, World!");
    }

    #[test]
    fn test_into_bstring() {
        let b: HipByt<'static> = HipByt::from(b"Hello, World!");
        let bstring: BString = b.into();
        assert_eq!(bstring, "Hello, World!");
    }

    #[test]
    fn test_mutate() {
        let mut b = HipByt::from(b"Hello, World!");
        {
            let mut m = b.mutate();
            let r: &mut BString = &mut m;
            r.push_char('!');
            assert_eq!(r, "Hello, World!!");
        }
        assert_eq!(b, b"Hello, World!!");
    }
}
