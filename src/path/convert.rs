//! Conversion trait implementations for `HipPath`.

use core::borrow::Borrow;
use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};

use super::HipPath;
use crate::alloc::borrow::Cow;
use crate::alloc::boxed::Box;
use crate::alloc::string::String;
use crate::os_string::HipOsStr;
use crate::string::HipStr;
use crate::Backend;

// AsRef

impl<'borrow, B> AsRef<Path> for HipPath<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn as_ref(&self) -> &Path {
        self.as_path()
    }
}

impl<'borrow, B> AsRef<OsStr> for HipPath<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn as_ref(&self) -> &OsStr {
        self.as_os_str()
    }
}

// Borrow

impl<'borrow, B> Borrow<Path> for HipPath<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn borrow(&self) -> &Path {
        self.as_path()
    }
}

impl<'borrow, B> Borrow<OsStr> for HipPath<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn borrow(&self) -> &OsStr {
        self.as_os_str()
    }
}

// Infallible conversions
// From

impl<'borrow, B> From<&Path> for HipPath<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: &Path) -> Self {
        Self(HipOsStr::from(value.as_os_str()))
    }
}

impl<'borrow, B> From<&str> for HipPath<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: &str) -> Self {
        Self(HipOsStr::from(value))
    }
}

impl<'borrow, B> From<&OsStr> for HipPath<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: &OsStr) -> Self {
        Self(HipOsStr::from(value))
    }
}

impl<'borrow, B> From<Box<str>> for HipPath<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: Box<str>) -> Self {
        Self(HipOsStr::from(value.into_string()))
    }
}

impl<'borrow, B> From<String> for HipPath<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: String) -> Self {
        Self(HipOsStr::from(value))
    }
}

impl<'borrow, B> From<OsString> for HipPath<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: OsString) -> Self {
        Self(HipOsStr::from(value))
    }
}

impl<'borrow, B> From<PathBuf> for HipPath<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: PathBuf) -> Self {
        Self(HipOsStr::from(value.into_os_string()))
    }
}

impl<'borrow, B> From<Cow<'borrow, str>> for HipPath<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: Cow<'borrow, str>) -> Self {
        match value {
            Cow::Borrowed(borrow) => Self::borrowed(borrow),
            Cow::Owned(owned) => Self::from(owned),
        }
    }
}

impl<'borrow, B> From<Cow<'borrow, OsStr>> for HipPath<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: Cow<'borrow, OsStr>) -> Self {
        match value {
            Cow::Borrowed(borrow) => Self::borrowed(borrow),
            Cow::Owned(owned) => Self::from(owned),
        }
    }
}

impl<'borrow, B> From<Cow<'borrow, Path>> for HipPath<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: Cow<'borrow, Path>) -> Self {
        match value {
            Cow::Borrowed(borrow) => Self::borrowed(borrow),
            Cow::Owned(owned) => Self::from(owned),
        }
    }
}

impl<'borrow, B> From<HipOsStr<'borrow, B>> for HipPath<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: HipOsStr<'borrow, B>) -> Self {
        Self(value)
    }
}

impl<'borrow, B> From<HipStr<'borrow, B>> for HipPath<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: HipStr<'borrow, B>) -> Self {
        Self(HipOsStr::from(value))
    }
}

impl<'borrow, B> From<&HipOsStr<'borrow, B>> for HipPath<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: &HipOsStr<'borrow, B>) -> Self {
        Self::from(value.clone())
    }
}

impl<'borrow, B> From<&HipStr<'borrow, B>> for HipPath<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: &HipStr<'borrow, B>) -> Self {
        Self::from(value.clone())
    }
}

// Into

impl<'borrow, B> From<HipPath<'borrow, B>> for PathBuf
where
    B: Backend,
{
    #[inline]
    fn from(value: HipPath<B>) -> Self {
        value
            .into_path_buf()
            .unwrap_or_else(|value| value.as_path().to_path_buf())
    }
}

impl<'borrow, B> From<HipPath<'borrow, B>> for OsString
where
    B: Backend,
{
    #[inline]
    fn from(value: HipPath<B>) -> Self {
        value
            .into_os_string()
            .unwrap_or_else(|value| value.as_os_str().to_os_string())
    }
}

impl<'borrow, B> From<HipPath<'borrow, B>> for HipOsStr<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: HipPath<'borrow, B>) -> Self {
        value.into_os_str()
    }
}

impl<'borrow, B> From<&HipPath<'borrow, B>> for HipOsStr<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn from(value: &HipPath<'borrow, B>) -> Self {
        Self::from(value.clone())
    }
}

impl<'borrow, B> From<HipPath<'borrow, B>> for Cow<'borrow, Path>
where
    B: Backend,
{
    #[inline]
    fn from(value: HipPath<'borrow, B>) -> Self {
        value
            .into_borrowed()
            .map_or_else(|value| Cow::Owned(value.into()), Cow::Borrowed)
    }
}

// Fallible conversions

//?

#[cfg(test)]
mod tests {
    use core::borrow::Borrow;
    use core::ptr;
    use std::ffi::{OsStr, OsString};
    use std::path::{Path, PathBuf};

    use crate::alloc::borrow::Cow;
    use crate::alloc::boxed::Box;
    use crate::alloc::string::String;
    use crate::{HipOsStr, HipPath, HipStr};

    #[test]
    fn test_as_ref() {
        let a = HipPath::from("abc");

        let p: &Path = a.as_ref();
        assert!(ptr::eq(a.as_path(), p));

        let o: &OsStr = a.as_ref();
        assert!(ptr::eq(a.as_os_str(), o));
    }

    #[test]
    fn test_borrow() {
        let a = HipPath::from("abc");

        let p: &Path = a.borrow();
        assert!(ptr::eq(a.as_path(), p));

        let o: &OsStr = a.borrow();
        assert!(ptr::eq(a.as_os_str(), o));
    }

    #[test]
    fn test_from() {
        let slice = "abcdefghijklmnopqrstuvwxyz";
        let os_slice = OsStr::new(slice);
        let path = Path::new(slice);
        let string = String::from(slice);
        let ptr_string = string.as_ptr();
        let os_string = OsString::from(slice);
        let ptr_os_string = os_string.as_encoded_bytes().as_ptr();
        let path_buf = PathBuf::from(slice);
        let ptr_path_buf = path_buf.as_os_str().as_encoded_bytes().as_ptr();
        let b: Box<str> = slice.into();
        let ptr_b = b.as_ptr();

        let cow_str1: Cow<str> = Cow::Borrowed(slice);
        let cow_str2: Cow<str> = String::from(slice).into();
        let ptr_cow_str2 = cow_str2.as_ptr();

        let cow_os_str1: Cow<OsStr> = Cow::Borrowed(os_slice);
        let cow_os_str2: Cow<OsStr> = OsString::from(os_slice).into();
        let ptr_cow_os_str2 = cow_os_str2.as_encoded_bytes().as_ptr();

        let cow_path1: Cow<Path> = Cow::Borrowed(path);
        let cow_path2: Cow<Path> = PathBuf::from(path).into();
        let ptr_cow_path2 = cow_path2.as_os_str().as_encoded_bytes().as_ptr();

        let h_string = HipStr::from(slice);
        let h_string_ptr = h_string.as_ptr();

        let h_os_string = HipOsStr::from(slice);
        let h_os_string_ptr = h_os_string.as_ptr();

        let fs = HipPath::from(slice);
        assert_eq!(fs.as_os_str(), slice);

        let fs = HipPath::from(os_slice);
        assert_eq!(fs.as_os_str(), os_slice);

        let fv = HipPath::from(string);
        assert_eq!(fv.as_os_str(), slice);
        assert!(ptr::eq(fv.0.as_ptr(), ptr_string));

        let fs = HipPath::from(os_string);
        assert_eq!(fs.as_os_str(), os_slice);
        assert_eq!(fs.as_os_str().as_encoded_bytes().as_ptr(), ptr_os_string);

        let fs = HipPath::from(path_buf);
        assert_eq!(fs.as_os_str(), os_slice);
        assert_eq!(fs.as_os_str().as_encoded_bytes().as_ptr(), ptr_path_buf);

        let fv = HipPath::from(b);
        assert_eq!(fv.as_os_str(), slice);
        assert!(ptr::eq(fv.0.as_ptr(), ptr_b));

        let fc1 = HipPath::from(cow_str1);
        assert_eq!(fc1.as_os_str(), slice);

        let fc2 = HipPath::from(cow_str2);
        assert_eq!(fc2.as_os_str(), slice);
        assert!(ptr::eq(fc2.0.as_ptr(), ptr_cow_str2));

        let fc1 = HipPath::from(cow_os_str1);
        assert_eq!(fc1.as_os_str(), os_slice);

        let fc2 = HipPath::from(cow_os_str2);
        assert_eq!(fc2.as_os_str(), os_slice);
        assert!(ptr::eq(fc2.0.as_ptr(), ptr_cow_os_str2));

        let fc1 = HipPath::from(cow_path1);
        assert_eq!(fc1.as_os_str(), os_slice);

        let fc2 = HipPath::from(cow_path2);
        assert_eq!(fc2.as_os_str(), os_slice);
        assert!(ptr::eq(fc2.0.as_ptr(), ptr_cow_path2));

        let fhs = HipPath::from(&h_string);
        assert_eq!(fhs.as_os_str(), slice);
        assert!(ptr::eq(fhs.0.as_ptr(), h_string_ptr));

        let fhs = HipPath::from(h_string);
        assert_eq!(fhs.as_os_str(), slice);
        assert!(ptr::eq(fhs.0.as_ptr(), h_string_ptr));

        let fhs = HipPath::from(&h_os_string);
        assert_eq!(fhs.as_os_str(), slice);
        assert!(ptr::eq(fhs.0.as_ptr(), h_os_string_ptr));

        let fho = HipPath::from(h_os_string);
        assert_eq!(fho.as_os_str(), slice);
        assert!(ptr::eq(fho.0.as_ptr(), h_os_string_ptr));
    }

    #[test]
    fn test_into_path_buf() {
        let v = "a".repeat(42); // string's length > inline capacity
        let p = v.as_ptr();
        let a = HipPath::from(v);
        let v: PathBuf = a.into();
        assert_eq!(v.as_os_str().as_encoded_bytes().as_ptr(), p);

        let a = HipPath::from("abc");
        let v: PathBuf = a.into();
        assert_eq!(v, Path::new("abc"));

        let a = HipPath::borrowed("abc");
        let v: PathBuf = a.into();
        assert_eq!(v, Path::new("abc"));
    }

    #[test]
    fn test_into_cow() {
        let h = HipPath::from_static("abc");
        let c: Cow<'static, Path> = h.into();
        assert_eq!(c, Cow::Borrowed(Path::new("abc")));

        let h = HipPath::from("abc");
        let c: Cow<'static, Path> = h.into();
        assert_eq!(c, Cow::<'static, Path>::Owned("abc".into()));
    }

    #[test]
    fn test_into_os_string() {
        let v = "a".repeat(42); // string's length > inline capacity
        let p = v.as_ptr();
        let a = HipPath::from(v);
        let v: OsString = a.into();
        assert_eq!(v.as_encoded_bytes().as_ptr(), p);

        let a = HipPath::from("abc");
        let v: OsString = a.into();
        assert_eq!(v, "abc");

        let a = HipPath::borrowed("abc");
        let v: OsString = a.into();
        assert_eq!(v, "abc");
    }

    #[test]
    fn test_into_hip_os_str() {
        let v = "a".repeat(42); // string's length > inline capacity
        let p = v.as_ptr();
        let hs = HipPath::from(v);

        let hb = HipOsStr::from(&hs);
        assert_eq!(hb.as_encoded_bytes(), b"a".repeat(42));
        assert_eq!(hb.as_ptr(), p);

        let hb: HipOsStr = hs.into();
        assert_eq!(hb.as_encoded_bytes(), b"a".repeat(42));
        assert_eq!(hb.as_ptr(), p);

        let a = HipPath::from("abc");
        let v: HipOsStr = a.into();
        assert_eq!(v.as_encoded_bytes(), b"abc");

        let a = HipPath::borrowed("abc");
        let v: HipOsStr = a.into();
        assert_eq!(v.as_encoded_bytes(), b"abc");
    }

    // #[test]
    // fn test_try_from() {
    //     let slice: &[u8] = b"abcdefghijklmnopqrstuvwxyz";

    //     let hb = HipByt::borrowed(slice);
    //     let hs: HipPath = hb.try_into().unwrap();
    //     assert_eq!(hs, "abcdefghijklmnopqrstuvwxyz");
    //     assert!(hs.is_borrowed());

    //     let hb = HipByt::from(slice);
    //     let hs: HipPath = hb.try_into().unwrap();
    //     assert_eq!(hs, "abcdefghijklmnopqrstuvwxyz");

    //     let hb = HipByt::borrowed(slice);
    //     let hs: HipPath = (&hb).try_into().unwrap();
    //     assert_eq!(hs, "abcdefghijklmnopqrstuvwxyz");

    //     let hs: HipPath = slice.try_into().unwrap();
    //     assert_eq!(hs, "abcdefghijklmnopqrstuvwxyz");

    //     let v = b"a".repeat(42);
    //     let p = v.as_ptr();
    //     let hs: HipPath = v.try_into().unwrap();
    //     assert_eq!(hs, "a".repeat(42));
    //     assert_eq!(hs.as_ptr(), p);
    // }

    // #[test]
    // fn test_try_from_err() {
    //     let slice: &[u8] = b"abc\x80";
    //     let hb = HipByt::borrowed(slice);
    //     assert!(HipPath::try_from(slice).is_err());
    //     assert!(HipPath::try_from(slice.to_vec()).is_err());
    //     assert!(HipPath::try_from(&hb).is_err());
    //     assert!(HipPath::try_from(hb).is_err());
    // }
}
