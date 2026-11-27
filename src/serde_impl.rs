//! `serde` support, for every family and size.
//!
//! Deserialization reuses the deserializer's buffer when it hands one over
//! (`visit_string`, `visit_byte_buf`). The `borrow_deserialize` functions of
//! the submodules also borrow from the input when possible (e.g. with
//! `#[serde(borrow, deserialize_with = "…")]`); `Tiny*` types, which cannot
//! borrow, copy instead.

use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;
use core::marker::PhantomData;

use serde::de::{Error, SeqAccess, Unexpected, Visitor};
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use super::enc::{Bytes, Utf8};
use super::hip::Hip;
use super::repr::Repr;

// ----- strings -----

impl<'a, R: Repr<'a>> Serialize for Hip<Utf8, R> {
    #[inline]
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(self.as_inner())
    }
}

/// Visits a string; with `BORROW`, keeps borrowed input borrowed.
struct StrVisitor<R, const BORROW: bool>(PhantomData<R>);

macro_rules! str_visits {
    () => {
        fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("a string")
        }

        #[inline]
        fn visit_str<E: Error>(self, v: &str) -> Result<Self::Value, E> {
            Ok(Hip::from_inner(v))
        }

        #[inline]
        fn visit_string<E: Error>(self, v: String) -> Result<Self::Value, E> {
            Ok(Hip::from_owned(v))
        }

        fn visit_bytes<E: Error>(self, v: &[u8]) -> Result<Self::Value, E> {
            core::str::from_utf8(v)
                .map(Hip::from_inner)
                .map_err(|_| Error::invalid_value(Unexpected::Bytes(v), &self))
        }

        fn visit_byte_buf<E: Error>(self, v: Vec<u8>) -> Result<Self::Value, E> {
            String::from_utf8(v)
                .map(Hip::from_owned)
                .map_err(|e| Error::invalid_value(Unexpected::Bytes(e.as_bytes()), &self))
        }
    };
}

impl<'de, 'a, R: Repr<'a>> Visitor<'de> for StrVisitor<R, false> {
    type Value = Hip<Utf8, R>;
    str_visits!();
}

impl<'de: 'a, 'a, R: Repr<'a>> Visitor<'de> for StrVisitor<(R, &'a ()), true> {
    type Value = Hip<Utf8, R>;
    str_visits!();

    #[inline]
    fn visit_borrowed_str<E: Error>(self, v: &'de str) -> Result<Self::Value, E> {
        Ok(Hip::from_inner_borrowed(v))
    }

    fn visit_borrowed_bytes<E: Error>(self, v: &'de [u8]) -> Result<Self::Value, E> {
        core::str::from_utf8(v)
            .map(Hip::from_inner_borrowed)
            .map_err(|_| Error::invalid_value(Unexpected::Bytes(v), &self))
    }
}

impl<'de, 'a, R: Repr<'a>> Deserialize<'de> for Hip<Utf8, R> {
    #[inline]
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_str(StrVisitor::<R, false>(PhantomData))
    }
}

/// `serde` helpers for strings.
pub mod string {
    use super::*;

    /// Deserializes a string, borrowing from the input when possible.
    ///
    /// # Errors
    ///
    /// Returns the deserializer's error, or an error if the input is not a
    /// string or not UTF-8.
    #[inline]
    pub fn borrow_deserialize<'de: 'a, 'a, D, R>(deserializer: D) -> Result<Hip<Utf8, R>, D::Error>
    where
        D: Deserializer<'de>,
        R: Repr<'a>,
    {
        deserializer.deserialize_str(StrVisitor::<(R, &'a ()), true>(PhantomData))
    }
}

// ----- bytes -----

impl<'a, R: Repr<'a>> Serialize for Hip<Bytes, R> {
    #[inline]
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_bytes(self.bytes())
    }
}

/// Visits bytes; with `BORROW`, keeps borrowed input borrowed.
struct BytesVisitor<R, const BORROW: bool>(PhantomData<R>);

macro_rules! bytes_visits {
    ($de:lifetime) => {
        fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("a byte array")
        }

        #[inline]
        fn visit_bytes<E: Error>(self, v: &[u8]) -> Result<Self::Value, E> {
            Ok(Hip::from_inner(v))
        }

        #[inline]
        fn visit_byte_buf<E: Error>(self, v: Vec<u8>) -> Result<Self::Value, E> {
            Ok(Hip::from_owned(v))
        }

        #[inline]
        fn visit_str<E: Error>(self, v: &str) -> Result<Self::Value, E> {
            Ok(Hip::from_inner(v.as_bytes()))
        }

        #[inline]
        fn visit_string<E: Error>(self, v: String) -> Result<Self::Value, E> {
            Ok(Hip::from_owned(v.into_bytes()))
        }

        fn visit_seq<A: SeqAccess<$de>>(self, mut seq: A) -> Result<Self::Value, A::Error> {
            let mut bytes = Vec::with_capacity(seq.size_hint().unwrap_or(0).min(4096));
            while let Some(b) = seq.next_element()? {
                bytes.push(b);
            }
            Ok(Hip::from_owned(bytes))
        }
    };
}

impl<'de, 'a, R: Repr<'a>> Visitor<'de> for BytesVisitor<R, false> {
    type Value = Hip<Bytes, R>;
    bytes_visits!('de);
}

impl<'de: 'a, 'a, R: Repr<'a>> Visitor<'de> for BytesVisitor<(R, &'a ()), true> {
    type Value = Hip<Bytes, R>;
    bytes_visits!('de);

    #[inline]
    fn visit_borrowed_bytes<E: Error>(self, v: &'de [u8]) -> Result<Self::Value, E> {
        Ok(Hip::from_inner_borrowed(v))
    }

    #[inline]
    fn visit_borrowed_str<E: Error>(self, v: &'de str) -> Result<Self::Value, E> {
        Ok(Hip::from_inner_borrowed(v.as_bytes()))
    }
}

impl<'de, 'a, R: Repr<'a>> Deserialize<'de> for Hip<Bytes, R> {
    #[inline]
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_bytes(BytesVisitor::<R, false>(PhantomData))
    }
}

/// `serde` helpers for byte strings.
pub mod bytes {
    use super::*;

    /// Deserializes bytes, borrowing from the input when possible.
    ///
    /// # Errors
    ///
    /// Returns the deserializer's error, or an error if the input is not bytes.
    #[inline]
    pub fn borrow_deserialize<'de: 'a, 'a, D, R>(deserializer: D) -> Result<Hip<Bytes, R>, D::Error>
    where
        D: Deserializer<'de>,
        R: Repr<'a>,
    {
        deserializer.deserialize_bytes(BytesVisitor::<(R, &'a ()), true>(PhantomData))
    }
}

// ----- bstr byte strings -----

/// `bstr` byte strings serialize as bytes, like `bstr::BString` does.
#[cfg(feature = "bstr")]
impl<'a, R: Repr<'a>> Serialize for Hip<crate::enc::BStr, R> {
    #[inline]
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_bytes(self.bytes())
    }
}

#[cfg(feature = "bstr")]
impl<'de, 'a, R: Repr<'a>> Deserialize<'de> for Hip<crate::enc::BStr, R> {
    #[inline]
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Hip::<Bytes, R>::deserialize(deserializer).map(Self::from)
    }
}

// ----- C strings -----

/// C strings serialize like `CStr` (bytes without the terminator) and
/// deserialize like `CString` (rejecting interior NULs).
impl<'a, R: Repr<'a>> Serialize for Hip<crate::enc::CStr, R> {
    #[inline]
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.as_inner().serialize(serializer)
    }
}

impl<'de, 'a, R: Repr<'a>> Deserialize<'de> for Hip<crate::enc::CStr, R> {
    #[inline]
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        alloc::ffi::CString::deserialize(deserializer).map(Self::from_owned)
    }
}

// ----- OS strings and paths -----

#[cfg(feature = "std")]
mod os {
    use std::ffi::OsString;

    use super::*;
    use crate::enc;

    impl<'a, R: Repr<'a>> Serialize for Hip<enc::OsStr, R> {
        #[inline]
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            self.as_os_str().serialize(serializer)
        }
    }

    impl<'de, 'a, R: Repr<'a>> Deserialize<'de> for Hip<enc::OsStr, R> {
        #[inline]
        fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
            OsString::deserialize(deserializer).map(Self::from_owned)
        }
    }

    /// Paths go through strings, as `std::path::Path`'s own impls do.
    impl<'a, R: Repr<'a>> Serialize for Hip<enc::Path, R> {
        #[inline]
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            self.as_path().serialize(serializer)
        }
    }

    impl<'de, 'a, R: Repr<'a>> Deserialize<'de> for Hip<enc::Path, R> {
        #[inline]
        fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
            Hip::<Utf8, R>::deserialize(deserializer).map(Self::from)
        }
    }
}

/// `serde` helpers for paths.
#[cfg(feature = "std")]
pub mod path {
    use super::*;
    use crate::enc;

    /// Deserializes a path, borrowing from the input when possible.
    ///
    /// # Errors
    ///
    /// Returns the deserializer's error, or an error if the input is not a
    /// UTF-8 string.
    #[inline]
    pub fn borrow_deserialize<'de: 'a, 'a, D, R>(
        deserializer: D,
    ) -> Result<Hip<enc::Path, R>, D::Error>
    where
        D: Deserializer<'de>,
        R: Repr<'a>,
    {
        super::string::borrow_deserialize(deserializer).map(Hip::from)
    }
}

// ----- inline values -----

/// Inline values serialize like the matching `Hip` types and deserialize
/// without allocating: input longer than the capacity is an error.
mod inline {
    use super::*;
    use crate::enc::{self, Encoding};
    use crate::inline::Inline;

    /// What deserialization accepts for each encoding.
    trait Check: Encoding {
        const WHAT: &'static str;

        /// Whether `bytes` (terminator excluded) are valid.
        fn valid(bytes: &[u8]) -> bool;
    }

    impl Check for Utf8 {
        const WHAT: &'static str = "a string";

        fn valid(bytes: &[u8]) -> bool {
            core::str::from_utf8(bytes).is_ok()
        }
    }

    impl Check for Bytes {
        const WHAT: &'static str = "a byte array";

        fn valid(_: &[u8]) -> bool {
            true
        }
    }

    #[cfg(feature = "bstr")]
    impl Check for enc::BStr {
        const WHAT: &'static str = "a byte array";

        fn valid(_: &[u8]) -> bool {
            true
        }
    }

    impl Check for enc::CStr {
        const WHAT: &'static str = "a byte array without NUL";

        fn valid(bytes: &[u8]) -> bool {
            !bytes.contains(&0)
        }
    }

    struct InlineVisitor<E, const N: usize>(PhantomData<E>);

    impl<E: Check, const N: usize> InlineVisitor<E, N> {
        fn build<Er: Error>(
            &self,
            bytes: &[u8],
            unexpected: Unexpected<'_>,
        ) -> Result<Inline<E, N>, Er> {
            if !E::valid(bytes) {
                return Err(Er::invalid_value(unexpected, self));
            }
            // SAFETY: checked for `E`
            unsafe { Inline::<E, N>::try_from_bytes(bytes) }
                .ok_or_else(|| Er::invalid_length(bytes.len(), self))
        }
    }

    impl<'de, E: Check, const N: usize> Visitor<'de> for InlineVisitor<E, N> {
        type Value = Inline<E, N>;

        fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(
                f,
                "{} of at most {} bytes",
                E::WHAT,
                Inline::<E, N>::capacity()
            )
        }

        fn visit_str<Er: Error>(self, v: &str) -> Result<Self::Value, Er> {
            self.build(v.as_bytes(), Unexpected::Str(v))
        }

        fn visit_bytes<Er: Error>(self, v: &[u8]) -> Result<Self::Value, Er> {
            self.build(v, Unexpected::Bytes(v))
        }

        fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<Self::Value, A::Error> {
            // `N <= 254`: a fixed buffer, no allocation
            let mut buf = [0u8; 255];
            let mut len = 0;
            while let Some(b) = seq.next_element::<u8>()? {
                if len == Inline::<E, N>::capacity() {
                    return Err(Error::invalid_length(len + 1, &self));
                }
                buf[len] = b;
                len += 1;
            }
            self.build(&buf[..len], Unexpected::Bytes(&buf[..len]))
        }
    }

    impl<const N: usize> Serialize for Inline<Utf8, N> {
        #[inline]
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            serializer.serialize_str(self.as_str())
        }
    }

    impl<'de, const N: usize> Deserialize<'de> for Inline<Utf8, N> {
        #[inline]
        fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
            deserializer.deserialize_str(InlineVisitor::<Utf8, N>(PhantomData))
        }
    }

    impl<const N: usize> Serialize for Inline<Bytes, N> {
        #[inline]
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            serializer.serialize_bytes(self.as_slice())
        }
    }

    impl<'de, const N: usize> Deserialize<'de> for Inline<Bytes, N> {
        #[inline]
        fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
            deserializer.deserialize_bytes(InlineVisitor::<Bytes, N>(PhantomData))
        }
    }

    #[cfg(feature = "bstr")]
    impl<const N: usize> Serialize for Inline<enc::BStr, N> {
        #[inline]
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            serializer.serialize_bytes(self.as_bytes())
        }
    }

    #[cfg(feature = "bstr")]
    impl<'de, const N: usize> Deserialize<'de> for Inline<enc::BStr, N> {
        #[inline]
        fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
            deserializer.deserialize_bytes(InlineVisitor::<enc::BStr, N>(PhantomData))
        }
    }

    /// Like `CStr` / `CString`: bytes without the terminator.
    impl<const N: usize> Serialize for Inline<enc::CStr, N> {
        #[inline]
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            self.as_c_str().serialize(serializer)
        }
    }

    impl<'de, const N: usize> Deserialize<'de> for Inline<enc::CStr, N> {
        #[inline]
        fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
            deserializer.deserialize_byte_buf(InlineVisitor::<enc::CStr, N>(PhantomData))
        }
    }

    #[cfg(feature = "std")]
    mod os {
        use std::ffi::OsString;
        use std::path::Path;

        use super::*;

        /// Like `OsStr` (the platform's own format).
        impl<const N: usize> Serialize for Inline<enc::OsStr, N> {
            #[inline]
            fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                self.as_os_str().serialize(serializer)
            }
        }

        /// Goes through an `OsString` (std's format is not a plain string).
        impl<'de, const N: usize> Deserialize<'de> for Inline<enc::OsStr, N> {
            fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
                let os = OsString::deserialize(deserializer)?;
                Self::try_from_inner(&os).map_err(|_| {
                    Error::invalid_length(os.len(), &"an OS string that fits the capacity")
                })
            }
        }

        /// Like `Path`: as a string.
        impl<const N: usize> Serialize for Inline<enc::Path, N> {
            #[inline]
            fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                self.as_path().serialize(serializer)
            }
        }

        impl<'de, const N: usize> Deserialize<'de> for Inline<enc::Path, N> {
            fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
                let s = Inline::<Utf8, N>::deserialize(deserializer)?;
                // same bytes, so it fits
                Ok(Self::try_from_inner(Path::new(s.as_str())).expect("same length"))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use alloc::string::ToString;

    use super::*;
    use crate::{HipByt, HipStr, SmallStr, TinyByt, TinyStr};

    const LONG: &str = "a string that is definitely longer than any inline capacity";

    #[test]
    fn round_trips() {
        let json = serde_json::to_string(LONG).unwrap();
        let s: HipStr<'_> = serde_json::from_str(&json).unwrap();
        assert_eq!(s, LONG);
        assert_eq!(serde_json::to_string(&s).unwrap(), json);
        let s: TinyStr = serde_json::from_str(&json).unwrap();
        assert_eq!(s, LONG);

        let b: TinyByt = serde_json::from_str("[1,2,3]").unwrap();
        assert_eq!(b, [1, 2, 3].as_slice());
        assert_eq!(
            serde_json::to_string(&HipByt::from(b"ab")).unwrap(),
            "[97,98]"
        );
    }

    #[test]
    fn borrowing() {
        let json = serde_json::to_string(LONG).unwrap();
        let mut de = serde_json::Deserializer::from_str(&json);
        let s: SmallStr<'_> = string::borrow_deserialize(&mut de).unwrap();
        assert!(s.is_borrowed());
        assert_eq!(s, LONG);

        let mut de = serde_json::Deserializer::from_str(&json);
        let s: TinyStr = string::borrow_deserialize(&mut de).unwrap();
        assert!(!s.is_borrowed());
        assert_eq!(s, LONG);
    }

    #[test]
    #[cfg(feature = "bstr")]
    fn bstr_byte_strings() {
        use crate::TinyBStr;
        let b = TinyBStr::from(b"\xffab".as_slice());
        let json = serde_json::to_string(&b).unwrap();
        assert_eq!(json, "[255,97,98]");
        let back: TinyBStr = serde_json::from_str(&json).unwrap();
        assert_eq!(back, b);
    }

    #[test]
    fn c_strings() {
        use crate::{SmallCStr, TinyCStr};
        let c = SmallCStr::from(c"hello");
        let json = serde_json::to_string(&c).unwrap();
        assert_eq!(json, serde_json::to_string(c"hello").unwrap());
        let back: TinyCStr = serde_json::from_str(&json).unwrap();
        assert_eq!(back, c"hello");
        assert!(serde_json::from_str::<TinyCStr>("[97,0,98]").is_err());
    }

    #[test]
    fn errors() {
        let r: Result<HipStr<'_>, _> = serde_json::from_str("[255]");
        assert!(r.unwrap_err().to_string().contains("a string"));
    }

    #[cfg(feature = "std")]
    #[test]
    fn os_and_path() {
        use crate::{HipPath, TinyOsStr};
        let p: HipPath<'_> = serde_json::from_str(r#""/usr/bin""#).unwrap();
        assert_eq!(p, std::path::Path::new("/usr/bin"));
        assert_eq!(serde_json::to_string(&p).unwrap(), r#""/usr/bin""#);
        let os = TinyOsStr::from("x");
        let back: TinyOsStr = serde_json::from_str(&serde_json::to_string(&os).unwrap()).unwrap();
        assert_eq!(back, os);
    }

    #[test]
    fn inline_values() {
        use crate::inline::{InlineByt, InlineCStr, InlineStr};

        let s = InlineStr::<8>::inline("héllo");
        let json = serde_json::to_string(&s).unwrap();
        assert_eq!(
            json,
            serde_json::to_string("héllo").unwrap(),
            "same format as str"
        );
        assert_eq!(serde_json::from_str::<InlineStr<8>>(&json).unwrap(), s);
        let e = serde_json::from_str::<InlineStr<4>>(&json)
            .unwrap_err()
            .to_string();
        assert!(e.contains("at most 4 bytes"), "{e}");

        // bytes: JSON arrays go through `visit_seq`, without allocating
        let b = InlineByt::<4>::inline(b"ab");
        let json = serde_json::to_string(&b).unwrap();
        assert_eq!(json, "[97,98]");
        assert_eq!(serde_json::from_str::<InlineByt<4>>(&json).unwrap(), b);
        assert!(serde_json::from_str::<InlineByt<4>>("[1,2,3,4,5]").is_err());
        assert_eq!(serde_json::from_str::<InlineByt<4>>("\"ab\"").unwrap(), b);

        let c = InlineCStr::<8>::inline(c"abc");
        let json = serde_json::to_string(&c).unwrap();
        assert_eq!(
            json,
            serde_json::to_string(c"abc").unwrap(),
            "same format as CStr"
        );
        assert_eq!(serde_json::from_str::<InlineCStr<8>>(&json).unwrap(), c);
        assert!(
            serde_json::from_str::<InlineCStr<8>>("[97,0,98]").is_err(),
            "NUL"
        );
        assert!(
            serde_json::from_str::<InlineCStr<3>>(&json).is_err(),
            "too long with its NUL"
        );

        assert!(
            serde_json::from_str::<InlineStr<8>>("[255]").is_err(),
            "not UTF-8"
        );
    }

    #[test]
    #[cfg(feature = "std")]
    fn inline_os_and_path() {
        use crate::inline::{InlineOsStr, InlinePath};

        let p = InlinePath::<16>::try_from_inner(std::path::Path::new("/a/b")).unwrap();
        let json = serde_json::to_string(&p).unwrap();
        assert_eq!(json, "\"/a/b\"");
        assert_eq!(serde_json::from_str::<InlinePath<16>>(&json).unwrap(), p);
        assert!(serde_json::from_str::<InlinePath<2>>(&json).is_err());

        let o = InlineOsStr::<16>::try_from_inner(std::ffi::OsStr::new("os")).unwrap();
        let json = serde_json::to_string(&o).unwrap();
        assert_eq!(
            json,
            serde_json::to_string(std::ffi::OsStr::new("os")).unwrap()
        );
        assert_eq!(serde_json::from_str::<InlineOsStr<16>>(&json).unwrap(), o);
        assert!(serde_json::from_str::<InlineOsStr<1>>(&json).is_err());
    }
}
