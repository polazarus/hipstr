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

impl<'a, R: Repr<'a, u8>> Serialize for Hip<Utf8, R> {
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

impl<'de, 'a, R: Repr<'a, u8>> Visitor<'de> for StrVisitor<R, false> {
    type Value = Hip<Utf8, R>;
    str_visits!();
}

impl<'de: 'a, 'a, R: Repr<'a, u8>> Visitor<'de> for StrVisitor<(R, &'a ()), true> {
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

impl<'de, 'a, R: Repr<'a, u8>> Deserialize<'de> for Hip<Utf8, R> {
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
        R: Repr<'a, u8>,
    {
        deserializer.deserialize_str(StrVisitor::<(R, &'a ()), true>(PhantomData))
    }
}

// ----- bytes -----

impl<'a, R: Repr<'a, u8>> Serialize for Hip<Bytes, R> {
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

impl<'de, 'a, R: Repr<'a, u8>> Visitor<'de> for BytesVisitor<R, false> {
    type Value = Hip<Bytes, R>;
    bytes_visits!('de);
}

impl<'de: 'a, 'a, R: Repr<'a, u8>> Visitor<'de> for BytesVisitor<(R, &'a ()), true> {
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

impl<'de, 'a, R: Repr<'a, u8>> Deserialize<'de> for Hip<Bytes, R> {
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
        R: Repr<'a, u8>,
    {
        deserializer.deserialize_bytes(BytesVisitor::<(R, &'a ()), true>(PhantomData))
    }
}

// ----- bstr byte strings -----

/// `bstr` byte strings serialize as bytes, like `bstr::BString` does.
#[cfg(feature = "bstr")]
impl<'a, R: Repr<'a, u8>> Serialize for Hip<crate::enc::BStr, R> {
    #[inline]
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_bytes(self.bytes())
    }
}

#[cfg(feature = "bstr")]
impl<'de, 'a, R: Repr<'a, u8>> Deserialize<'de> for Hip<crate::enc::BStr, R> {
    #[inline]
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Hip::<Bytes, R>::deserialize(deserializer).map(Self::from)
    }
}

// ----- C strings -----

/// C strings serialize like `CStr` (bytes without the terminator) and
/// deserialize like `CString` (rejecting interior NULs).
impl<'a, R: Repr<'a, u8>> Serialize for Hip<crate::enc::CStr, R> {
    #[inline]
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.as_inner().serialize(serializer)
    }
}

impl<'de, 'a, R: Repr<'a, u8>> Deserialize<'de> for Hip<crate::enc::CStr, R> {
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

    impl<'a, R: Repr<'a, u8>> Serialize for Hip<enc::OsStr, R> {
        #[inline]
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            self.as_os_str().serialize(serializer)
        }
    }

    impl<'de, 'a, R: Repr<'a, u8>> Deserialize<'de> for Hip<enc::OsStr, R> {
        #[inline]
        fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
            OsString::deserialize(deserializer).map(Self::from_owned)
        }
    }

    /// Paths go through strings, as `std::path::Path`'s own impls do.
    impl<'a, R: Repr<'a, u8>> Serialize for Hip<enc::Path, R> {
        #[inline]
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            self.as_path().serialize(serializer)
        }
    }

    impl<'de, 'a, R: Repr<'a, u8>> Deserialize<'de> for Hip<enc::Path, R> {
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
        R: Repr<'a, u8>,
    {
        super::string::borrow_deserialize(deserializer).map(Hip::from)
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
}
