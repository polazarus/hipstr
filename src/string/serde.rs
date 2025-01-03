//! `serde` support for `HipStr`.
//!
//! This module provides support for serializing and deserializing `HipStr`
//! using [`serde`]. It is enabled by default when the `serde` feature is
//! enabled.
//!
//! # Examples
//!
//! ```
//! use hipstr::HipStr;
//!
//! let s = HipStr::from("hello");
//! let serialized = serde_json::to_string(&s).unwrap();
//! assert_eq!(serialized, r#""hello""#);
//!
//! let deserialized: HipStr = serde_json::from_str(&serialized).unwrap();
//! assert_eq!(deserialized, s);
//! ```
//!
//! # Notable aspects of the implementation
//!
//! During deserialization, this implementation minimizes allocations by
//! reusing the deserializer's internal buffer if possible.
//!
//! Like `String`'s serde implementation, this implementation supports
//! UTF-8 encoded byte sequence as input.

#![allow(clippy::option_if_let_else)]

use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;
use core::marker::PhantomData;

use serde::de::{Error, Unexpected, Visitor};
use serde::{de, Deserialize, Deserializer, Serialize};

use super::HipStr;
use crate::bytes::HipByt;
use crate::Backend;

const EXPECTING: &str = "a string";

impl<B> Serialize for HipStr<'_, B>
where
    B: Backend,
{
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(self.as_str())
    }
}

/// Deserializer's visitor for owned `HipStr`.
struct OwnedVisitor<'borrow, B: Backend>(PhantomData<HipStr<'borrow, B>>);

impl<'b, B: Backend> Visitor<'_> for OwnedVisitor<'b, B> {
    type Value = HipStr<'b, B>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str(EXPECTING)
    }

    #[inline]
    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: Error,
    {
        Ok(HipStr::from(v))
    }

    #[inline]
    fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
    where
        E: Error,
    {
        Ok(HipStr::from(v))
    }

    fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
    where
        E: Error,
    {
        match core::str::from_utf8(v) {
            Ok(s) => Ok(HipStr::from(s)),
            Err(_) => Err(Error::invalid_value(Unexpected::Bytes(v), &self)),
        }
    }

    fn visit_byte_buf<E>(self, v: Vec<u8>) -> Result<Self::Value, E>
    where
        E: Error,
    {
        match String::from_utf8(v) {
            Ok(s) => Ok(HipStr::from(s)),
            Err(e) => Err(Error::invalid_value(
                Unexpected::Bytes(&e.into_bytes()),
                &self,
            )),
        }
    }
}

impl<'de, B> Deserialize<'de> for HipStr<'_, B>
where
    B: Backend,
{
    #[inline]
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_str(OwnedVisitor(PhantomData))
    }
}

/// Deserializer's visitor for borrowed `HipStr`.
struct BorrowedVisitor<'de, B: Backend>(PhantomData<HipByt<'de, B>>);

impl<'de, B: Backend> Visitor<'de> for BorrowedVisitor<'de, B> {
    type Value = HipStr<'de, B>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str(EXPECTING)
    }

    fn visit_borrowed_str<E>(self, v: &'de str) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Ok(HipStr::borrowed(v))
    }

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Ok(HipStr::from(v))
    }

    fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Ok(HipStr::from(v))
    }

    fn visit_borrowed_bytes<E>(self, v: &'de [u8]) -> Result<Self::Value, E>
    where
        E: Error,
    {
        match core::str::from_utf8(v) {
            Ok(s) => Ok(HipStr::borrowed(s)),
            Err(_) => Err(Error::invalid_value(Unexpected::Bytes(v), &self)),
        }
    }

    fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
    where
        E: Error,
    {
        match core::str::from_utf8(v) {
            Ok(s) => Ok(HipStr::from(s)),
            Err(_) => Err(Error::invalid_value(Unexpected::Bytes(v), &self)),
        }
    }

    fn visit_byte_buf<E>(self, v: Vec<u8>) -> Result<Self::Value, E>
    where
        E: Error,
    {
        match String::from_utf8(v) {
            Ok(s) => Ok(HipStr::from(s)),
            Err(e) => Err(Error::invalid_value(
                Unexpected::Bytes(&e.into_bytes()),
                &self,
            )),
        }
    }
}

/// Deserializes a `HipStr` as a borrow if possible.
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// use hipstr::HipStr;
/// use serde::Deserialize;
///
/// #[derive(Deserialize)]
/// struct MyStruct<'a> {
///     #[serde(borrow, deserialize_with = "hipstr::string::serde::borrow_deserialize")]
///     field: HipStr<'a>,
/// }
///
/// # fn main() {
/// let s: MyStruct = serde_json::from_str(r#"{"field": "abc"}"#).unwrap();
/// assert!(s.field.is_borrowed());
/// # }
/// ```
///
/// # Errors
///
/// Returns a deserializer error if either the serialization is incorrect or an unexpected value is encountered.
#[inline]
pub fn borrow_deserialize<'de: 'a, 'a, D, B>(deserializer: D) -> Result<HipStr<'a, B>, D::Error>
where
    D: serde::Deserializer<'de>,
    B: Backend,
{
    deserializer.deserialize_str(BorrowedVisitor(PhantomData))
}

#[cfg(test)]
mod tests;
