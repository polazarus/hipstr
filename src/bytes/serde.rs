//! `serde` support for `HipByt`.
//!
//! This module provides support for serializing and deserializing `HipByt`
//! using [`serde`]. It is enabled by default when the `serde` feature is
//! enabled.
//!
//! # Examples
//!
//! ```
//! use hipstr::HipByt;
//!
//! let s = HipByt::from(b"hello");
//! let serialized = serde_json::to_string(&s).unwrap();
//! assert_eq!(serialized, "[104,101,108,108,111]");
//!
//! let deserialized: HipByt = serde_json::from_str(r#""hello""#).unwrap();
//! assert_eq!(deserialized, s);
//! ```
//!
//! # Notable aspects of the implementations
//!
//! Unlike the `Vec<T>` generic implementation which treats data as a generic
//! sequence, `HipByt` uses the more efficient byte sequence specific API for
//! serialization (similar to the [`serde_bytes`] crate). Note that the actual
//! outcome of a serialization depends on the underlying format's support for
//! byte sequences.
//!
//! During deserialization, this implementation minimizes allocations by reusing
//! the deserializer's internal buffer if possible.
//!
//! [`serde_bytes`]: https://docs.rs/serde_bytes

use alloc::fmt;
use alloc::string::String;
use alloc::vec::Vec;
use core::marker::PhantomData;

use serde::de::Visitor;
use serde::{Deserialize, Serialize};

use super::HipByt;
use crate::Backend;

const EXPECTING: &str = "a byte array";

impl<B> Serialize for HipByt<'_, B>
where
    B: Backend,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_bytes(self.as_slice())
    }
}

/// Deserializer's visitor for owned `HipByt`.
struct OwnedVisitor<'borrow, B: Backend>(PhantomData<HipByt<'borrow, B>>);

impl<'de, 'borrow, B: Backend> Visitor<'de> for OwnedVisitor<'borrow, B> {
    type Value = HipByt<'borrow, B>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str(EXPECTING)
    }

    fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(HipByt::from(v))
    }

    fn visit_byte_buf<E>(self, v: Vec<u8>) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(HipByt::from(v))
    }

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(HipByt::from(v.as_bytes()))
    }

    fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(HipByt::from(v.into_bytes()))
    }

    fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
    where
        A: serde::de::SeqAccess<'de>,
    {
        let len = core::cmp::min(seq.size_hint().unwrap_or(0), 4096);
        let mut bytes = Vec::with_capacity(len);

        while let Some(b) = seq.next_element()? {
            bytes.push(b);
        }

        Ok(HipByt::from(bytes))
    }
}

impl<'de, B> Deserialize<'de> for HipByt<'_, B>
where
    B: Backend,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_bytes(OwnedVisitor(PhantomData))
    }
}

/// Deserializer's visitor for borrowed `HipByt`.
struct BorrowedVisitor<'de, B: Backend>(PhantomData<HipByt<'de, B>>);

impl<'de, B: Backend> Visitor<'de> for BorrowedVisitor<'de, B> {
    type Value = HipByt<'de, B>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str(EXPECTING)
    }

    fn visit_borrowed_bytes<E>(self, v: &'de [u8]) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(HipByt::borrowed(v))
    }

    fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(HipByt::from(v))
    }

    fn visit_byte_buf<E>(self, v: Vec<u8>) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(HipByt::from(v))
    }

    fn visit_borrowed_str<E>(self, v: &'de str) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(HipByt::borrowed(v.as_bytes()))
    }

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(HipByt::from(v.as_bytes()))
    }

    fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(HipByt::from(v.into_bytes()))
    }

    fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
    where
        A: serde::de::SeqAccess<'de>,
    {
        let len = core::cmp::min(seq.size_hint().unwrap_or(0), 4096);
        let mut bytes = Vec::with_capacity(len);

        while let Some(b) = seq.next_element()? {
            bytes.push(b);
        }

        Ok(HipByt::from(bytes))
    }
}

/// Deserializes a `HipByt` as a borrow if possible.
///
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// # use hipstr::HipByt;
/// use serde::Deserialize;
///
/// #[derive(Deserialize)]
/// struct MyStruct<'a> {
///     #[serde(borrow, deserialize_with = "hipstr::bytes::serde::borrow_deserialize")]
///     field: HipByt<'a>,
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
pub fn borrow_deserialize<'de: 'a, 'a, D, B>(deserializer: D) -> Result<HipByt<'a, B>, D::Error>
where
    D: serde::Deserializer<'de>,
    B: Backend,
{
    deserializer.deserialize_bytes(BorrowedVisitor(PhantomData))
}

#[cfg(test)]
mod tests;
