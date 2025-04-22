//! `serde` support for `HipPath`.
//!
//! This module provides support for serializing and deserializing `HipStr`
//! using [`serde`]. It is enabled by default when the `serde` feature is
//! enabled.
//!
//! # Examples
//!
//! ```
//! use hipstr::HipPath;
//!
//! let s = HipPath::borrowed("/usr/bin");
//! let serialized = serde_json::to_string(&s).unwrap();
//! assert_eq!(serialized, r#""/usr/bin""#);
//!
//! let deserialized: HipPath = serde_json::from_str(&serialized).unwrap();
//! assert_eq!(deserialized, s);
//! ```
//!
//! # Notable aspects of the implementation
//!
//! During deserialization, this implementation minimizes allocations by reusing
//! the deserializer's internal buffer if possible.
//!
//! Unlike `PathBuf`'s `Deserialize`, this implementation declares transparently
//! that it's expecting a string. Indeed not reusing `HipStr`'s implementation
//! just does not make any sense.

use serde::{Deserialize, Serialize};

use super::HipPath;
use crate::backend::Backend;
use crate::string::HipStr;

impl<B> Serialize for HipPath<'_, B>
where
    B: Backend,
{
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.as_path().serialize(serializer)
    }
}

impl<'de, B> Deserialize<'de> for HipPath<'_, B>
where
    B: Backend,
{
    #[inline]
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let s = HipStr::deserialize(deserializer)?;
        Ok(Self::from(s))
    }
}

/// Deserializes a `HipPath` as a borrow if possible.
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// # use hipstr::HipPath;
/// use serde::Deserialize;
///
/// #[derive(Deserialize)]
/// struct MyStruct<'a> {
///     #[serde(borrow, deserialize_with = "hipstr::path::serde::borrow_deserialize")]
///     field: HipPath<'a>,
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
pub fn borrow_deserialize<'de: 'a, 'a, D, B>(deserializer: D) -> Result<HipPath<'a, B>, D::Error>
where
    D: serde::Deserializer<'de>,
    B: Backend,
{
    crate::string::serde::borrow_deserialize(deserializer).map(HipPath::from)
}

#[cfg(test)]
mod tests;
