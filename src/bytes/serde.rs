use serde::{Deserialize, Serialize};

use super::HipByt;
use crate::alloc::borrow::Cow;
use crate::alloc::vec::Vec;
use crate::Backend;

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

impl<'de, B> Deserialize<'de> for HipByt<'_, B>
where
    B: Backend,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let v: Vec<u8> = serde_bytes::deserialize(deserializer)?;
        Ok(Self::from(v))
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
    let cow: Cow<'de, [u8]> = serde_bytes::Deserialize::deserialize(deserializer)?;
    Ok(HipByt::from(cow))
}

#[cfg(test)]
mod tests;
