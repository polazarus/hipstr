use std::path::PathBuf;

use serde::{de, Deserialize, Serialize};

use super::HipPath;
use crate::alloc::borrow::Cow;
use crate::alloc::fmt;
use crate::Backend;

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
        Ok(Self::from(PathBuf::deserialize(deserializer)?))
    }
}

/// Minimal string cow visitor
struct CowVisitor;

impl<'de> de::Visitor<'de> for CowVisitor {
    type Value = Cow<'de, str>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("path string")
    }

    fn visit_borrowed_str<E>(self, v: &'de str) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Ok(Cow::Borrowed(v))
    }

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Ok(Cow::Owned(v.to_string()))
    }

    fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Ok(Cow::Owned(v))
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
    let cow: Cow<'de, str> = deserializer.deserialize_str(CowVisitor)?;
    Ok(HipPath::from(cow))
}

#[cfg(test)]
mod tests;
