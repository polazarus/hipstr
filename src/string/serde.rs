use core::marker::PhantomData;

use serde::de::{Error, Visitor};
use serde::{de, Deserialize, Deserializer, Serialize};

use super::HipStr;
use crate::alloc::borrow::Cow;
use crate::alloc::fmt;
use crate::alloc::string::{String, ToString};
use crate::Backend;

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

struct HipStrVisitor<'b, B> {
    data: PhantomData<&'b B>,
}

impl<'a, 'b, B: Backend> Visitor<'a> for HipStrVisitor<'b, B> {
    type Value = HipStr<'b, B>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a string")
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
        deserializer.deserialize_str(HipStrVisitor::<B> {
            data: PhantomData::default(),
        })
    }
}

/// Minimal string cow visitor
struct CowVisitor;

impl<'de> de::Visitor<'de> for CowVisitor {
    type Value = Cow<'de, str>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a string")
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
    let cow: Cow<'de, str> = deserializer.deserialize_str(CowVisitor)?;
    Ok(HipStr::from(cow))
}

#[cfg(test)]
mod tests;
