use std::borrow::Cow;
use std::fmt;

use serde::{de, Deserialize, Serialize};

use super::HipStr;
use crate::Backend;

impl<'borrow, B> Serialize for HipStr<'borrow, B>
where
    B: Backend,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(self.as_str())
    }
}

impl<'de, 'borrow, B> Deserialize<'de> for HipStr<'borrow, B>
where
    B: Backend,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        Ok(Self::from(s))
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
        println!("borrowed");
        Ok(Cow::Borrowed(v))
    }

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        println!("owned");
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
/// ```ignore
/// use hipstr::HipStr;
/// #[derive(Deserialize)]
/// struct MyStruct<'a> {
///     #[serde(borrow, deserialize_with = "hipstr::string::serde::borrow_deserialize")]
///     field: HipStr<'a>,
/// }
/// # fn main() {
/// let s: MyStruct = serde_json::from_str(r#"{"field": "abc"}"#).unwrap();
/// assert!(s.field.is_borrowed());
/// # }
/// ```
///
/// # Errors
///
/// Returns a deserializer if either the serialization is incorrect or an unexpected value is encountered.
pub fn borrow_deserialize<'de: 'a, 'a, D, B>(deserializer: D) -> Result<HipStr<'a, B>, D::Error>
where
    D: serde::Deserializer<'de>,
    B: Backend,
{
    let cow: Cow<'de, str> = deserializer.deserialize_str(CowVisitor)?;
    Ok(HipStr::from(cow))
}

#[cfg(test)]
mod tests {
    use serde_test::{assert_de_tokens, assert_tokens, Token};

    use super::borrow_deserialize;
    use crate::HipStr;

    #[test]
    fn test_serde() {
        let empty_str = HipStr::new();
        assert_tokens(&empty_str, &[Token::Str("")]);
        assert_de_tokens(&empty_str, &[Token::BorrowedStr("")]);
        assert_de_tokens(&empty_str, &[Token::String("")]);

        let small = HipStr::from("abc");
        assert_de_tokens(&small, &[Token::Str("abc")]);
        assert_de_tokens(&small, &[Token::BorrowedStr("abc")]);
        assert_de_tokens(&small, &[Token::String("abc")]);
    }

    #[test]
    fn test_serde_borrowing() {
        use serde::Deserialize;
        use serde_json::Value;

        let v = Value::from("abcdefghijklmnopqrstuvwxyz");
        let h1: HipStr = borrow_deserialize(&v).unwrap();
        let h2: HipStr = Deserialize::deserialize(&v).unwrap();
        assert!(h1.is_borrowed());
        assert!(!h2.is_borrowed());

        #[derive(Deserialize)]
        struct MyStruct<'a> {
            #[serde(borrow, deserialize_with = "crate::string::serde::borrow_deserialize")]
            field: HipStr<'a>,
        }
        let s: MyStruct =
            serde_json::from_str(r#"{"field": "abcdefghijklmnopqrstuvwxyz"}"#).unwrap();
        assert!(s.field.is_borrowed());
    }
}
