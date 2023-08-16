use serde::{de, Deserialize, Serialize};

use super::HipStr;
use crate::alloc::borrow::Cow;
use crate::alloc::fmt;
use crate::alloc::string::{String, ToString};
use crate::Backend;

impl<'borrow, B> Serialize for HipStr<'borrow, B>
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

impl<'de, 'borrow, B> Deserialize<'de> for HipStr<'borrow, B>
where
    B: Backend,
{
    #[inline]
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
mod tests {
    use serde::Deserialize;
    use serde_test::{assert_de_tokens, assert_de_tokens_error, assert_tokens, Token};

    use super::borrow_deserialize;
    use crate::HipStr;

    #[derive(Deserialize, PartialEq, Eq, Debug)]
    struct MyStruct<'a> {
        #[serde(borrow, deserialize_with = "borrow_deserialize")]
        field: HipStr<'a>,
    }

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
    fn test_serde_err() {
        assert_de_tokens_error::<HipStr>(
            &[Token::I32(0)],
            "invalid type: integer `0`, expected a string",
        );
    }

    #[test]
    fn test_serde_borrow() {
        use serde_json::Value;

        let v = Value::from("abcdefghijklmnopqrstuvwxyz");
        let h1: HipStr = borrow_deserialize(&v).unwrap();
        let h2: HipStr = Deserialize::deserialize(&v).unwrap();
        assert!(h1.is_borrowed());
        assert!(!h2.is_borrowed());

        let s: MyStruct =
            serde_json::from_str(r#"{"field": "abcdefghijklmnopqrstuvwxyz"}"#).unwrap();
        assert!(s.field.is_borrowed());

        assert_de_tokens(
            &MyStruct {
                field: HipStr::from("a"),
            },
            &[
                Token::Struct {
                    name: "MyStruct",
                    len: 1,
                },
                Token::Str("field"),
                Token::Str("a"),
                Token::StructEnd,
            ],
        );

        assert_de_tokens(
            &MyStruct {
                field: HipStr::from("a"),
            },
            &[
                Token::Struct {
                    name: "MyStruct",
                    len: 1,
                },
                Token::Str("field"),
                Token::BorrowedStr("a"),
                Token::StructEnd,
            ],
        );

        assert_de_tokens(
            &MyStruct {
                field: HipStr::from("a"),
            },
            &[
                Token::Struct {
                    name: "MyStruct",
                    len: 1,
                },
                Token::String("field"),
                Token::String("a"),
                Token::StructEnd,
            ],
        );
    }

    #[test]
    fn test_serde_borrow_err() {
        assert_de_tokens_error::<MyStruct>(
            &[
                Token::Struct {
                    name: "MyStruct",
                    len: 1,
                },
                Token::Str("field"),
                Token::I32(0),
                Token::StructEnd,
            ],
            "invalid type: integer `0`, expected a string",
        );
    }
}
