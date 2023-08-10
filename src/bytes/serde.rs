use std::borrow::Cow;

use serde::{Deserialize, Serialize};

use super::HipByt;
use crate::Backend;

impl<'borrow, B> Serialize for HipByt<'borrow, B>
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

impl<'de, 'borrow, B> Deserialize<'de> for HipByt<'borrow, B>
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
/// ```ignore
/// use hipstr::HipByt;
/// #[derive(Deserialize)]
/// struct MyStruct<'a> {
///     #[serde(borrow, deserialize_with = "hipstr::bytes::serde::borrowg_deserialize")]
///     field: HipByt<'a>,
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
pub fn borrow_deserialize<'de: 'a, 'a, D, B>(deserializer: D) -> Result<HipByt<'a, B>, D::Error>
where
    D: serde::Deserializer<'de>,
    B: Backend,
{
    let cow: Cow<'de, [u8]> = serde_bytes::Deserialize::deserialize(deserializer)?;
    Ok(HipByt::from(cow))
}

#[cfg(test)]
mod tests {
    use serde_test::{
        assert_de_tokens, assert_de_tokens_error, assert_ser_tokens, assert_tokens, Token,
    };

    use crate::bytes::serde::borrow_deserialize;
    use crate::HipByt;

    #[test]
    fn test_serde() {
        let ref empty = HipByt::new();
        assert_ser_tokens(empty, &[Token::Bytes(b"")]);
        assert_de_tokens(empty, &[Token::Bytes(b"")]);
        assert_de_tokens(empty, &[Token::ByteBuf(b"")]);
        assert_de_tokens(empty, &[Token::BorrowedBytes(b"")]);
        assert_de_tokens(empty, &[Token::Seq { len: Some(0) }, Token::SeqEnd]);

        let ref small = HipByt::from(&[1, 2, 3]);
        assert_tokens(small, &[Token::Bytes(b"\x01\x02\x03")]);
        assert_de_tokens(small, &[Token::ByteBuf(b"\x01\x02\x03")]);
        assert_de_tokens(small, &[Token::BorrowedBytes(b"\x01\x02\x03")]);
        assert_de_tokens(
            small,
            &[
                Token::Seq { len: Some(3) },
                Token::U8(1),
                Token::U8(2),
                Token::U8(3),
                Token::SeqEnd,
            ],
        );
    }

    #[test]
    fn test_de_error() {
        assert_de_tokens_error::<HipByt>(
            &[Token::F32(0.0)],
            "invalid type: floating point `0`, expected byte array",
        );
    }

    #[test]
    fn test_serde_borrowing() {
        use serde::de::Deserialize;
        use serde_json::Value;

        use super::super::HipByt;
        use crate::Local;

        let v = Value::from("abcdefghijklmnopqrstuvwxyz");
        let h1: HipByt<'_, Local> = borrow_deserialize(&v).unwrap();
        let h2: HipByt<'_, Local> = Deserialize::deserialize(&v).unwrap();
        assert!(h1.is_borrowed());
        assert!(!h2.is_borrowed());
    }
}
