use std::marker::PhantomData;

use serde::de::Visitor;
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

#[derive(Clone, Copy, Debug)]
struct BytesVisitor;

impl<'de> Visitor<'de> for BytesVisitor {
    type Value = Vec<u8>;

    fn visit_byte_buf<E>(self, v: Vec<u8>) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(v)
    }

    fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(v.into())
    }

    fn visit_borrowed_bytes<E>(self, v: &'de [u8]) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(v.into())
    }

    fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
    where
        A: serde::de::SeqAccess<'de>,
    {
        let mut v = seq.size_hint().map_or_else(Vec::new, Vec::with_capacity);
        while let Some(e) = seq.next_element()? {
            v.push(e);
        }
        Ok(v)
    }

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(formatter, "bytes")
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
        let v = deserializer.deserialize_byte_buf(BytesVisitor)?;
        Ok(Self::from(v))
    }
}

#[derive(Clone, Copy, Debug)]
struct BorrowingByteVisitor<B>(PhantomData<B>);

impl<'de, B> Visitor<'de> for BorrowingByteVisitor<B>
where
    B: Backend,
{
    type Value = HipByt<'de, B>;

    fn visit_byte_buf<E>(self, v: Vec<u8>) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(v.into())
    }

    fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(v.into())
    }

    fn visit_borrowed_bytes<E>(self, v: &'de [u8]) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(HipByt::with_borrow(v))
    }

    fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
    where
        A: serde::de::SeqAccess<'de>,
    {
        let mut v = seq.size_hint().map_or_else(Vec::new, Vec::with_capacity);
        while let Some(e) = seq.next_element()? {
            v.push(e);
        }
        Ok(v.into())
    }

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(formatter, "bytes")
    }
}

/// Deserializes a `HipByt` as a borrow if possible.
///
/// ```rust
/// use hipstr::bytes::HipByt;
/// use hipstr::Local;
/// #[derive(serde::Deserialize)]
/// struct MyStruct<'a> {
///     #[serde(borrow, deserialize_with = "hipstr::bytes::serde::borrowing_deserialize")]
///     field: HipByt<'a, Local>,
/// }
/// ```
pub fn borrowing_deserialize<'de, D, B>(deserializer: D) -> Result<HipByt<'de, B>, D::Error>
where
    D: serde::Deserializer<'de>,
    B: Backend,
{
    deserializer.deserialize_byte_buf(BorrowingByteVisitor(PhantomData))
}

#[cfg(test)]
mod tests {
    use serde_test::{
        assert_de_tokens, assert_de_tokens_error, assert_ser_tokens, assert_tokens, Token,
    };

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
            &[Token::Str("")],
            "invalid type: string \"\", expected bytes",
        );
    }
}
