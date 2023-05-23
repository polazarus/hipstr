use serde::{Deserialize, Serialize};

use super::HipStr;
use crate::Backend;

impl<B> Serialize for HipStr<B>
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

impl<'de, B> Deserialize<'de> for HipStr<B>
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

#[cfg(test)]
mod tests {
    use serde_test::{assert_de_tokens, assert_tokens, Token};

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
}
