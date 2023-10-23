use std::ffi::OsString;

use serde::{Deserialize, Serialize};

use super::HipOsStr;
use crate::Backend;

impl<'borrow, B> Serialize for HipOsStr<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.as_os_str().serialize(serializer)
    }
}

impl<'de, 'borrow, B> Deserialize<'de> for HipOsStr<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        Ok(Self::from(OsString::deserialize(deserializer)?))
    }
}

#[cfg(test)]
mod tests {
    use serde_test::{assert_de_tokens_error, assert_tokens, Token};

    use crate::HipOsStr;

    #[test]
    fn test_serde() {
        let empty = HipOsStr::new();
        #[cfg(windows)]
        assert_tokens(
            &empty,
            &[
                Token::NewtypeVariant {
                    name: "OsString",
                    variant: "Windows",
                },
                Token::Seq { len: Some(0) },
                Token::SeqEnd,
            ],
        );
        #[cfg(not(windows))]
        assert_tokens(
            &empty,
            &[
                Token::NewtypeVariant {
                    name: "OsString",
                    variant: "Unix",
                },
                Token::Seq { len: Some(0) },
                Token::SeqEnd,
            ],
        );
    }

    #[test]
    fn test_serde_err() {
        assert_de_tokens_error::<HipOsStr>(
            &[Token::I32(0)],
            "invalid type: integer `0`, expected os string",
        );
    }
}
