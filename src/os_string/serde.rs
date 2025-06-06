//! `serde` support for `HipOsStr`.
//!
//! This module provides support for serializing and deserializing `HipStr`
//! using [`serde`]. It is enabled by default when the `serde` feature is
//! enabled and on supported platforms (`unix` and `windows`).
//!
//! # Examples
//!
//! ```
//! use hipstr::HipStr;
//!
//! let s = HipStr::from("hello");
//! let serialized = serde_json::to_string(&s).unwrap();
//! assert_eq!(serialized, r#""hello""#);
//!
//! let deserialized: HipStr = serde_json::from_str(&serialized).unwrap();
//! assert_eq!(deserialized, s);
//! ```
//!
//! # Notable aspects of the implementation
//!
//! Due to the overall weirdness of `OsString` and their support in `serde`, no
//! attempt is made to improve on `OsString` standard `serde` implementation.

use std::ffi::OsString;

use serde::{Deserialize, Serialize};

use super::HipOsStr;
use crate::backend::Backend;

impl<B> Serialize for HipOsStr<'_, B>
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

impl<'de, B> Deserialize<'de> for HipOsStr<'_, B>
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
        #[cfg(unix)]
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
