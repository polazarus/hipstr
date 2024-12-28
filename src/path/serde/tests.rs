use serde_test::{assert_de_tokens, assert_de_tokens_error, assert_tokens, Token};

use super::*;
use crate::HipPath;

#[derive(Deserialize, PartialEq, Eq, Debug)]
struct MyStruct<'a> {
    #[serde(borrow, deserialize_with = "borrow_deserialize")]
    field: HipPath<'a>,
}

#[test]
fn test_serde() {
    let empty = HipPath::new();
    assert_tokens(&empty, &[Token::Str("")]);
}

#[test]
fn test_serde_err() {
    assert_de_tokens_error::<HipPath>(
        &[Token::I32(0)],
        "invalid type: integer `0`, expected a string",
    );
}

#[test]
fn test_serde_borrow() {
    use serde_json::Value;

    let v = Value::from("abcdefghijklmnopqrstuvwxyz");
    let h1: HipPath = borrow_deserialize(&v).unwrap();
    let h2: HipPath = Deserialize::deserialize(&v).unwrap();
    assert!(h1.is_borrowed());
    assert!(!h2.is_borrowed());

    let s: MyStruct = serde_json::from_str(r#"{"field": "abcdefghijklmnopqrstuvwxyz"}"#).unwrap();
    assert!(s.field.is_borrowed());

    assert_de_tokens(
        &MyStruct {
            field: HipPath::from("a"),
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
            field: HipPath::from("a"),
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
            field: HipPath::from("a"),
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
