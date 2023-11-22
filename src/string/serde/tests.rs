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

    let s: MyStruct = serde_json::from_str(r#"{"field": "abcdefghijklmnopqrstuvwxyz"}"#).unwrap();
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
