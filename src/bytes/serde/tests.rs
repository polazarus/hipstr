use serde::Deserialize;
use serde_test::{
    assert_de_tokens, assert_de_tokens_error, assert_ser_tokens, assert_tokens, Token,
};

use super::borrow_deserialize;
use crate::HipByt;

#[derive(Deserialize, Debug, PartialEq, Eq)]
struct MyStruct<'a> {
    #[serde(borrow, deserialize_with = "borrow_deserialize")]
    field: HipByt<'a>,
}

#[test]
fn test_serde() {
    let empty = &HipByt::new();
    assert_ser_tokens(empty, &[Token::Bytes(b"")]);
    assert_de_tokens(empty, &[Token::Bytes(b"")]);
    assert_de_tokens(empty, &[Token::ByteBuf(b"")]);
    assert_de_tokens(empty, &[Token::BorrowedBytes(b"")]);
    assert_de_tokens(empty, &[Token::Seq { len: Some(0) }, Token::SeqEnd]);

    let small = &HipByt::from(&[1, 2, 3]);
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
        &[Token::Bool(true)],
        "invalid type: boolean `true`, expected byte array",
    );
}

#[test]
fn test_serde_borrow() {
    use serde_json::Value;

    use super::super::HipByt;
    use crate::Local;

    let v = Value::from("abcdefghijklmnopqrstuvwxyz");
    let h1: HipByt<'_, Local> = borrow_deserialize(&v).unwrap();
    let h2: HipByt<'_, Local> = Deserialize::deserialize(&v).unwrap();
    assert!(h1.is_borrowed());
    assert!(!h2.is_borrowed());

    let s: MyStruct = serde_json::from_str(r#"{"field": "abcdefghijklmnopqrstuvwxyz"}"#).unwrap();
    assert!(s.field.is_borrowed());

    assert_de_tokens(
        &MyStruct {
            field: HipByt::from(b"a"),
        },
        &[
            Token::Struct {
                name: "MyStruct",
                len: 1,
            },
            Token::Str("field"),
            Token::Bytes(b"a"),
            Token::StructEnd,
        ],
    );

    assert_de_tokens(
        &MyStruct {
            field: HipByt::from(b"a"),
        },
        &[
            Token::Struct {
                name: "MyStruct",
                len: 1,
            },
            Token::Str("field"),
            Token::BorrowedBytes(b"a"),
            Token::StructEnd,
        ],
    );

    assert_de_tokens(
        &MyStruct {
            field: HipByt::from(b"a"),
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
            field: HipByt::from(b"a"),
        },
        &[
            Token::Struct {
                name: "MyStruct",
                len: 1,
            },
            Token::Str("field"),
            Token::String("a"),
            Token::StructEnd,
        ],
    );
    assert_de_tokens(
        &MyStruct {
            field: HipByt::from(b"a"),
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
        "invalid type: integer `0`, expected a byte array",
    );
}
