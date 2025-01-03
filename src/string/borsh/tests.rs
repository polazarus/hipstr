use alloc::string::String;
use alloc::vec::Vec;

use super::*;
use crate::{HipByt, HipStr as H};

#[test]
fn test_borsh() {
    let s = H::from("123");
    let mut buf = Vec::new();
    s.serialize(&mut buf).unwrap();
    let s = H::deserialize(&mut buf.as_slice()).unwrap();
    assert_eq!(s, "123");

    let a = "a".repeat(42);
    let s = H::from(a.as_str());
    let mut buf = Vec::new();
    s.serialize(&mut buf).unwrap();
    let s = H::deserialize(&mut buf.as_slice()).unwrap();
    assert_eq!(s, a);

    let s = H::new();
    let mut buf = Vec::new();
    s.serialize(&mut buf).unwrap();
    let s = H::deserialize(&mut buf.as_slice()).unwrap();
    assert_eq!(s, "");
}

#[test]
fn test_compat_borsh() {
    let s = "123";
    let mut buf = Vec::new();
    s.serialize(&mut buf).unwrap();
    let s = H::deserialize(&mut buf.as_slice()).unwrap();
    assert_eq!(s, "123");

    let s = H::from("123");
    let mut buf = Vec::new();
    s.serialize(&mut buf).unwrap();
    let s = String::deserialize(&mut buf.as_slice()).unwrap();
    assert_eq!(s, "123");
}

#[test]
fn test_bad_borsh() {
    let s = H::from("123");
    let mut buf = Vec::new();
    s.serialize(&mut buf).unwrap();

    let payload_short = H::deserialize(&mut &buf[..buf.len() - 1]);
    assert!(payload_short.is_err());

    let size_short = H::deserialize(&mut &buf[..2]);
    assert!(size_short.is_err());

    let v: &[u8] = b"abc\xFFc";
    let mut buf = Vec::new();
    v.serialize(&mut buf).unwrap();
    let s = HipByt::deserialize(&mut buf.as_slice()).unwrap();
    assert_eq!(s, v);

    let s = H::deserialize(&mut buf.as_slice());
    let err = s.unwrap_err();
    let kind = err.kind();
    assert_eq!(kind, ErrorKind::InvalidData);
    assert_eq!(
        err.get_ref().unwrap(),
        "invalid utf-8 sequence of 1 bytes from index 3"
    );
}
