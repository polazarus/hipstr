use super::*;
use crate::HipByt as H;

#[test]
fn test_borsh() {
    let s = H::from(b"123");
    let mut buf = Vec::new();
    s.serialize(&mut buf).unwrap();
    let s = H::deserialize(&mut buf.as_slice()).unwrap();
    assert_eq!(s, b"123");

    let a = b"a".repeat(42);
    let s = H::from(a.as_slice());
    let mut buf = Vec::new();
    s.serialize(&mut buf).unwrap();
    let s = H::deserialize(&mut buf.as_slice()).unwrap();
    assert_eq!(s, a);

    let s = H::new();
    let mut buf = Vec::new();
    s.serialize(&mut buf).unwrap();
    let s = H::deserialize(&mut buf.as_slice()).unwrap();
    assert_eq!(s, b"");
}

#[test]
fn test_compat_borsh() {
    let s = "123";
    let mut buf = Vec::new();
    s.serialize(&mut buf).unwrap();
    let s = H::deserialize(&mut buf.as_slice()).unwrap();
    assert_eq!(s, b"123");

    let s = H::from(b"123");
    let mut buf = Vec::new();
    s.serialize(&mut buf).unwrap();
    let s = Vec::<u8>::deserialize(&mut buf.as_slice()).unwrap();
    assert_eq!(s, b"123");
}

#[test]
fn test_bad_borsh() {
    let s = H::from(b"123");
    let mut buf = Vec::new();
    s.serialize(&mut buf).unwrap();

    let payload_short = H::deserialize(&mut &buf[..buf.len() - 1]);
    assert!(payload_short.is_err());

    let size_short = H::deserialize(&mut &buf[..2]);
    assert!(size_short.is_err());
}
