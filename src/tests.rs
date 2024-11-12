use crate::{HipStr, LocalHipStr, UniqueHipStr};

#[test]
fn test_unique() {
    let r = UniqueHipStr::from("*".repeat(42));
    let t = r.clone();
    assert_eq!(r, t);
}

#[test]
fn test_local() {
    let r = LocalHipStr::from("*".repeat(42));
    let t = r.clone();
    assert_eq!(r, t);
}

#[test]
fn test_threadsafe() {
    let r = HipStr::from("*".repeat(42));
    let t = r.clone();
    assert_eq!(r, t);
}
