use super::*;

#[test]
fn test_clone() {
    let a = Borrowed::new(b"abc");
    let b = a.clone();
    assert_eq!(a.as_slice(), b.as_slice());
}
