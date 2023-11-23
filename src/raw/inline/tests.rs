use super::*;

const N: usize = 23;

type I = Inline<N>;

#[test]
fn test_clone() {
    let a: I = Inline::new(b"abc");
    let b = a.clone();
    assert_eq!(a.as_slice(), b.as_slice());
}

#[test]
fn test_zeroed() {
    let inline = I::zeroed(5);
    assert_eq!(inline.as_slice(), &[0; 5]);
}

#[test]
#[should_panic]
fn test_zeroed_panic() {
    let _ = I::zeroed(N + 1);
}
