use super::*;

const N: usize = 23;

type I = Inline<N>;

#[test]
fn test_inline() {
    let inline = I::new(b"abc").unwrap();
    assert_eq!(inline.as_slice(), b"abc");
    assert_eq!(inline.len(), 3);

    assert!(I::new(&b"*".repeat(N + 1)).is_none());
}

#[test]
fn test_clone() {
    let a: I = Inline::new(b"abc").unwrap();
    let b = a.clone();
    assert_eq!(a.as_slice(), b.as_slice());
}

#[test]
fn test_zeroed() {
    let inline = I::zeroed(5);
    assert_eq!(inline.as_slice(), &[0; 5]);
}

#[should_panic]
#[test]
fn test_zeroed_panic() {
    let _ = I::zeroed(N + 1);
}
