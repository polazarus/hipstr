use super::*;
use crate::thin::Reserved;

type Thin<T> = ThinVec<T, Reserved>;

#[test]
fn remove() {
    let mut v: Thin<i32> = crate::copy_thin_vec![10, 20, 30, 40];
    let removed = v.remove(1);
    assert_eq!(removed, 20);
    assert_eq!(v.as_slice(), &[10, 30, 40]);
}

#[test]
fn remove_first() {
    let mut v: Thin<i32> = crate::copy_thin_vec![10, 20, 30, 40];
    let removed = v.remove(0);
    assert_eq!(removed, 10);
    assert_eq!(v.as_slice(), &[20, 30, 40]);
}

#[test]
fn remove_last() {
    let mut v: Thin<i32> = crate::copy_thin_vec![10, 20, 30, 40];
    let removed = v.remove(v.len() - 1);
    assert_eq!(removed, 40);
    assert_eq!(v.as_slice(), &[10, 20, 30]);
}

#[test]
#[should_panic(expected = "index out of bounds")]
fn remove_panic() {
    let mut v: Thin<i32> = crate::copy_thin_vec![1, 2, 3];
    let _ = v.remove(3);
}

#[test]
fn swap_remove() {
    let mut v: Thin<i32> = crate::copy_thin_vec![10, 20, 30, 40];
    let removed = v.swap_remove(1);
    assert_eq!(removed, 20);
    assert_eq!(v.as_slice(), &[10, 40, 30]);
}

#[test]
fn swap_remove_first() {
    let mut v: Thin<i32> = crate::copy_thin_vec![10, 20, 30, 40];
    let removed = v.swap_remove(0);
    assert_eq!(removed, 10);
    assert_eq!(v.as_slice(), &[40, 20, 30]);
}

#[test]
fn swap_remove_last() {
    let mut v: Thin<i32> = crate::copy_thin_vec![10, 20, 30, 40];
    let removed = v.swap_remove(v.len() - 1);
    assert_eq!(removed, 40);
    assert_eq!(v.as_slice(), &[10, 20, 30]);
}

#[test]
#[should_panic(expected = "index out of bounds")]
fn swap_remove_panic() {
    let mut v: Thin<i32> = crate::copy_thin_vec![1, 2, 3];
    let _ = v.swap_remove(3);
}
