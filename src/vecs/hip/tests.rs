use alloc::boxed::Box;
use core::hash;

use crate::vecs::hip::{HipVec, SplitOffError};
use crate::Arc;

#[test]
fn size_of_hipvec() {
    assert_eq!(
        size_of::<HipVec<'static, u8, Arc>>(),
        3 * size_of::<usize>()
    );

    assert_eq!(
        size_of::<HipVec<'static, usize, Arc>>(),
        3 * size_of::<usize>()
    );
}

#[test]
fn new() {
    let h = HipVec::<u8, Arc>::new();
    assert_eq!(h.len(), 0);
    assert!(!h.is_allocated());
}

#[test]
fn new_boxed() {
    let h = HipVec::<Box<u8>, Arc>::new();
    assert_eq!(h.len(), 0);
    assert!(!h.is_allocated());
}

#[test]
fn from_array_inline() {
    let h = HipVec::<u8, Arc>::from([1, 2, 3, 4, 5]);
    assert_eq!(h.len(), 5);
    assert!(h.is_inline());
    assert!(!h.is_allocated());
    assert_eq!(h.as_slice(), &[1, 2, 3, 4, 5]);
}

#[test]
fn from_array_thin() {
    let h = HipVec::<u8, Arc>::from([42; 42]);
    assert_eq!(h.len(), 42);
    // assert!(!h.is_inline());
    // assert!(h.is_allocated());
    assert_eq!(h.as_slice(), &[42; 42]);
    assert!(h.is_thin());
    assert!(!h.is_fat());
    assert!(h.is_allocated());
}

#[test]
fn try_split_off() {
    let mut h = HipVec::<u8, Arc>::from([1, 2, 3, 4, 5]);
    let other = h.try_split_off(2).unwrap();
    assert_eq!(h.len(), 2);
    assert_eq!(h.as_slice(), &[1, 2]);
    assert!(h.is_inline());
    assert_eq!(other.len(), 3);
    assert_eq!(other.as_slice(), &[3, 4, 5]);
    assert!(other.is_inline());

    let mut h = HipVec::<u8, Arc>::from([42; 42]);
    let other = h.try_split_off(10).unwrap();
    assert_eq!(h.len(), 10);
    assert_eq!(h.as_slice(), &[42; 10]);
    assert!(h.is_thin());
    assert_eq!(other.len(), 32);
    assert_eq!(other.as_slice(), &[42; 32]);
    assert!(other.is_thin());
    assert_eq!(other.as_ptr(), unsafe { h.as_ptr().add(10) });

    let mut h = HipVec::<u8, Arc>::from([1, 2, 3, 4, 5]);
    let other = h.try_split_off(5).unwrap();
    assert!(other.is_empty());

    let mut h = HipVec::<u8, Arc>::from([1, 2, 3, 4, 5]);
    assert_eq!(h.try_split_off(6).unwrap_err(), SplitOffError::OutOfBounds);

    // TODO test ref count overflow
}

#[test]
fn split_off() {
    let mut h = HipVec::<u8, Arc>::from([1, 2, 3, 4, 5]);
    let other = h.split_off(2);
    assert_eq!(h.len(), 2);
    assert_eq!(h.as_slice(), &[1, 2]);
    assert!(h.is_inline());
    assert_eq!(other.len(), 3);
    assert_eq!(other.as_slice(), &[3, 4, 5]);
    assert!(other.is_inline());

    let mut h = HipVec::<u8, Arc>::from([42; 42]);
    let other = h.split_off(10);
    assert_eq!(h.len(), 10);
    assert_eq!(h.as_slice(), &[42; 10]);
    assert!(h.is_thin());
    assert_eq!(other.len(), 32);
    assert_eq!(other.as_slice(), &[42; 32]);
    assert!(other.is_thin());
    assert_eq!(other.as_ptr(), unsafe { h.as_ptr().add(10) });

    let mut h = HipVec::<u8, Arc>::from([1, 2, 3, 4, 5]);
    let other = h.split_off(5);
    assert!(other.is_empty());
}

#[test]
#[should_panic(expected = "split index out of bounds")]
fn split_off_oob() {
    let mut h = HipVec::<u8, Arc>::from([1, 2, 3, 4, 5]);
    // should panic
    let _h2 = h.split_off(6);
}

#[test]
fn truncate() {
    let mut h = HipVec::<u8, Arc>::from([1, 2, 3, 4, 5]);
    h.truncate(3);
    assert_eq!(h.len(), 3);
    assert_eq!(h.as_slice(), &[1, 2, 3]);
    assert!(h.is_inline());

    let mut h = HipVec::<u8, Arc>::from([42; 42]);
    let h2 = h.clone();
    h.truncate(10);
    assert_eq!(h.len(), 10);
    assert_eq!(h.as_slice(), &[42; 10]);
    assert!(h.is_thin());
    assert_eq!(h2.as_slice(), &[42; 42]);
    assert!(h2.is_thin());
    assert_eq!(h2.as_ptr(), h.as_ptr());
}
