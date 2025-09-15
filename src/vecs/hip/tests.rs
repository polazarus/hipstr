use alloc::boxed::Box;

use crate::vecs::hip::HipVec;
use crate::vecs::SmartThinVec;
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
