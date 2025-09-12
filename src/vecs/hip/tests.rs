use alloc::boxed::Box;

use crate::vecs::hip::HipVec;
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
