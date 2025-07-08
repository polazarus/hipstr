use alloc::vec;

use super::*;

#[test]
fn vector_vec() {
    let vec = vec![1, 2, 3];
    let cap = vec.capacity();
    let ptr = vec.as_ptr();
    let len = vec.len();

    test_mut_vector(vec, cap, len, ptr);
}

#[track_caller]
pub fn test_mut_vector<T>(mut v: impl MutVector<Item = T>, cap: usize, len: usize, ptr: *const T) {
    assert_eq!(v.len(), 3);

    assert_eq!(v.capacity(), cap);

    assert_eq!(v.as_slice().len(), len);
    assert_eq!(v.as_slice().as_ptr(), ptr);

    assert_eq!(v.as_mut_slice().len(), len);
    assert_eq!(v.as_mut_slice().as_ptr(), ptr);

    assert_eq!(v.as_ptr(), ptr);
    assert_eq!(v.as_mut_ptr().cast_const(), ptr);
    assert_eq!(v.as_non_null().as_ptr().cast_const(), ptr);
}
