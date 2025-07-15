use super::*;
use crate::backend::Arc;

#[test]
fn from_array() {
    let hip_vec = HipVec::<u8, Arc>::from_array([1, 2, 3]);
    assert!(hip_vec.is_inline());
    assert_eq!(hip_vec.repr(), Repr::Inline);
    assert_eq!(hip_vec.len(), 3);
    assert_eq!(hip_vec.as_slice(), [1, 2, 3]);

    let hip_vec = HipVec::<u8, Arc>::from_array([1; 40]);
    assert!(!hip_vec.is_inline());
    assert_eq!(hip_vec.repr(), Repr::Thin);
    assert_eq!(hip_vec.len(), 40);
    assert_eq!(hip_vec.as_slice(), [1; 40]);
}
