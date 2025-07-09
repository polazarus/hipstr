use super::*;
use crate::backend::Arc;

#[test]
fn from_array() {
    let hip_vec = HipVec::<u8, Arc>::from_array([1, 2, 3]);
    assert!(hip_vec.is_inline());
}
