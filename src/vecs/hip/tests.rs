use super::*;
use crate::backend::Arc;
use crate::vecs::inline::InlineVec;

#[test]
fn test_new_inline() {
    let inline_vec: InlineVec<u16, INLINE_BYTES> = InlineVec::new();
    assert!(inline_vec.is_empty());

    let hip_vec = HipVec::<_, Arc>::from_inline(inline_vec);
    assert!(hip_vec.is_inline());
}
