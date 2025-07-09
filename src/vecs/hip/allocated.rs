use crate::vecs::SmartVec;
use crate::Backend;

#[repr(C)]
pub struct Allocated<T, B: Backend> {
    pub owner: SmartVec<T, B>,
    pub ptr: *const T,
    pub len: usize,
}

impl<T, B: Backend> Allocated<T, B> {
    pub fn new(owner: SmartVec<T, B>) -> Self {
        Self {
            ptr: owner.as_ptr(),
            len: owner.len(),
            owner,
        }
    }
}
