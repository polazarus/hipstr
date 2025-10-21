//! Internal representation for fat vectors.

use core::ptr::NonNull;

use crate::vecs::reprs::MagicPointer;

/// An indirect fat vector representation.
pub type FatRepr<T, P> = MagicPointer<FatInner<T, P>>;

/// A fat vector representation with prefix.
#[repr(C)]
pub struct FatInner<T, P> {
    /// Prefix.
    pub prefix: P,
    /// Pointer to the data.
    pub ptr: NonNull<T>,
    /// Capacity.
    pub cap: usize,
    /// Length.
    pub len: usize,
}
