//! Internal representation for wide vectors.

use core::ptr::NonNull;

use crate::vecs::reprs::MagicPointer;

/// An indirect wide vector representation.
pub type WideRepr<T, P> = MagicPointer<WideInner<T, P>>;

/// A wide vector representation with prefix.
#[repr(C)]
pub struct WideInner<T, P> {
    /// Prefix.
    pub prefix: P,
    /// Pointer to the data.
    pub ptr: NonNull<T>,
    /// Capacity.
    pub cap: usize,
    /// Length.
    pub len: usize,
}
