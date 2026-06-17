pub(crate) mod base;
pub mod copy;
mod generic;
pub mod noncopy;

/// Representation of the owned, allocated vector.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OwnedRepr {
    /// Thin vector representation.
    Thin,

    /// Wide vector representation.
    Wide,
}

/// Representation of the hip vector.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Repr {
    /// Owned, allocated vector.
    Owned(OwnedRepr),

    /// Borrowed slice.
    Borrowed,

    /// Owned, inline vector.
    Inline,
}

pub use copy::HipVec as CopyHipVec;
pub use noncopy::HipVec;
