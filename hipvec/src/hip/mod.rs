pub(crate) mod base;
pub mod copy;
pub mod noncopy;

/// Representation of the owned, allocated vector.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Owned {
    /// Thin vector representation.
    Thin,

    /// Wide vector representation.
    Wide,
}

/// Representation of the hip vector.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Repr {
    /// Owned, allocated vector.
    Owned(Owned),

    /// Borrowed slice.
    Borrowed,

    /// Owned, inline vector.
    Inline,
}
