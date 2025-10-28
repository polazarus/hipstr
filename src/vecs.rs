//! Vector types.
//!
//! In addition to hip vectors, this module contains various vector types:
//!
//! - thin vectors,
//! - inline vectors,
//! - thin handles to wide vectors.
//!
//! They are not intended to be used directly but rather through the hip
//! vectors. But they may be interesting for advanced use cases.

pub mod hip;
pub mod inline;
pub(crate) mod reprs;
pub mod thin;
pub mod wide;

use crate::backend;

/// A thin vector.
pub type ThinVec<T> = self::thin::ThinVec<T, self::thin::Reserved>;

/// An inline vector with the same size as `HipVec`.
pub type InlineVec<T> = self::inline::InlineVec<T, self::hip::Bytes>;

/// A hip vector that uses `Arc` as the backend.
#[cfg(target_has_atomic = "ptr")]
pub type HipVec<'a, T> = hip::HipVec<'a, T, backend::Arc>;
