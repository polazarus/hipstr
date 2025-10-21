//! Vector types.

pub mod fat;
pub mod hip;
pub mod inline;
pub(crate) mod reprs;
pub mod thin;

use crate::backend;

pub type ThinVec<T> = self::thin::ThinVec<T, self::thin::Reserved>;

/// An inline vector that can store up to `L` bytes inline.
pub type InlineVec<T, L = self::hip::Bytes> = self::inline::InlineVec<T, L>;

/// A possibly reference-counted thin vector
#[cfg(target_has_atomic = "ptr")]
pub type SmartThinVec<T> = self::thin::SmartThinVec<T, backend::Arc>;

/// A hip vector that uses `Arc` as the backend.
#[cfg(target_has_atomic = "ptr")]
pub type HipVec<'a, T> = hip::HipVec<'a, T, backend::Arc>;
