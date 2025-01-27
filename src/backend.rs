//! Sealed backend trait and the built-in implementations.

#[cfg(target_has_atomic = "ptr")]
pub use crate::smart::Arc;
pub use crate::smart::{Rc, Unique};

#[deprecated(note = "renamed to Rc")]
pub type Local = crate::smart::Rc;

#[deprecated(note = "renamed to Arc")]
pub type ThreadSafe = crate::smart::Arc;

/// Sealed marker trait for allocated backend.
pub trait Backend: crate::smart::Kind + 'static {}

impl Backend for Rc {}

#[cfg(target_has_atomic = "ptr")]
impl Backend for Arc {}

impl Backend for Unique {}
