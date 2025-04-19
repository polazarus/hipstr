//! Sealed backend trait and the built-in implementations.

use crate::smart;
pub use crate::smart::{CloneOnOverflow, PanicOnOverflow};

#[cfg(target_has_atomic = "ptr")]
pub type Arc = PanicOnOverflow<smart::Arc>;

pub type Rc = PanicOnOverflow<smart::Rc>;

pub type Unique = CloneOnOverflow<smart::Unique>;

#[deprecated(note = "renamed to Rc")]
pub type Local = Rc;

#[deprecated(note = "renamed to Arc")]
pub type ThreadSafe = Arc;

/// Sealed marker trait for allocated backend.
pub trait Backend: crate::smart::SmartKind + 'static {}

impl Backend for Rc {}

#[cfg(target_has_atomic = "ptr")]
impl Backend for Arc {}

impl Backend for Unique {}
