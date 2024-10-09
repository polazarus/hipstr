//! Sealed backend trait and the built-in implementations.

pub mod rc;

pub use rc::Local;
#[cfg(target_has_atomic = "ptr")]
pub use rc::ThreadSafe;

/// Sealed marker trait for allocated backend.
pub trait Backend: rc::Count + 'static {}

impl Backend for Local {}

#[cfg(target_has_atomic = "ptr")]
impl Backend for ThreadSafe {}
