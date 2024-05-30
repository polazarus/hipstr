//! Unstable allocated backend trait and the built-in implementations.

// #[cfg(not(feature = "unstable"))]
pub mod rc;

/// Use a local reference counted backend.
pub use rc::Local;
/// Shared (thread-safe) reference counted backend.
#[cfg(target_has_atomic = "ptr")]
pub use rc::ThreadSafe;

/// Sealed marker trait for allocated backend.
// #[cfg(not(feature = "unstable"))]
pub trait Backend: rc::Count + 'static {}

// #[cfg(not(feature = "unstable"))]
impl Backend for Local {}

// #[cfg(not(feature = "unstable"))]
#[cfg(target_has_atomic = "ptr")]
impl Backend for ThreadSafe {}
