//! Unstable allocated backend trait and the built-in implementations.

// #[cfg(not(feature = "unstable"))]
pub mod smart;

/// Use a unique refrence.
pub use smart::Unique;

/// Use a local reference counted backend.
pub use smart::Local;

/// Shared (thread-safe) reference counted backend.
#[cfg(target_has_atomic = "ptr")]
pub use smart::ThreadSafe;

/// Sealed marker trait for allocated backend.
pub trait Backend: smart::SealedBackend + 'static {}

impl Backend for Local {}

#[cfg(target_has_atomic = "ptr")]
impl Backend for ThreadSafe {}
