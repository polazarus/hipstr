//! Cheaply clonable, sliceable, and mostly immutable string [`HipStr`] and byte
//! string [`HipByt`].
//!
//! # Representations
//!
//! Each type has three distinct representations:
//!
//! - Static borrow, constructed with [`HipStr::from_static`] or
//! [`HipByt::from_static`]
//! - Inline sequence (up to [`HipByt::inline_capacity()`])
//! - Shared reference (cheaply clonable) _and slice_ (sliceable)
//!
//! The shared reference can be [`Local`] ([`std::rc::Rc`]) or [`ThreadSafe`] ([`std::sync::Arc`]).
//! The default aliases in the root of the library use [`ThreadSafe`].
//!
//! # Platform support
//!
//! This crate is only supported on platform where:
//!
//! - pointers have the same memory size has `usize`
//! - the pointer alignment requirement is strictly greater than 1
//!
//! For now, most common architectures are like so. However, `hipstr` will not
//! work on new and future architectures relying on large tagged pointers
//! (e.g. CHERI 128-bit pointers).

#![warn(clippy::pedantic, clippy::nursery, clippy::cargo)]
#![warn(unsafe_op_in_unsafe_fn)]

mod backend;
pub mod bytes;
mod raw;
pub mod string;

pub use backend::{Backend, Local, ThreadSafe};

/// Thread-safe shared byte sequence.
pub type HipByt = bytes::HipByt<ThreadSafe>;

/// Thread-safe shared string.
pub type HipStr = string::HipStr<ThreadSafe>;

/// Thread-local byte sequence.
pub type LocalHipByt = bytes::HipByt<Local>;

/// Thread-local string.
pub type LocalHipStr = string::HipStr<Local>;
