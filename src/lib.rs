//! Yet another **string type** for Rust 🦀
//!
//! * no copy and `const` **literal wrapping**
//! * no alloc **small strings** (23 bytes on 64-bit platform)
//! * no copy **owned slices**
//! * **zero dependency**, except for optional `serde` support
//!
//! And **byte strings** too!
//!
//! # Examples
//!
//! ```rust
//! use hipstr::HipStr;
//!
//! let simple_greetings = HipStr::borrowed("Hello world");
//! let clone = simple_greetings.clone(); // no copy
//! std::thread::spawn(move || { println!("{}", clone); });
//!
//! let user = "John";
//! let greetings = HipStr::from(format!("Hello {}", user));
//! let user = greetings.slice(6..); // no copy
//! drop(greetings); // the slice is _owned_, it exits even if greetings disappear
//!
//! let chars = user.chars().count(); // "inherits" `&str` methods
//! ```
//!
//! # Two Types
//!
//! - [`HipByt<B>`](crate::bytes::HipByt) \
//!   a replacement for both `Vec<u8>` and `[u8]`
//! - [`HipStr<B>`](crate::string::HipStr) \
//!   a replacement for both `String` and `str`
//!
//! where `B` is a backend, see below.
//!
//! # Three Representations
//!
//! Each type has three distinct representations:
//!
//! - Static borrow, constructed with [`HipStr::from_static`] or
//!   [`HipByt::from_static`]
//! - Inline sequence (up to [`HipByt::inline_capacity()`])
//! - Shared reference (cheaply clonable) _and slice_ (sliceable)
//!
//! The shared reference can be thread-safe or not, depending on the backend.
//!
//! ## ⚠️ Warning!
//!
//! The used representation of the empty string is **unspecified** and may change between patch versions!
//! It may be *borrowed* or *inlined* but will never be allocated.
//!
//! # Two Backends
//!
//! The crate provides two backends:
//!
//! - `ThreadSafe` ([`Arc<Vec<u8>>`](std::sync::Arc)),
//! - `Local` ([`Rc<Vec<u8>>`](std::rc::Rc)).
//!
//! The crate root also provides some convenience type aliases:
//!
//! - `hipstr::HipByt` and `hipstr::HipStr` that set `B` to `ThreadSafe`,
//! - `hipstr::LocalHipByt` and `hipstr::LocalHipStr` that set `B` to `Local`.
//!
//! # Platform Support
//!
//! This crate is only supported on platforms where:
//!
//! - pointers have the same memory size has `usize`
//! - pointer alignment requirement is strictly greater than 1
//!
//! For now, most common architectures are like that. However, `hipstr` will not
//! work on new and future architectures relying on large tagged pointers
//! (e.g. CHERI 128-bit pointers).

#![cfg_attr(not(feature = "std"), no_std)]
#![warn(clippy::pedantic, clippy::nursery, clippy::cargo)]
#![warn(unsafe_op_in_unsafe_fn)]

#[cfg(not(feature = "std"))]
pub(crate) extern crate alloc;

#[cfg(feature = "std")]
pub(crate) use std as alloc;

mod backend;
pub mod bytes;
mod raw;
pub mod string;

pub use backend::{Backend, Local, ThreadSafe};

/// Thread-safe shared byte sequence.
pub type HipByt<'borrow> = bytes::HipByt<'borrow, ThreadSafe>;

/// Thread-safe shared string.
pub type HipStr<'borrow> = string::HipStr<'borrow, ThreadSafe>;

/// Thread-local byte sequence.
pub type LocalHipByt<'borrow> = bytes::HipByt<'borrow, Local>;

/// Thread-local string.
pub type LocalHipStr<'borrow> = string::HipStr<'borrow, Local>;
