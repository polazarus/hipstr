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
//! let simple_greetings = HipStr::from_static("Hello world");
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
//! where `B` is a backend among `ThreadSafe` ([`Arc<Vec<u8>>`](std::sync::Arc)) and `Local` ([`Rc<Vec<u8>>`](std::rc::Rc))
//!
//! The crate root provides aliases with `B` fixed to `ThreadSafe`.
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
//! The shared reference can be [`Local`] or [`ThreadSafe`].
//! Default aliases in the root of the library use [`ThreadSafe`].
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
