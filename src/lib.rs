//! Yet another **string type** for Rust 🦀
//!
//! * no copy and `const` **literal wrapping**
//! * no alloc **small strings** (_23 bytes_ on 64-bit platform)
//! * no copy **owned slices**
//! * a niche: `Option<HipStr>` and `HipStr` have the same size
//! * **zero dependency**, except for optional `serde` support
//!
//! Also byte strings, OS strings, paths, too!
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
//! drop(greetings); // the slice is _owned_, it exists even if greetings disappear
//!
//! let chars = user.chars().count(); // "inherits" `&str` methods
//! ```
//!
//! # Three Representations
//!
//! Each type has three distinct representations:
//!
//! - Borrowed slice
//! - Inline sequence (up to [`HipByt::inline_capacity()`])
//! - Shared reference (cheaply clonable) _and slice_ (sliceable)
//!
//! The shared reference can be thread-safe or not, depending on the backend.
//!
//! Most operations keep string **normalized**, that is, if the string is not
//! borrowed, the inline representation is preferred when possible.
//!
//! ## ⚠️ Warning!
//!
//! The used representation of the empty string is **unspecified** and may
//! change between patch versions! It may be _borrowed_ or _inlined_ but will
//! never be allocated.
//!
//! # Two Backends
//!
//! The crate provides two backends:
//!
//! - `ThreadSafe` (atomic reference counting),
//! - `Local` (reference counting).
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
//! - pointers have the same memory size as `usize`,
//! - pointer alignment requirement is strictly greater than **2**.
//!
//! For now, most common architectures are like that. However, `hipstr` will not
//! work on new and future architectures relying on large tagged pointers (e.g.
//! CHERI 128-bit pointers).
//!
//! # Features
//!
//! * `std` (default): uses `std` rather than `core` and `alloc`, and also
//!   provides more trait implementations (for comparison, conversions)
//! * `serde`: provides serialization/deserialization support with `serde` crate
//! * `bstr`: provides compatibility with [BurntSushi's bstr
//!   crate](https://github.com/BurntSushi/bstr) make `HipByt` deref to
//!   [`&bstr::BStr`](bstr::BStr) rather than [`&[u8]`](slice)
//! * `unstable`: do nothing, used to reveal unstable implementation details

#![cfg_attr(coverage_nightly, feature(coverage_attribute))]
#![cfg_attr(docsrs, feature(doc_auto_cfg))]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(not(feature = "std"), no_std)]
#![warn(clippy::pedantic, clippy::nursery, clippy::cargo)]
#![warn(unsafe_op_in_unsafe_fn)]

pub(crate) extern crate alloc;
pub(crate) mod backend;
pub mod bytes;
pub(crate) mod macros;
pub(crate) mod smart;
pub mod string;

#[cfg(feature = "std")]
pub mod os_string;
#[cfg(feature = "std")]
pub mod path;

#[cfg(test)]
pub mod tests;

pub use backend::*;

/// Thread-safe shared byte sequence.
pub type HipByt<'borrow> = bytes::HipByt<'borrow, Arc>;

/// Thread-safe shared string.
pub type HipStr<'borrow> = string::HipStr<'borrow, Arc>;

/// Thread-safe shared string.
#[cfg(feature = "std")]
pub type HipOsStr<'borrow> = os_string::HipOsStr<'borrow, Arc>;

/// Thread-safe shared path.
#[cfg(feature = "std")]
pub type HipPath<'borrow> = path::HipPath<'borrow, Arc>;

/// Thread-local shared byte sequence.
pub type LocalHipByt<'borrow> = bytes::HipByt<'borrow, Rc>;

/// Thread-local shared string.
pub type LocalHipStr<'borrow> = string::HipStr<'borrow, Rc>;

/// Thread-local shared byte sequence.
#[cfg(feature = "std")]
pub type LocalHipOsStr<'borrow> = os_string::HipOsStr<'borrow, Rc>;

/// Thread-local shared path.
#[cfg(feature = "std")]
pub type LocalHipPath<'borrow> = path::HipPath<'borrow, Rc>;
