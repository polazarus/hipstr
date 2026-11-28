//! Yet another **string type** for Rust 🦀
//!
//! * no copy and `const` **literal wrapping**
//! * no alloc **small strings** (up to _23 bytes_ on 64-bit platforms)
//! * no copy **owned slices**
//! * three sizes: 3 words, 2 words or a single word
//! * a niche: `Option<HipStr>` and `HipStr` have the same size
//!
//! Also byte strings, C strings, OS strings, paths, too!
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
//! # Three Sizes
//!
//! Each family (strings, byte strings, C strings, OS strings, paths) comes in
//! three sizes:
//!
//! | Size    | Types                              | Inline (64-bit) | Borrowed | O(1) slicing | Adopts `String`/`Vec` |
//! |---------|------------------------------------|-----------------|----------|--------------|-----------------------|
//! | 3 words | [`HipStr`], [`HipByt`], …          | 23 bytes        | yes      | yes          | yes                   |
//! | 2 words | [`SmallStr`], [`SmallByt`], …      | 15 bytes        | yes      | no           | no (copies)           |
//! | 1 word  | [`TinyStr`], [`TinyByt`], …        | 7 bytes         | no       | no           | no (copies)           |
//!
//! Every size has the same niche: `Option<T>` is as large as `T`.
//!
//! For values that never allocate, the [`inline`] module has fixed-capacity
//! types — [`InlineStr`], [`InlineByt`], [`InlineCStr`], … — with a mostly
//! `const` API and any capacity up to 254 bytes (`inline::InlineStr<N>`).
//!
//! # Representations
//!
//! A value is either
//!
//! - an inline sequence (up to `inline_capacity()` bytes),
//! - a borrowed slice (3- and 2-word types),
//! - or a shared heap buffer (cheaply clonable). The 3-word types may adopt a
//!   [`Vec`] without copying (`From<String>`, `From<Vec<u8>>`, …, and back with
//!   `into_string`, `into_vec`, …); the 2- and 1-word types always copy into
//!   their own buffer, which keeps their reads to a pointer and a length.
//!
//! The shared reference can be thread-safe or not, depending on the backend.
//!
//! Most operations keep values **normalized**, that is, if the value is not
//! borrowed, the inline representation is preferred when possible. Empty
//! values are always inline.
//!
//! [`Vec`]: alloc::vec::Vec
//!
//! # Three Backends
//!
//! The crate provides three backends:
//!
//! - `Arc` (atomic reference counting)
//! - `Rc` (reference counting)
//! - `Unique` (unique reference, clones copy)
//!
//! The crate root provides type aliases for the first two:
//!
//! - `hipstr::HipStr`, `hipstr::SmallStr`, `hipstr::TinyStr`, … with `Arc`,
//! - `hipstr::LocalHipStr`, `hipstr::LocalSmallStr`, … with `Rc`.
//!
//! Each family module also has backend-generic aliases, e.g.
//! [`string::HipStr<'a, B>`](string::HipStr).
//!
//! # Std Compatibility
//!
//! Each family mirrors the API of its std counterpart: `Vec<u8>`, `String`,
//! `CString`, `OsString`, `PathBuf` (and `bstr`'s `BString`). Inherent methods
//! have the same names and signatures (`insert`, `drain`, `splice`, `retain`,
//! `split_off`, `try_reserve`, `push` on paths, …), the borrowed type's
//! methods are reached through `Deref`, and the std trait impls (comparisons,
//! `Extend`, `FromIterator`, `From`/`TryFrom`, `fmt::Write`, `io::Write`,
//! `IntoIterator`, `Add`, …) are provided. Mutating methods are
//! copy-on-write: a borrowed or shared value is copied first. Bytes, `str` and
//! `BStr` values also dereference mutably, with the same copy-on-write
//! semantics.
//!
//! The few std methods that cannot apply (raw parts, allocator parameters,
//! `String::as_mut_vec`, …) are listed with the reason in the crate's
//! `compat/LEDGER.md`, which CI checks against std's rustdoc.
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
//!   provides more trait implementations (for comparison, conversions) and the
//!   OS string and path types
//! * `serde`: provides serialization/deserialization support with [`serde`](https://serde.rs)
//! * `borsh`: provides serialization/deserialization support with [`borsh`](https://borsh.io)
//! * `bstr`: provides compatibility with [BurntSushi's bstr
//!   crate](https://github.com/BurntSushi/bstr), and the [`HipBStr`],
//!   `SmallBStr` and `TinyBStr` byte strings, which dereference to
//!   `bstr::BStr`
//! * `unstable`: do nothing, used to reveal unstable implementation details

#![no_std]
#![cfg_attr(coverage_nightly, feature(coverage_attribute))]
#![cfg_attr(docsrs, feature(doc_auto_cfg))]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![warn(clippy::pedantic, clippy::nursery, clippy::cargo)]
#![warn(unsafe_op_in_unsafe_fn)]

extern crate alloc;
#[cfg(feature = "std")]
extern crate std;

pub mod backend;
#[cfg(feature = "bstr")]
pub mod bstr;
pub mod bytes;
pub mod cstr;
pub mod enc;
pub mod hip;
pub mod inline;
#[cfg(feature = "std")]
pub mod os_string;
#[cfg(feature = "std")]
pub mod path;
pub mod pattern;
mod repr;
pub mod slice;
pub mod string;

#[cfg(feature = "borsh")]
mod borsh_impl;
#[cfg(feature = "bstr")]
mod bstr_impl;
mod family;
#[cfg(feature = "serde")]
mod serde_impl;
mod std_traits;
mod string_ops;
mod string_pattern;
mod vec_ops;

// Internal vector machinery (ported from the `hipvec` branch, copy-only).
// Its doc examples are `ignore`d: the items are not public.
mod common;
mod inline_buf;
mod thin;

#[cfg(test)]
mod tests;

// compile-time thread-safety checks (doctests and a unit test)
#[cfg(any(test, doctest))]
mod thread_safety;

pub use backend::{Arc, Backend, Rc, Unique};
pub use hip::Hip;
pub use inline::{CapacityError, Inline};
pub use repr::Repr;

/// Inline string of up to 23 bytes (24 bytes in all); any capacity with
/// [`inline::InlineStr<N>`](inline::InlineStr).
pub type InlineStr = inline::InlineStr;
/// Inline byte string of up to 23 bytes; see [`inline::InlineByt<N>`](inline::InlineByt).
pub type InlineByt = inline::InlineByt;
/// Inline C string of up to 22 bytes and its NUL; see [`inline::InlineCStr<N>`](inline::InlineCStr).
pub type InlineCStr = inline::InlineCStr;
/// Inline `bstr` byte string of up to 23 bytes; see [`inline::InlineBStr<N>`](inline::InlineBStr).
#[cfg(feature = "bstr")]
pub type InlineBStr = inline::InlineBStr;
/// Inline OS string of up to 23 bytes; see [`inline::InlineOsStr<N>`](inline::InlineOsStr).
#[cfg(feature = "std")]
pub type InlineOsStr = inline::InlineOsStr;
/// Inline path of up to 23 bytes; see [`inline::InlinePath<N>`](inline::InlinePath).
#[cfg(feature = "std")]
pub type InlinePath = inline::InlinePath;

/// Declares the public aliases of one family: 3 sizes × {`Arc`, `Rc`}.
///
/// The backend is fixed (no default type parameter): defaults of type aliases
/// do not drive inference in expressions such as `HipStr::from("…")`. The
/// backend-generic aliases live in each family module.
macro_rules! aliases {
    ($m:ident, $wide:ident, $small:ident, $tiny:ident, $lwide:ident, $lsmall:ident, $ltiny:ident) => {
        #[doc = concat!("Thread-safe [`", stringify!($m), "::", stringify!($wide), "`] (`Arc` backend).")]
        pub type $wide<'a> = $m::$wide<'a, Arc>;
        #[doc = concat!("Thread-safe [`", stringify!($m), "::", stringify!($small), "`] (`Arc` backend).")]
        pub type $small<'a> = $m::$small<'a, Arc>;
        #[doc = concat!("Thread-safe [`", stringify!($m), "::", stringify!($tiny), "`] (`Arc` backend).")]
        pub type $tiny = $m::$tiny<Arc>;
        #[doc = concat!("Thread-local [`", stringify!($m), "::", stringify!($wide), "`] (`Rc` backend).")]
        pub type $lwide<'a> = $m::$wide<'a, Rc>;
        #[doc = concat!("Thread-local [`", stringify!($m), "::", stringify!($small), "`] (`Rc` backend).")]
        pub type $lsmall<'a> = $m::$small<'a, Rc>;
        #[doc = concat!("Thread-local [`", stringify!($m), "::", stringify!($tiny), "`] (`Rc` backend).")]
        pub type $ltiny = $m::$tiny<Rc>;
    };
}

/// Declares the backend-generic aliases of one family, in its module.
macro_rules! generic_aliases {
    ($enc:ty, $wide:ident, $small:ident, $tiny:ident, $what:literal) => {
        #[doc = concat!("3-word ", $what, ": inline, borrowed or shared, with O(1) slicing.")]
        pub type $wide<'a, B> = $crate::hip::Hip<$enc, $crate::repr::Wide<'a, B>>;
        #[doc = concat!("2-word ", $what, ": inline, borrowed or shared.")]
        pub type $small<'a, B> = $crate::hip::Hip<$enc, $crate::repr::Small<'a, B>>;
        #[doc = concat!("1-word ", $what, ": inline or shared (no borrowing).")]
        pub type $tiny<B> = $crate::hip::Hip<$enc, $crate::repr::Tiny<B>>;
    };
}
pub(crate) use generic_aliases;

aliases!(
    string,
    HipStr,
    SmallStr,
    TinyStr,
    LocalHipStr,
    LocalSmallStr,
    LocalTinyStr
);
aliases!(
    bytes,
    HipByt,
    SmallByt,
    TinyByt,
    LocalHipByt,
    LocalSmallByt,
    LocalTinyByt
);
#[cfg(feature = "bstr")]
aliases!(
    bstr,
    HipBStr,
    SmallBStr,
    TinyBStr,
    LocalHipBStr,
    LocalSmallBStr,
    LocalTinyBStr
);
aliases!(
    cstr,
    HipCStr,
    SmallCStr,
    TinyCStr,
    LocalHipCStr,
    LocalSmallCStr,
    LocalTinyCStr
);
#[cfg(feature = "std")]
aliases!(
    os_string,
    HipOsStr,
    SmallOsStr,
    TinyOsStr,
    LocalHipOsStr,
    LocalSmallOsStr,
    LocalTinyOsStr
);
#[cfg(feature = "std")]
aliases!(
    path,
    HipPath,
    SmallPath,
    TinyPath,
    LocalHipPath,
    LocalSmallPath,
    LocalTinyPath
);
