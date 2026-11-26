//! Next-generation core, ported from the `hipvec` branch (copy-only).
//!
//! Temporary home: this tree lives beside the current implementation until
//! phase 3 of `PLAN.md` rebuilds the public types on top of it.

//! Doc examples are `ignore`d: they refer to items that are not public yet.

#![allow(dead_code, unused_imports, unused_macros, unreachable_pub)]

pub mod backend;
#[cfg(feature = "borsh")]
mod borsh;
#[cfg(feature = "bstr")]
mod bstr;
pub mod bytes;
pub mod common;
pub mod enc;
mod family;
pub mod hip;
pub mod inline;
#[cfg(feature = "std")]
pub mod os_string;
#[cfg(feature = "std")]
pub mod path;
pub mod pattern;
pub mod repr;
#[cfg(feature = "serde")]
pub mod serde;
pub mod slice;
pub mod string;
mod string_pattern;
pub mod thin;
pub mod traits;

#[cfg(test)]
mod tests;

pub use backend::{Arc, Backend, Rc, Unique};
pub use hip::Hip;

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
        pub type $wide<'a, B> = $crate::next::hip::Hip<$enc, $crate::next::repr::Wide<'a, u8, B>>;
        #[doc = concat!("2-word ", $what, ": inline, borrowed or shared.")]
        pub type $small<'a, B> = $crate::next::hip::Hip<$enc, $crate::next::repr::Small<'a, u8, B>>;
        #[doc = concat!("1-word ", $what, ": inline or shared (no borrowing).")]
        pub type $tiny<B> = $crate::next::hip::Hip<$enc, $crate::next::repr::Tiny<u8, B>>;
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
