//! Next-generation core, ported from the `hipvec` branch (copy-only).
//!
//! Temporary home: this tree lives beside the current implementation until
//! phase 3 of `PLAN.md` rebuilds the public types on top of it.

//! Doc examples are `ignore`d: they refer to items that are not public yet.

#![allow(dead_code, unused_imports, unused_macros, unreachable_pub)]

pub mod backend;
pub mod common;
pub mod inline;
pub mod thin;
pub mod traits;
