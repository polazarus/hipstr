#![no_std]

#[cfg(feature = "std")]
extern crate std;

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(feature = "alloc")]
pub mod backend;

pub mod common;

#[cfg(feature = "alloc")]
pub mod hip;

pub mod inline;

#[cfg(feature = "alloc")]
pub mod thin;

pub mod traits;

#[cfg(feature = "alloc")]
#[cfg(target_has_atomic = "ptr")]
pub use backend::Arc;
#[cfg(feature = "alloc")]
pub use backend::{Rc, Unique};
