#![no_std]

#[cfg(feature = "std")]
extern crate std;

#[cfg(feature = "alloc")]
extern crate alloc;

pub mod backend;
pub mod common;
pub mod hip;
pub mod inline;
pub mod thin;
pub mod traits;

#[cfg(target_has_atomic = "ptr")]
pub use backend::Arc;
pub use backend::{Rc, Unique};
