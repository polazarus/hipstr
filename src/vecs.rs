//! Vector types.

use alloc::vec::Vec;

use crate::smart::Smart;

pub mod inline;
pub mod smart;
pub mod smart_thin;
pub mod thin;

#[doc(inline)]
pub use inline::InlineVec;
#[doc(inline)]
pub use smart::SmartVec;
#[doc(inline)]
pub use smart_thin::SmartThinVec;

pub type ThinVec<T> = thin::ThinVec<T, thin::Reserved>;

pub type SmartFatVec<T, C> = Smart<Vec<T>, C>;
