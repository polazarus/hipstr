//! Vector types.

pub mod hip;
pub mod inline;
pub(crate) mod reprs;
pub mod smart_fat;
pub mod smart_thin;
pub mod thin;

#[doc(inline)]
pub use inline::InlineVec;
#[doc(inline)]
pub use smart_thin::SmartThinVec;

use crate::backend;

pub type ThinVec<T> = thin::ThinVec<T, thin::Reserved>;
pub type HipVec<'a, T, B = backend::Arc> = hip::HipVec<'a, T, B>;
