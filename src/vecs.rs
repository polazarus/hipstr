//! Vector types.

pub mod inline;
pub mod thin;

#[doc(inline)]
pub use inline::InlineVec;

pub type ThinVec<T> = thin::ThinVec<T, thin::Reserved>;
