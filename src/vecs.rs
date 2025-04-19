//! Vector types.

pub mod inline;
pub mod smart_thin;
pub mod thin;

#[doc(inline)]
pub use inline::InlineVec;

pub type ThinVec<T> = thin::ThinVec<T, thin::Reserved>;

#[doc(inline)]
pub use smart_thin::SmartThinVec;
