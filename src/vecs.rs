//! Vector types.

use alloc::vec::Vec;

use crate::smart::Smart;

pub mod hip;
pub mod inline;
pub mod smart;
pub mod smart_thin;
pub mod thin;

#[doc(inline)]
pub use self::hip::HipVec;
#[doc(inline)]
pub use self::inline::InlineVec;
#[doc(inline)]
pub use self::smart::SmartVec;
#[doc(inline)]
pub use self::smart_thin::SmartThinVec;

pub type ThinVec<T> = thin::ThinVec<T, thin::Reserved>;

pub type SmartFatVec<T, C> = Smart<Vec<T>, C>;

pub(crate) const TAG_INLINE: u8 = 0b0000_0001;
pub(crate) const TAG_THIN: u8 = 0b0000_0010;
pub(crate) const TAG_FAT: u8 = 0b0000_0011;
pub(crate) const TAG_BORROWED: u8 = 0b1111_1100;
pub(crate) const TAG_BORROWED_MASKED: u8 = 0b0000_0000;

pub(crate) const TAG_MASK: u8 = 0b0000_0011;
pub(crate) const TAG_SHIFT: u8 = 2;
