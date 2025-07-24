//! Vector types.

use alloc::vec::Vec;

use crate::smart::Smart;
use crate::{macros, Backend};

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

impl<T, C: Backend> SmartFatVec<T, C> {
    /// Creates a new `SmartFatVec` with the specified capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self::new(Vec::with_capacity(capacity))
    }

    /// Returns the current capacity of the vector.
    pub const fn capacity(&self) -> usize {
        Self::get(self).capacity()
    }

    pub const fn len(&self) -> usize {
        Self::get(self).len()
    }

    pub const fn is_empty(&self) -> bool {
        Self::get(self).is_empty()
    }

    pub const fn as_ptr(&self) -> *const T {
        Self::get(self).as_ptr()
    }

    pub const fn as_vec(&self) -> &Vec<T> {
        Self::get(self)
    }
}

macros::trait_impls! {
    [T, B: Backend] {
        Vector {
            SmartFatVec<T, B> : T;
        }
    }
}
