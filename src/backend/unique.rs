use const_default::ConstDefault;

use super::{Counter, Sealed, UpdateResult};
use crate::common::ZeroUsize;

/// Fake counter for unique smart pointers.
#[repr(transparent)]
pub struct One(ZeroUsize);

impl super::InitPrefix for One {
    #[inline]
    fn init() -> Self {
        Self::DEFAULT
    }
}

impl ConstDefault for One {
    const DEFAULT: Self = Self(ZeroUsize::DEFAULT);
}

impl Sealed for One {}

unsafe impl Counter for One {
    #[inline]
    fn incr(&self) -> UpdateResult {
        UpdateResult::Overflow
    }
    #[inline]
    fn decr(&self) -> UpdateResult {
        UpdateResult::Overflow
    }

    #[inline]
    fn is_unique(&self) -> bool {
        true
    }
}
