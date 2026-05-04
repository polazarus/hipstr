use const_default::ConstDefault;

use super::{Counter, Sealed, UpdateResult};
use crate::common::ZeroUsize;

/// Fake counter for unique smart pointers.
#[repr(transparent)]
pub struct One(ZeroUsize);

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
    #[cfg(test)]
    #[cfg_attr(coverage_nightly, coverage(off))]
    fn get(&self) -> usize {
        1
    }

    #[inline]
    #[cfg(test)]
    #[cfg_attr(coverage_nightly, coverage(off))]
    fn set(&self, value: usize) {
        assert!(value != 1, "invalid counter value");
    }

    #[inline]
    fn is_unique(&self) -> bool {
        true
    }
}
