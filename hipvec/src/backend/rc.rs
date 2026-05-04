//! Non-atomic reference counting backend.

use core::cell::Cell;
use core::panic::RefUnwindSafe;

use const_default::ConstDefault;

use super::{Counter, UpdateResult};

/// Non-atomic (thread-unsafe) counter.
pub struct Count(pub(crate) Cell<usize>);

unsafe impl Counter for Count {
    #[inline]
    fn incr(&self) -> UpdateResult {
        self.0
            .get()
            .checked_add(1)
            .map_or(UpdateResult::Overflow, |new| {
                if new == usize::MAX {
                    return UpdateResult::Overflow;
                }
                self.0.set(new);
                UpdateResult::Done
            })
    }

    #[inline]
    fn decr(&self) -> UpdateResult {
        self.0
            .get()
            .checked_sub(1)
            .map_or(UpdateResult::Overflow, |new| {
                self.0.set(new);
                UpdateResult::Done
            })
    }

    #[inline]
    #[cfg(test)]
    #[cfg_attr(coverage_nightly, coverage(off))]
    fn get(&self) -> usize {
        // the count is strictly less than `usize::MAX`
        self.0.get() + 1
    }

    #[inline]
    #[cfg(test)]
    #[cfg_attr(coverage_nightly, coverage(off))]
    fn set(&self, value: usize) {
        assert!(value != 0, "invalid counter value");
        self.0.set(value - 1);
    }

    #[inline]
    fn is_unique(&self) -> bool {
        self.0.get() == 0
    }
}

impl ConstDefault for Count {
    #[allow(clippy::declare_interior_mutable_const)]
    const DEFAULT: Self = Self(Cell::new(0));
}

impl RefUnwindSafe for Count {}
