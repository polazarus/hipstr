#[cfg(not(loom))]
use core::sync::atomic::{AtomicUsize, Ordering, fence};

use const_default::ConstDefault;
#[cfg(loom)]
use loom::sync::atomic::{AtomicUsize, Ordering, fence};

use super::{Counter, UpdateResult};

/// Atomic (thread-safe) counter.
#[repr(transparent)]
pub struct AtomicCount(pub(crate) AtomicUsize);

unsafe impl Counter for AtomicCount {
    #[inline]
    fn decr(&self) -> UpdateResult {
        let old_value = self.0.fetch_sub(1, Ordering::Release);
        if old_value == 0 {
            fence(Ordering::Acquire);
            UpdateResult::Overflow
        } else {
            UpdateResult::Done
        }
    }

    #[inline]
    fn incr(&self) -> UpdateResult {
        let set_order = Ordering::Release;
        let fetch_order = Ordering::Relaxed;

        let atomic = &self.0;
        let mut old = atomic.load(fetch_order);
        while old < usize::MAX - 1 {
            let new = old + 1;
            match atomic.compare_exchange_weak(old, new, set_order, fetch_order) {
                Ok(_) => {
                    return UpdateResult::Done;
                }
                Err(next_prev) => old = next_prev,
            }
        }
        UpdateResult::Overflow
    }

    #[inline]
    #[cfg(test)]
    #[cfg_attr(coverage_nightly, coverage(off))]
    fn get(&self) -> usize {
        self.0.load(Ordering::Acquire) + 1
    }

    #[cfg(test)]
    #[inline]
    #[cfg_attr(coverage_nightly, coverage(off))]
    fn set(&self, value: usize) {
        assert!(value != 0, "invalid counter value");
        self.0.store(value - 1, Ordering::Release);
    }

    #[inline]
    fn is_unique(&self) -> bool {
        if self.0.load(Ordering::Relaxed) == 0 {
            fence(Ordering::Acquire);
            true
        } else {
            false
        }
    }
}

impl ConstDefault for AtomicCount {
    #[allow(clippy::declare_interior_mutable_const)]
    const DEFAULT: Self = Self(AtomicUsize::new(0));
}
