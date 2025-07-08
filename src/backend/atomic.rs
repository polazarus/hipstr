#[cfg(not(loom))]
use core::sync::atomic::{fence, AtomicUsize, Ordering};

#[cfg(loom)]
use loom::sync::atomic::{fence, AtomicUsize, Ordering};

use super::{BackendImpl, Counter, PanicOnOverflow, Sealed, UpdateResult};

/// Atomic counter backend.
pub type Arc = BackendImpl<AtomicCount, PanicOnOverflow>;

#[deprecated(note = "renamed to Arc")]
pub type ThreadSafe = Arc;

/// Atomic (thread-safe) counter.
pub struct AtomicCount(pub(crate) AtomicUsize);

impl Sealed for AtomicCount {}

impl Counter for AtomicCount {
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
        if value == 0 {
            panic!("invalid counter value");
        }
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

impl Default for AtomicCount {
    #[inline]
    fn default() -> Self {
        Self(AtomicUsize::new(0))
    }
}
