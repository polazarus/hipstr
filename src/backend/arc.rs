#[cfg(not(loom))]
use core::sync::atomic::{AtomicUsize, Ordering, fence};

#[cfg(not(loom))]
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

        #[allow(deprecated, reason = "renamed `try_update`, which loom lacks")]
        match self.0.fetch_update(set_order, fetch_order, |old| {
            (old < usize::MAX - 1).then_some(old + 1)
        }) {
            Ok(_) => UpdateResult::Done,
            Err(_) => UpdateResult::Overflow,
        }
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

impl super::InitPrefix for AtomicCount {
    #[inline]
    fn init() -> Self {
        Self(AtomicUsize::new(0))
    }
}

#[cfg(not(loom))]
impl ConstDefault for AtomicCount {
    #[allow(clippy::declare_interior_mutable_const)]
    const DEFAULT: Self = Self(AtomicUsize::new(0));
}
