use core::cell::Cell;

use const_default::ConstDefault;

use super::*;

pub type PanickyUnique = BackendImpl<Unique, true>;

pub type BoundedRc<const MAX: usize> = BackendImpl<BoundedCount<MAX>, true>;

#[repr(C)]
pub struct BoundedCount<const MAX: usize>(Cell<usize>);

impl<const MAX: usize> InitPrefix for BoundedCount<MAX> {
    fn init() -> Self {
        Self::DEFAULT
    }
}

impl<const MAX: usize> ConstDefault for BoundedCount<MAX> {
    const DEFAULT: Self = Self(Cell::new(1));
}

impl<const MAX: usize> Sealed for BoundedCount<MAX> {}

unsafe impl<const MAX: usize> Counter for BoundedCount<MAX> {
    #[inline]
    fn incr(&self) -> UpdateResult {
        let val = self.0.get();
        if val == MAX {
            UpdateResult::Overflow
        } else {
            self.0.set(val + 1);
            UpdateResult::Done
        }
    }

    #[inline]
    fn decr(&self) -> UpdateResult {
        let val = self.0.get();
        if val == 1 {
            UpdateResult::Overflow
        } else {
            self.0.set(val - 1);
            UpdateResult::Done
        }
    }

    #[inline]
    fn is_unique(&self) -> bool {
        self.0.get() == 1
    }
}
