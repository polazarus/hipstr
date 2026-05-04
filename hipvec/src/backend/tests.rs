use core::cell::Cell;

use const_default::ConstDefault;

use super::*;

pub type PanickyUnique = BackendImpl<Unique, PanicOnOverflow>;

pub type BoundedRc<const MAX: usize> = BackendImpl<BoundedCount<MAX>, PanicOnOverflow>;

pub struct BoundedCount<const MAX: usize>(Cell<usize>);

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
    fn get(&self) -> usize {
        self.0.get()
    }

    #[inline]
    fn set(&self, value: usize) {
        self.0.set(value);
    }

    #[inline]
    fn is_unique(&self) -> bool {
        self.0.get() == 1
    }
}
