//! Sealed backend traits and the built-in implementations.

use core::cell::Cell;
use core::marker::PhantomData;
use core::panic::RefUnwindSafe;

use crate::common::traits::sealed::Sealed;

#[cfg(target_has_atomic = "ptr")]
mod atomic;

#[cfg(target_has_atomic = "ptr")]
pub use atomic::*;

pub type Rc = BackendImpl<Count, PanicOnOverflow, CloneOnInlineClone>;

pub type Unique = BackendImpl<(), CloneOnOverflow, CloneOnInlineClone>;

#[deprecated(note = "renamed to Rc")]
pub type Local = Rc;

/// Sealed marker trait for allocated backend.
pub trait Backend: Counter + 'static {}

impl<C: Counter, B: 'static, I: 'static> Backend for BackendImpl<C, B, I> {}

#[cfg(test)]
pub type PanickyUnique = BackendImpl<Unique, PanicOnOverflow, PanicOnInlineClone>;

#[derive(Clone, Copy, Debug)]
pub struct BackendImpl<C: Counter, B, I>(pub(crate) C, PhantomData<(B, I)>);

impl<C: Counter, B, I> Sealed for BackendImpl<C, B, I> {}

impl<C: Counter, B, I> Default for BackendImpl<C, B, I> {
    #[inline]
    fn default() -> Self {
        Self(C::default(), PhantomData)
    }
}

impl<C: Counter, B: 'static, I: 'static> Counter for BackendImpl<C, B, I> {
    #[inline]
    fn incr(&self) -> UpdateResult {
        self.0.incr()
    }

    #[inline]
    fn decr(&self) -> UpdateResult {
        self.0.decr()
    }

    #[inline]
    #[cfg(test)]
    #[cfg_attr(coverage_nightly, coverage(off))]
    fn get(&self) -> usize {
        self.0.get()
    }

    #[inline]
    #[cfg(test)]
    #[cfg_attr(coverage_nightly, coverage(off))]
    fn set(&self, value: usize) {
        self.0.set(value)
    }

    #[inline]
    fn is_unique(&self) -> bool {
        self.0.is_unique()
    }
}

/// Overflow behavior for smart pointers.
///
/// This trait is sealed and cannot be implemented outside this crate.
pub trait OverflowBehavior: Sealed + 'static {}

/// Clone on overflow behavior for the smart pointer.
///
/// This is the behavior intended for [`Unique`].
///
/// [`Unique`]: crate::Unique
pub struct CloneOnOverflow(PhantomData<()>);

impl Sealed for CloneOnOverflow {}

impl OverflowBehavior for CloneOnOverflow {}

/// Panic on overflow behavior for the smart pointer.
///
/// This is the usual behavior for [`Arc`] and [`Rc`].
///
/// [`Arc`]: crate::Arc
/// [`Rc`]: crate::Rc
pub struct PanicOnOverflow(PhantomData<()>);

impl Sealed for PanicOnOverflow {}

impl OverflowBehavior for PanicOnOverflow {}

/// Local (thread-unsafe) counter.
pub struct Count(pub(crate) Cell<usize>);

/// Counter update result.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum UpdateResult {
    /// The update was successful.
    Done,
    /// No update was performed because the counter has already reached a boundary.
    Overflow,
}

/// Trait for a basic reference counter.
///
/// This trait is sealed and cannot be implemented outside this crate.
pub trait Counter: Sealed + Default + 'static {
    /// Tries to increment the counter.
    ///
    /// In case of atomics, the [`Ordering::Release`] semantics is expected on the write.
    ///
    /// [`Ordering::Release`]: core::sync::atomic::Ordering
    fn incr(&self) -> UpdateResult;

    /// Tries to decrement the counter.
    ///
    /// In case of atomics, the [`Ordering::Release`] semantics is expected on the write.
    ///
    /// [`Ordering::Release`]: core::sync::atomic::Ordering
    fn decr(&self) -> UpdateResult;

    /// Returns the current value of the counter.
    ///
    /// In case of atomics, the [`Ordering::Acquire`] semantics is expected.
    ///
    /// [`Ordering::Acquire`]: core::sync::atomic::Ordering
    #[cfg(test)]
    fn get(&self) -> usize;

    /// Sets the current value of the counter.
    ///
    /// In case of atomics, the [`Ordering::Release`] semantics is expected.
    ///
    /// [`Ordering::Release`]: core::sync::atomic::Ordering
    #[cfg(test)]
    fn set(&self, value: usize);

    /// Checks if the counter is at one.
    ///
    /// In case of atomics, the [`Ordering::Acquire`] semantics is expected.
    ///
    /// [`Ordering::Acquire`]: core::sync::atomic::Ordering
    fn is_unique(&self) -> bool;
}

impl Sealed for () {}

impl Counter for () {
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
        if value != 1 {
            panic!("invalid counter value");
        }
    }

    #[inline]
    fn is_unique(&self) -> bool {
        true
    }
}

impl Sealed for Count {}

impl Counter for Count {
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
        if value == 0 {
            panic!("invalid counter value");
        }
        self.0.set(value - 1);
    }

    #[inline]
    fn is_unique(&self) -> bool {
        self.0.get() == 0
    }
}

impl Default for Count {
    #[inline]
    fn default() -> Self {
        Self(Cell::new(0))
    }
}

impl RefUnwindSafe for Count {}

pub trait InlineBehavior: Sealed + 'static {}

pub struct CloneOnInlineClone(PhantomData<()>);
pub struct PanicOnInlineClone(PhantomData<()>);

impl Sealed for CloneOnInlineClone {}
impl InlineBehavior for CloneOnInlineClone {}

impl Sealed for PanicOnInlineClone {}
impl InlineBehavior for PanicOnInlineClone {}
