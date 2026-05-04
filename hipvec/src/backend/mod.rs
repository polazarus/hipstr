//! Backend traits for smart pointers and the built-in implementations.

use core::marker::PhantomData;

#[cfg(target_has_atomic = "ptr")]
mod arc;
mod rc;
mod unique;

mod seal {
    /// Sealed trait for internal use.
    pub trait Sealed {}
}

#[cfg(test)]
pub mod tests;

use self::seal::Sealed;

#[cfg(target_has_atomic = "ptr")]
pub use arc::*;
pub use rc::Count;
pub use unique::One;

use const_default::ConstDefault;

#[cfg(target_has_atomic = "ptr")]
pub type Arc = BackendImpl<AtomicCount, PanicOnOverflow>;

pub type Rc = BackendImpl<Count, PanicOnOverflow>;

pub type Unique = BackendImpl<One, CloneOnOverflow>;

/// Sealed marker trait for allocated backend.
pub trait Backend: Sealed + 'static {
    type Counter: Counter;
    type OverflowBehavior: OverflowBehavior;
}

impl<C: Counter, B: OverflowBehavior> Backend for BackendImpl<C, B> {
    type Counter = C;
    type OverflowBehavior = B;
}

#[derive(Clone, Copy, Debug)]
pub struct BackendImpl<C: Counter, B: OverflowBehavior>(pub(crate) C, PhantomData<B>);

impl<C: Counter, B: OverflowBehavior> Sealed for BackendImpl<C, B> {}

impl<C: Counter, B: OverflowBehavior> ConstDefault for BackendImpl<C, B> {
    const DEFAULT: Self = Self(C::DEFAULT, PhantomData);
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

/// Counter update result.
#[must_use]
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
///
/// # Safety
///
/// Implementors of this trait must ensure that the counter behaves correctly
/// according to the semantics described in each method's documentation. This
/// includes proper handling of increments and decrements, as well as ensuring
/// that the `get` and `set` methods reflect the current state of the counter
/// accurately. Failure to uphold these guarantees may lead to undefined
/// behavior in smart pointer implementations that rely on this trait.
pub unsafe trait Counter: ConstDefault + 'static {
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
