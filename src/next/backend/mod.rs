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

#[cfg(target_has_atomic = "ptr")]
pub use arc::*;
use const_default::ConstDefault;
pub use rc::Count;
pub use unique::One;

use self::seal::Sealed;

#[cfg(target_has_atomic = "ptr")]
pub type Arc = BackendImpl<AtomicCount, true>;

pub type Rc = BackendImpl<Count, true>;

pub type Unique = BackendImpl<One, false>;

/// Sealed marker trait for allocated backend.
pub trait Backend: Sealed + 'static {
    /// The counter type.
    type Counter: Counter;

    /// Whether to panic when the counter overflows.
    const PANIC_ON_OVERFLOW: bool;
}

/// Actual backend configuration type.
#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct BackendImpl<C: Counter, const PANIC_ON_OVERFLOW: bool>(PhantomData<C>);

impl<C: Counter, const PANIC_ON_OVERFLOW: bool> Backend for BackendImpl<C, PANIC_ON_OVERFLOW> {
    type Counter = C;

    const PANIC_ON_OVERFLOW: bool = PANIC_ON_OVERFLOW;
}

impl<C: Counter, const PANIC_ON_OVERFLOW: bool> Sealed for BackendImpl<C, PANIC_ON_OVERFLOW> {}

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
