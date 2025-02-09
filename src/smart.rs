//! Limited but generic smart pointer.
//!
//! This module provides a smart pointer that abstracts over its "kind":
//!
//! - unique,
//! - reference counted,
//! - atomically reference counted.

use alloc::boxed::Box;
use core::cell::Cell;
use core::mem::ManuallyDrop;
use core::ops::Deref;
use core::ptr::NonNull;
#[cfg(not(loom))]
use core::sync::atomic::{fence, AtomicUsize, Ordering};

#[cfg(loom)]
use loom::sync::atomic::{fence, AtomicUsize, Ordering};

#[cfg(test)]
mod tests;

/// Unique reference marker.
pub struct Unique(/* nothing but not constructible either */);

/// Local (thread-unsafe) reference counter.
pub struct Rc(Cell<usize>);

/// Atomic (thread-safe) reference counter.
#[cfg(target_has_atomic = "ptr")]
pub struct Arc(AtomicUsize);

/// Reference counting update result.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum UpdateResult {
    /// The update was successful.
    Done,
    /// No update was performed because the counter was already reaches a boundary.
    Overflow,
}

/// Trait for a basic reference counter.
pub trait Kind {
    /// Creates a new counter that starts at one.
    fn one() -> Self;

    /// Tries to increment the counter.
    fn incr(&self) -> UpdateResult;

    /// Tries to decrement the counter.
    fn decr(&self) -> UpdateResult;

    /// Returns the current value of the counter.
    fn get(&self) -> usize;

    /// Checks if the counter is at one.
    ///
    /// In case of atomics, the [`Ordering::Acquire`] semantics is expected.
    fn is_unique(&self) -> bool {
        self.get() == 1
    }
}

impl Kind for Unique {
    #[inline]
    fn one() -> Self {
        Self {}
    }
    #[inline]
    fn incr(&self) -> UpdateResult {
        UpdateResult::Overflow
    }
    #[inline]
    fn decr(&self) -> UpdateResult {
        UpdateResult::Overflow
    }
    #[inline]
    fn get(&self) -> usize {
        1
    }
}

impl Kind for Rc {
    #[inline]
    fn one() -> Self {
        Self(Cell::new(0))
    }

    #[inline]
    fn incr(&self) -> UpdateResult {
        let new = self.0.get() + 1;
        if new < usize::MAX {
            // usize::MAX is forbidden
            self.0.set(new);
            UpdateResult::Done
        } else {
            UpdateResult::Overflow
        }
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
    fn get(&self) -> usize {
        // the count is strictly less than `usize::MAX`
        self.0.get() + 1
    }
}

#[cfg(target_has_atomic = "ptr")]
impl Kind for Arc {
    #[inline]
    fn one() -> Self {
        Self(AtomicUsize::new(0))
    }

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
    fn get(&self) -> usize {
        self.0.load(Ordering::Relaxed) + 1
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

/// Smart pointer inner cell.
pub struct Inner<T, C>
where
    C: Kind,
{
    count: C,
    value: T,
}

impl<T, C> Clone for Inner<T, C>
where
    T: Clone,
    C: Kind,
{
    fn clone(&self) -> Self {
        Self {
            count: C::one(),
            value: self.value.clone(),
        }
    }
}

/// Basic smart pointer, with generic counter.
pub struct Smart<T, C>(NonNull<Inner<T, C>>)
where
    T: Clone,
    C: Kind;

#[allow(unused)]
impl<T, C> Smart<T, C>
where
    T: Clone,
    C: Kind,
{
    /// Creates the smart pointer.
    #[inline]
    #[must_use]
    pub fn new(value: T) -> Self {
        let ptr = Box::into_raw(Box::new(Inner {
            count: C::one(),
            value,
        }));
        Self(unsafe { NonNull::new_unchecked(ptr) })
    }

    #[inline]
    #[must_use]
    const fn inner(&self) -> &Inner<T, C> {
        // SAFETY: type invariant
        unsafe { self.0.as_ref() }
    }

    /// Converts the smart pointer to a raw pointer.
    #[inline]
    #[must_use]
    pub fn into_raw(self) -> NonNull<Inner<T, C>> {
        let smart = ManuallyDrop::new(self);
        smart.0
    }

    /// Creates a smart pointer from a raw pointer.
    #[inline]
    pub fn from_raw(ptr: NonNull<Inner<T, C>>) -> Self {
        debug_assert!(ptr.is_aligned());
        unsafe { Self(ptr) }
    }

    /// Gets a reference to the value.
    #[inline]
    #[must_use]
    pub const fn as_ref(&self) -> &T {
        &self.inner().value
    }

    /// Checks if this reference is unique.
    #[inline]
    #[must_use]
    pub fn is_unique(&self) -> bool {
        self.inner().count.is_unique()
    }

    /// Gets a mutable reference to the value
    #[inline]
    #[must_use]
    pub fn as_mut(&mut self) -> Option<&mut T> {
        // SAFETY: type invariant, the raw pointer is valid
        if self.is_unique() {
            // SAFETY: uniqueness checked
            Some(unsafe { &mut self.0.as_mut().value })
        } else {
            None
        }
    }

    /// Gets a mutable reference to the value without checking the uniqueness
    ///
    /// # Safety
    ///
    /// Any caller should check the uniqueness first with [`Self::is_unique`].
    #[inline]
    pub const unsafe fn as_mut_unchecked(&mut self) -> &mut T {
        // SAFETY: uniqueness precondition
        unsafe { &mut self.0.as_mut().value }
    }

    /// Gets a mutable reference to the value without checking the uniqueness
    ///
    /// # Safety
    ///
    /// - Any caller should check the uniqueness first with [`Self::is_unique`].
    /// - The referenced value must outlive `'a`.
    #[inline]
    pub(crate) const unsafe fn as_mut_unchecked_extended<'a>(&mut self) -> &'a mut T
    where
        Self: 'a,
    {
        // SAFETY: uniqueness precondition
        unsafe { &mut self.0.as_mut().value }
    }

    /// Gets the reference count.
    #[inline]
    #[must_use]
    pub(crate) fn ref_count(&self) -> usize {
        // SAFETY: type invariant, the raw pointer cannot be dangling
        let inner = unsafe { self.0.as_ref() };
        inner.count.get()
    }

    /// Try to unwrap to its inner value.
    #[inline]
    pub fn try_unwrap(self) -> Result<T, Self> {
        unsafe {
            if self.is_unique() {
                // do not drop `self`!
                let this = ManuallyDrop::new(self);
                // SAFETY: type invariant, pointer must be valid
                let inner = unsafe { Box::from_raw(this.0.as_ptr()) };
                Ok(inner.value)
            } else {
                Err(self)
            }
        }
    }

    pub(crate) fn incr(&self) -> UpdateResult {
        self.inner().count.incr()
    }
}

impl<T, C> Clone for Smart<T, C>
where
    T: Clone,
    C: Kind,
{
    fn clone(&self) -> Self {
        if unsafe { &(*self.0.as_ptr()).count }.incr() == UpdateResult::Done {
            Self(self.0)
        } else {
            let inner = self.inner().clone();
            let ptr = Box::into_raw(Box::new(inner));
            // SAFETY: duh
            let nonnull = unsafe { NonNull::new_unchecked(ptr) };
            Self(nonnull)
        }
    }
}

impl<T, C> Drop for Smart<T, C>
where
    T: Clone,
    C: Kind,
{
    fn drop(&mut self) {
        // SAFETY: type invariant, cannot be dangling
        unsafe {
            if self.inner().count.decr() == UpdateResult::Overflow {
                let ptr = self.0.as_ptr();
                let _ = Box::from_raw(ptr);
            }
        }
    }
}

impl<T, C> Deref for Smart<T, C>
where
    T: Clone,
    C: Kind,
{
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

unsafe impl<T, C> Send for Smart<T, C>
where
    T: Sync + Send + Clone,
    C: Send + Kind,
{
}

unsafe impl<T, C> Sync for Smart<T, C>
where
    T: Sync + Send + Clone,
    C: Sync + Kind,
{
}
