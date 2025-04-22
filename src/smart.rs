//! Limited but generic smart pointer.
//!
//! This module provides a smart pointer that abstracts over its "kind":
//!
//! - unique,
//! - reference counted,
//! - atomically reference counted.

use alloc::boxed::Box;
use core::mem::ManuallyDrop;
use core::ops::Deref;
use core::ptr::NonNull;

use crate::backend::{
    Backend, BackendImpl, CloneOnOverflow, Counter, PanicOnOverflow, UpdateResult,
};

#[cfg(test)]
mod tests;

/// Smart pointer inner cell.
pub struct Inner<T, C>
where
    C: Backend,
{
    count: C,
    value: T,
}

impl<T, C> Clone for Inner<T, C>
where
    T: Clone,
    C: Backend,
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
    C: Backend;

#[allow(unused)]
impl<T, C> Smart<T, C>
where
    C: Backend,
{
    /// Creates the smart pointer.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::smart::Smart;
    /// # use hipstr::Arc;
    /// let p = Smart::<_, Arc>::new(42);
    /// let q = p.clone();
    /// assert_eq!(p.as_ref(), q.as_ref());
    /// ```
    ///
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
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::smart::Smart;
    /// # use hipstr::Arc;
    /// let p = Smart::<_, Arc>::new(42);
    /// let ptr = Smart::into_raw(p);
    /// let q = unsafe { Smart::from_raw(ptr) };
    /// ```
    #[inline]
    #[must_use]
    pub fn into_raw(this: Self) -> NonNull<Inner<T, C>> {
        let smart = ManuallyDrop::new(this);
        smart.0
    }

    /// Creates a smart pointer from a raw pointer.
    ///
    /// # Safety
    ///
    /// The raw pointer must come from a previous call to
    /// [`Smart::<U, C>::into_raw`]
    /// where `U` must have the same size and alignment as `T`.
    ///
    /// Note that if `U` is not the same type as `T`, this is basically like
    /// transmuting a reference.
    ///
    /// [`Smart::<U, C>::into_raw`]: Self::into_raw
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::smart::Smart;
    /// # use hipstr::Arc;
    /// let p = Smart::<_, Arc>::new(42);
    /// let ptr = Smart::into_raw(p);
    /// let q = unsafe { Smart::from_raw(ptr) };
    /// ```
    #[inline]
    pub fn from_raw(ptr: NonNull<Inner<T, C>>) -> Self {
        debug_assert!(ptr.is_aligned());
        unsafe { Self(ptr) }
    }

    /// Gets a reference to the value.
    #[inline]
    #[must_use]
    pub const fn as_ref(this: &Self) -> &T {
        &this.inner().value
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
    #[cfg(test)]
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

    pub(crate) fn force_clone(&self) -> Self
    where
        T: Clone,
    {
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

impl<T: Clone, C: Counter> Clone for Smart<T, BackendImpl<C, CloneOnOverflow>> {
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

impl<T, C: Counter> Clone for Smart<T, BackendImpl<C, PanicOnOverflow>> {
    fn clone(&self) -> Self {
        if self.incr() == UpdateResult::Done {
            Self(self.0)
        } else {
            panic!("overflow on clone")
        }
    }
}

impl<T, C> Drop for Smart<T, C>
where
    C: Backend,
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
    C: Backend,
{
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        Smart::as_ref(self)
    }
}

impl<T, C> AsRef<T> for Smart<T, C>
where
    C: Backend,
{
    #[inline]
    fn as_ref(&self) -> &T {
        Smart::as_ref(self)
    }
}

unsafe impl<T, C> Send for Smart<T, C>
where
    T: Sync + Send,
    C: Send + Backend,
{
}

unsafe impl<T, C> Sync for Smart<T, C>
where
    T: Sync + Send,
    C: Sync + Backend,
{
}
