//! Limited but generic smart pointer.
//!
//! This module provides a smart pointer that abstracts over its "kind":
//!
//! - unique,
//! - reference counted,
//! - atomically reference counted.

use alloc::boxed::Box;
use core::borrow::Borrow;
use core::hash::{Hash, Hasher};
use core::mem::ManuallyDrop;
use core::ops::Deref;
use core::ptr::NonNull;
use core::{fmt, ptr};

use crate::backend::{
    Backend, BackendImpl, CloneOnOverflow, Counter, PanicOnOverflow, UpdateResult,
};

#[cfg(test)]
mod tests;

/// Smart pointer inner cell.
#[repr(C)]
pub struct Inner<T, C>
where
    C: Backend,
{
    pub(crate) count: C,
    value: T,
}

impl<T, C> Clone for Inner<T, C>
where
    T: Clone,
    C: Backend,
{
    fn clone(&self) -> Self {
        Self {
            count: C::default(),
            value: self.value.clone(),
        }
    }
}

/// Basic smart pointer, with generic counter.
#[repr(transparent)]
pub struct Smart<T, C>(pub(crate) NonNull<Inner<T, C>>)
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
            count: C::default(),
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
    #[must_use]
    pub unsafe fn from_raw(ptr: NonNull<Inner<T, C>>) -> Self {
        debug_assert!(ptr.is_aligned());
        unsafe { Self(ptr) }
    }

    /// Gets a reference to the value.
    #[inline]
    #[must_use]
    pub const fn get(this: &Self) -> &T {
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

    /// Tries to unwrap to its inner value.
    ///
    /// # Errors
    ///
    /// Returns `Err(this)` if the reference is shared.
    #[inline]
    pub fn try_unwrap(this: Self) -> Result<T, Self> {
        unsafe {
            if this.is_unique() {
                // do not drop `self`!
                let this = ManuallyDrop::new(this);
                // SAFETY: type invariant, pointer must be valid
                let inner = unsafe { Box::from_raw(this.0.as_ptr()) };
                Ok(inner.value)
            } else {
                Err(this)
            }
        }
    }

    pub(crate) fn incr(&self) -> UpdateResult {
        self.inner().count.incr()
    }

    pub(crate) unsafe fn into_inner_unchecked(self) -> T {
        debug_assert!(self.is_unique());

        let this = ManuallyDrop::new(self);
        // SAFETY: type invariant, pointer must be valid
        let inner = unsafe { Box::from_raw(this.0.as_ptr()) };
        inner.value
    }

    /// Tries to clone the smart pointer by increasing the reference count.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::smart::Smart;
    /// # use hipstr::{Arc, Unique};
    /// let p = Smart::<_, Arc>::new(42);
    /// let q = p.try_clone().unwrap();;
    /// assert_eq!(p.as_ref(), q.as_ref());
    ///
    /// let u = Smart::<_, Unique>::new(42);
    /// let q = u.try_clone();
    /// assert!(q.is_none());
    /// ```
    #[must_use]
    pub fn try_clone(&self) -> Option<Self> {
        if self.incr() == UpdateResult::Done {
            Some(Self(self.0))
        } else {
            None
        }
    }

    /// Clones the smart pointer even if the referenced count overflows, in
    /// which case the underlying data is cloned.
    ///
    /// This is equivalent to calling [`Self::try_clone`] and cloning the inner
    /// value if the reference count overflows.
    ///
    /// This is the default behavior of [`Clone::clone`] for `Unique`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::smart::Smart;
    /// # use hipstr::{Arc, Unique};
    /// let p = Smart::<_, Arc>::new(42);
    /// let q = Smart::force_clone(&p);
    /// assert_eq!(p.as_ref(), q.as_ref());
    /// assert_eq!(p.as_ref() as *const i32, q.as_ref() as *const i32);
    ///
    /// let u = Smart::<_, Unique>::new(42);
    /// let q = Smart::force_clone(&u);
    /// assert_eq!(u.as_ref(), q.as_ref());
    /// assert_ne!(u.as_ref() as *const i32, q.as_ref() as *const i32);
    /// ```
    #[must_use]
    pub fn force_clone(this: &Self) -> Self
    where
        T: Clone,
    {
        if unsafe { &(*this.0.as_ptr()).count }.incr() == UpdateResult::Done {
            Self(this.0)
        } else {
            let inner = this.inner().clone();
            let ptr = Box::into_raw(Box::new(inner));
            // SAFETY: duh
            let nonnull = unsafe { NonNull::new_unchecked(ptr) };
            Self(nonnull)
        }
    }

    #[inline]
    pub fn mutate(this: &mut Self) -> &mut T
    where
        T: Clone,
    {
        if !this.is_unique() {
            this.detach();
        }
        // SAFETY: uniqueness enforced
        unsafe { this.as_mut_unchecked() }
    }

    #[inline]
    pub fn mutate_copy(this: &mut Self) -> &mut T
    where
        T: Copy,
    {
        if !this.is_unique() {
            this.detach_copy();
        }
        // SAFETY: uniqueness enforced
        unsafe { this.as_mut_unchecked() }
    }

    pub(crate) fn detach(&mut self)
    where
        T: Clone,
    {
        *self = Self::new(Smart::get(self).clone());
    }

    pub(crate) fn detach_copy(&mut self)
    where
        T: Copy,
    {
        *self = Self::new(*Smart::get(self));
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
        Self::get(self)
    }
}

impl<T, C> AsRef<T> for Smart<T, C>
where
    C: Backend,
{
    #[inline]
    fn as_ref(&self) -> &T {
        Self::get(self)
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

impl<T, C> fmt::Debug for Smart<T, C>
where
    T: fmt::Debug,
    C: Backend,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        T::fmt(self, f)
    }
}

impl<T, C> fmt::Display for Smart<T, C>
where
    T: fmt::Display,
    C: Backend,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        T::fmt(self, f)
    }
}

impl<T, U, C1, C2> PartialEq<Smart<U, C2>> for Smart<T, C1>
where
    T: PartialEq<U>,
    C1: Backend,
    C2: Backend,
{
    #[inline]
    fn eq(&self, other: &Smart<U, C2>) -> bool {
        T::eq(self, other)
    }
}

impl<T, C> Eq for Smart<T, C>
where
    T: Eq,
    C: Backend,
{
}

impl<T, U, C1, C2> PartialOrd<Smart<U, C2>> for Smart<T, C1>
where
    T: PartialOrd<U>,
    C1: Backend,
    C2: Backend,
{
    #[inline]
    fn partial_cmp(&self, other: &Smart<U, C2>) -> Option<core::cmp::Ordering> {
        T::partial_cmp(self, other)
    }
}

impl<T, C> Ord for Smart<T, C>
where
    T: Ord,
    C: Backend,
{
    #[inline]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        T::cmp(self, other)
    }
}

impl<T, C> fmt::Pointer for Smart<T, C>
where
    C: Backend,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        ptr::from_ref(Self::get(self)).fmt(f)
    }
}

impl<T, C> Default for Smart<T, C>
where
    T: Default,
    C: Backend,
{
    #[inline]
    fn default() -> Self {
        Self::new(T::default())
    }
}

impl<T, C> Borrow<T> for Smart<T, C>
where
    C: Backend,
{
    #[inline]
    fn borrow(&self) -> &T {
        Self::get(self)
    }
}

impl<T, C> Hash for Smart<T, C>
where
    T: Hash,
    C: Backend,
{
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        T::hash(self, state)
    }
}
