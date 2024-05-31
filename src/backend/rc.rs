//! This module provides a basic reference-counting smart pointer.

use core::cell::Cell;
use core::mem::align_of;
use core::ptr::{addr_of, addr_of_mut, NonNull};
use core::sync::atomic::{fence, AtomicUsize, Ordering};

use crate::alloc::boxed::Box;

/// Trait for a basic reference counter
pub trait Count {
    /// Creates a new counter that starts at one.
    fn one() -> Self;

    /// Increments the counter and returns true iff the counter reaches `usize::MAX`.
    fn incr(&self) -> bool;

    /// Decrements the counter and returns true iff the counter reaches zero.
    fn decr(&self) -> bool;

    /// Returns the current value of the counter.
    fn get(&self) -> usize;
}

/// Local (not thread-safe) reference counter.
pub struct Local(Cell<usize>);

/// Thread-safe reference counter.
#[cfg(target_has_atomic = "ptr")]
pub struct ThreadSafe(AtomicUsize);

impl Count for Local {
    fn one() -> Self {
        Self(Cell::new(1))
    }

    fn incr(&self) -> bool {
        let new_value = self.0.get() + 1;
        self.0.set(new_value);
        new_value == usize::MAX
    }

    fn decr(&self) -> bool {
        let new_value = self.0.get().saturating_sub(1);
        self.0.set(new_value);
        new_value == 0
    }

    fn get(&self) -> usize {
        self.0.get()
    }
}

#[cfg(target_has_atomic = "ptr")]
impl Count for ThreadSafe {
    fn one() -> Self {
        Self(AtomicUsize::new(1))
    }

    fn decr(&self) -> bool {
        let old_value = self.0.fetch_sub(1, Ordering::Release);
        if old_value == 1 {
            fence(Ordering::Acquire);
            true
        } else {
            false
        }
    }

    fn incr(&self) -> bool {
        let old = self.0.fetch_add(1, Ordering::Relaxed);
        old == usize::MAX
    }

    fn get(&self) -> usize {
        self.0.load(Ordering::Acquire)
    }
}

/// Reference counting inner cell.
struct Inner<T, C: Count> {
    count: C,
    value: T,
}

/// Non-null raw pointer to a reference counting inner cell.
///
/// Using this raw pointer, rather than a full fledge Rc, can be error-prone.
/// Please follow the following rules:
///
/// - it should not be copied meaningfully (typically it excludes temporary
///   stack copise) without `incr()`-ing it
/// - it should not be dropped (except for temporary copies) without `decr()`-ing it
pub struct Raw<T, C: Count>(NonNull<Inner<T, C>>);

impl<T, C: Count> Copy for Raw<T, C> {}

impl<T, C: Count> Clone for Raw<T, C> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T, C: Count> Raw<T, C> {
    /// Creates a new raw pointer to a reference counting cell containing the provided value.
    ///
    /// The created raw pointer is valid.
    #[inline]
    #[must_use]
    pub fn new(value: T) -> Self {
        let ptr = Box::into_raw(Box::new(Inner {
            count: C::one(),
            value,
        }));
        Self(unsafe { NonNull::new_unchecked(ptr) })
    }

    /// Gets a reference to the inner cell.
    ///
    /// # Safety
    ///
    /// The pointer must be valid.
    #[inline]
    #[must_use]
    const unsafe fn inner(&self) -> &Inner<T, C> {
        unsafe { self.0.as_ref() }
    }

    /// Checks if this reference is unique.
    ///
    /// # Safety
    ///
    /// The pointer must be valid.
    #[inline]
    #[must_use]
    pub unsafe fn is_unique(self) -> bool {
        let inner = unsafe { self.inner() };

        inner.count.get() == 1
    }

    /// Gets the current reference count.
    ///
    /// # Safety
    ///
    /// The pointer must be valid.
    #[inline]
    #[must_use]
    pub unsafe fn ref_count(self) -> usize {
        let inner = unsafe { self.inner() };

        inner.count.get()
    }

    /// Increments the current reference count.
    ///
    /// # Safety
    ///
    /// The pointer must be valid.
    ///
    /// # Panics
    ///
    /// If the counter overflows.
    #[inline]
    pub unsafe fn incr(self) {
        let inner = unsafe { self.inner() };

        if inner.count.incr() {
            panic!("ref count overflow")
        }
    }

    /// Decrements the current reference count, deallocating the smart pointer
    /// if the count reaches zero.
    ///
    /// Note: consequently, it may invalidates the pointer.
    ///
    /// # Safety
    ///
    /// The pointer must be valid.
    #[inline]
    pub unsafe fn decr(self) {
        let inner = unsafe { self.inner() };

        if inner.count.decr() {
            let _ = unsafe { Box::from_raw(self.0.as_ptr()) };
        }
    }

    /// Checks the apparent validity of this smart pointer.
    ///
    /// # Safety
    ///
    /// The pointer must be valid.
    #[inline]
    #[cfg_attr(coverage_nightly, coverage(off))]
    pub unsafe fn is_valid(self) -> bool {
        // SAFETY: function precondition => pointer is valid
        self.0.as_ptr().align_offset(align_of::<Inner<T, C>>()) == 0
            && unsafe { self.ref_count() > 0 }
    }

    /// Gets a reference to the value.
    ///
    /// # Safety
    ///
    /// The pointer must be valid.
    #[inline]
    #[must_use]
    pub const unsafe fn as_ref<'a>(&self) -> &'a T {
        // SAFETY: function precondition => pointer is valid
        unsafe { &*addr_of!((*self.0.as_ptr().cast_const()).value) }
    }

    /// Extracts the value.
    ///
    /// # Safety
    ///
    /// The pointer must be valid.
    /// The reference count must be 1.
    /// And no other copy of this raw pointer should ever be accessed.
    #[inline]
    #[must_use]
    pub unsafe fn unwrap(self) -> T {
        // SAFETY: function precondition => pointer is valid
        let inner = unsafe { Box::from_raw(self.0.as_ptr()) };
        debug_assert!(inner.count.get() == 1);
        inner.value
    }

    /// Get a mutable reference to the value.
    ///
    /// # Safety
    ///
    /// The pointer must be valid.
    /// The reference count must be 1.
    /// And no other copy of this raw pointer should ever be accessed.
    #[inline]
    #[must_use]
    pub unsafe fn as_mut<'a>(&self) -> &'a mut T {
        // SAFETY: function precondition => pointer is valid
        debug_assert!(unsafe { self.is_unique() });

        // SAFETY: function precondition => pointer is valid
        unsafe { &mut *addr_of_mut!((*self.0.as_ptr()).value) }
    }
}

/// Basic single counter reference-counting smart pointer.
///
/// ONLY FOR TEST PURPOSES
#[allow(unused)]
pub struct Rc<T, C: Count>(Raw<T, C>);

#[allow(unused)]
impl<T, C: Count> Rc<T, C> {
    /// Creates the reference-counting smart pointer.
    #[inline]
    #[must_use]
    pub fn new(value: T) -> Self {
        let ptr = Box::into_raw(Box::new(Inner {
            count: C::one(),
            value,
        }));
        Self(Raw(unsafe { NonNull::new_unchecked(ptr) }))
    }

    /// Gets a reference to the value.
    #[inline]
    #[must_use]
    pub const fn as_ref(&self) -> &T {
        // SAFETY: type invariant, the raw pointer cannot be dangling
        unsafe { self.0.as_ref() }
    }

    /// Gets a mutable reference to the value
    #[inline]
    #[must_use]
    pub fn as_mut(&mut self) -> Option<&mut T> {
        unsafe {
            // SAFETY: type invariant, the raw pointer is valid
            if self.0.is_unique() {
                Some(self.0.as_mut())
            } else {
                None
            }
        }
    }

    /// Gets the reference count.
    #[inline]
    #[must_use]
    pub fn ref_count(&self) -> usize {
        // SAFETY: type invariant, the raw pointer cannot be dangling
        unsafe { self.0.ref_count() }
    }

    /// Try to unwrap to its inner value.
    #[inline]
    pub fn try_unwrap(self) -> Result<T, Self> {
        unsafe {
            if self.0.is_unique() {
                let value = self.0.unwrap();
                core::mem::forget(self);
                Ok(value)
            } else {
                Err(self)
            }
        }
    }
}

impl<T, C: Count> Clone for Rc<T, C> {
    fn clone(&self) -> Self {
        unsafe {
            self.0.incr();
        }
        Self(self.0)
    }
}

impl<T, C> Drop for Rc<T, C>
where
    C: Count,
{
    fn drop(&mut self) {
        // SAFETY: cannot be dangling
        unsafe { self.0.decr() }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type L<T> = Rc<T, Local>;
    type T<E> = Rc<E, ThreadSafe>;

    #[test]
    fn test_rc_local() {
        let mut a = L::new(1);
        assert_eq!(a.as_ref(), &1);

        let mut b = a.clone();
        assert_eq!(a.ref_count(), 2);
        assert_eq!(b.ref_count(), 2);

        assert!(a.as_mut().is_none());
        assert!(b.as_mut().is_none());

        assert_eq!(b.as_ref(), &1);

        // will drop b
        assert!(b.try_unwrap().is_err());

        assert!(a.as_mut().is_some());
        assert_eq!(a.try_unwrap().unwrap_or(0), 1);
    }

    #[test]
    fn test_rc_thread_safe() {
        let a = T::new(1);
        assert_eq!(a.as_ref(), &1);

        let a_raw = a.0.clone(); // could be just `a.0`
        assert_eq!(unsafe { a_raw.as_ref() }, &1);
        assert_eq!(unsafe { a_raw.ref_count() }, 1);

        let mut b = a.clone();
        assert_eq!(a.ref_count(), 2);
        assert_eq!(b.ref_count(), 2);
        assert_eq!(b.as_ref(), &1);
        assert!(b.as_mut().is_none());

        // will drop a
        assert!(a.try_unwrap().is_err());

        assert_eq!(b.ref_count(), 1);
        assert!(b.as_mut().is_some());
        assert_eq!(b.try_unwrap().unwrap_or(0), 1);
    }

    #[test]
    #[should_panic]
    fn test_rc_overflow() {
        struct Cleanup(Raw<i32, Local>);
        impl Drop for Cleanup {
            fn drop(&mut self) {
                unsafe {
                    self.0.inner().count.0.set(1);
                    self.0.decr();
                }
            }
        }

        let _cleanup_guard;
        {
            let a = L::new(1);
            _cleanup_guard = Cleanup(a.0);

            unsafe {
                a.0.inner().count.0.set(usize::MAX - 1);
            };
            let _b = a.clone();
        }
    }
}
