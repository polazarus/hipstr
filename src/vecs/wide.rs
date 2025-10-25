//! [`Vec`]-compatible vectors.
//!
//! This module contains the implementation of smart wide vectors with
//! reference counting. The main type is [`SmartWideVec<T, B>`], which
//! represents a vector of elements of type `T` with a backend `B`
//! that manages the reference counting.
//!
//! The vectors in this module are designed to be compatible with
//! the standard library's [`Vec`] type, providing similar functionality
//! while adding reference counting capabilities. This allows for efficient
//! sharing of vector data across multiple owners without unnecessary
//! copying.
//!
//! # Examples
//!
//! ```
//! # use hipstr::vecs::wide::SmartWideVec;
//! # use hipstr::Arc;
//! let vec: SmartWideVec<i32, Arc> = SmartWideVec::from(vec![1, 2, 3]);
//! let vec2 = vec.clone();
//! assert_eq!(vec.as_slice(), vec2.as_slice());
//! ```
use alloc::boxed::Box;
use alloc::vec::Vec;
use core::mem::{self, transmute, ManuallyDrop};
use core::ptr::{self, NonNull};

use const_default::ConstDefault;
use rules_derive::rules_derive;

use self::repr::{WideInner, WideRepr};
use crate::backend::{BackendImpl, CloneOnOverflow, Counter, PanicOnOverflow, UpdateResult};
use crate::common::derives::{AsRef, Borrow, ConstDefault, Deref, From, Vector};
use crate::common::traits::Mutate;
use crate::common::{manually_drop_as_mut, manually_drop_as_ref};
use crate::Backend;

pub(crate) mod repr;

#[cfg(test)]
mod tests;

#[repr(transparent)]
#[rules_derive(ConstDefault(Self(WideRepr::NULL)))]
pub struct WideVec<T, P>(WideRepr<T, P>);

impl<T, P> WideVec<T, P> {
    pub const fn new() -> Self {
        Self(WideRepr::NULL)
    }

    fn from_vec(vec: Vec<T>, prefix: P) -> Self {
        let cap = vec.capacity();
        let repr = if cap == 0 {
            WideRepr::NULL
        } else {
            let mut vec = ManuallyDrop::new(vec);

            // SAFETY: the vector ptr is not null by type invariant
            // as_non_null is not stable yet
            let ptr = unsafe { NonNull::new_unchecked(vec.as_mut_ptr()) };
            let len = vec.len();
            let inner = Box::new(WideInner {
                prefix,
                ptr,
                cap,
                len,
            });
            let inner = Box::into_raw(inner);
            // SAFETY: Box pointer is not null
            let inner = unsafe { NonNull::new_unchecked(inner) };
            WideRepr::new(inner)
        };
        Self(repr)
    }

    pub const fn as_ptr(&self) -> *const T {
        match self.0.as_ref() {
            Some(inner) => inner.ptr.as_ptr(),
            None => ptr::dangling(),
        }
    }

    pub const fn len(&self) -> usize {
        match self.0.as_ref() {
            Some(inner) => inner.len,
            None => 0,
        }
    }

    pub const fn as_slice(&self) -> &[T] {
        unsafe { core::slice::from_raw_parts(self.as_ptr(), self.len()) }
    }

    pub const fn as_mut_slice(&mut self) -> &mut [T] {
        match self.0.as_mut() {
            Some(inner) => unsafe {
                core::slice::from_raw_parts_mut(inner.ptr.as_ptr(), inner.len)
            },
            None => &mut [],
        }
    }

    pub const fn set_len(&mut self, new_len: usize) {
        if let Some(inner) = self.0.as_mut() {
            inner.len = new_len;
        }
    }

    fn take_vec(&mut self) -> Option<(Vec<T>, P)> {
        mem::replace(self, Self::DEFAULT).into_vec()
    }

    fn into_vec(self) -> Option<(Vec<T>, P)> {
        let old = ManuallyDrop::new(self);
        if let Some(inner) = old.0.get() {
            // SAFETY: type invariant
            let boxed = unsafe { Box::from_raw(inner.as_ptr()) };
            let WideInner {
                ptr,
                cap,
                len,
                prefix,
            } = *boxed;
            let vec = unsafe { Vec::from_raw_parts(ptr.as_ptr(), len, cap) };
            Some((vec, prefix))
        } else {
            None
        }
    }
}

impl<T, B> Drop for WideVec<T, B> {
    fn drop(&mut self) {
        if let Some(inner) = self.0.get() {
            // SAFETY: inner is valid by the type invariant
            unsafe {
                drop_inner(inner);
            }
        }
    }
}

/// Drops the inner wide vector, including the prefix and the vector.
///
/// # Safety
///
/// The caller must ensure that `inner` is a valid pointer to a `WideInner<T, P>`
/// that was allocated with `Box::new`.
unsafe fn drop_inner<T, P>(inner: NonNull<WideInner<T, P>>) {
    // retrieve the raw vec
    let &WideInner { ptr, cap, len, .. } = unsafe { inner.as_ref() };

    // drop the inner box, will drop the prefix too
    // SAFETY: precondition
    let _ = unsafe { Box::from_raw(inner.as_ptr()) };

    // SAFETY: we are taking ownership of the vector, so the pointer is valid
    // and was allocated by the global allocator
    let _ = unsafe { Vec::from_raw_parts(ptr.as_ptr(), len, cap) };
}

/// A shared vector backed by a standard wide vector, [`Vec`].
#[repr(transparent)]
#[rules_derive(
    ConstDefault(Self::new()),
    AsRef([T], Self::as_slice),
    Deref([T], Self::as_slice),
    Borrow([T], Self::as_slice),
    From(Vec<T>, Self::from_vec),
    Vector(T),
)]
pub struct SmartWideVec<T, B: Backend>(pub(super) WideRepr<T, B>);

impl<T, B: Backend> SmartWideVec<T, B> {
    /// Creates a new, empty `SmartWideVec`.
    ///
    /// This is equivalent to `SmartWideVec::default()`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::vecs::SmartWideVec;
    /// let vec: SmartWideVec<i32> = SmartWideVec::new();
    /// assert!(vec.is_empty());
    /// assert_eq!(vec.len(), 0);
    /// assert_eq!(vec.capacity(), 0);
    /// assert_eq!(vec.as_slice(), &[]);
    /// ```
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        unsafe { Self::from_wide_vec_unchecked(WideVec::new()) }
    }

    pub(crate) const unsafe fn from_wide_vec_unchecked(wide_vec: WideVec<T, B>) -> Self {
        unsafe { transmute(wide_vec) }
    }

    /// Returns a reference to the underlying `WideVec`.
    pub(crate) const fn as_wide_vec(&self) -> &WideVec<T, B> {
        // SAFETY: type invariant
        unsafe { &*(&raw const *self).cast() }
    }

    /// Creates a new `SmartWideVec` from a standard `Vec`.
    pub(crate) fn from_vec(vec: Vec<T>) -> Self {
        let wide_vec = WideVec::from_vec(vec, B::DEFAULT);
        unsafe { Self::from_wide_vec_unchecked(wide_vec) }
    }

    /// Converts the `SmartWideVec` into a standard `Vec` without checking
    /// for uniqueness.
    pub(crate) unsafe fn into_vec_unchecked(self) -> Vec<T> {
        debug_assert!(self.is_unique() || self.is_empty());
        let wide_vec: WideVec<T, B> = unsafe { transmute(self) };
        wide_vec.into_vec().map_or_else(Vec::new, |(vec, _)| vec)
    }

    /// Returns a raw pointer to the vector's buffer.
    ///
    /// If the vector is not yet allocated, this function returns a dangling
    /// pointer (see [`std::ptr::dangling`]).
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::vec;
    /// use hipstr::vecs::wide::SmartWideVec;
    /// use hipstr::Arc;
    /// let vec: SmartWideVec<i32, Arc> = SmartWideVec::from(vec![1, 2, 3]);
    /// let ptr = vec.as_ptr();
    /// assert_eq!(unsafe { *ptr }, 1);
    /// assert!(std::ptr::eq(ptr, &vec[0]));
    /// ```
    #[must_use]
    pub const fn as_ptr(&self) -> *const T {
        match self.0.as_ref() {
            Some(inner) => inner.ptr.as_ptr(),
            None => ptr::dangling(),
        }
    }

    /// Returns the number of elements the vector can hold without reallocating.
    ///
    /// If the vector is not yet allocated (typically, constructed with
    /// [`SmartWideVec::new`]), the capacity is `0`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::vecs::wide::SmartWideVec;
    /// # use hipstr::Arc;
    /// let vec: SmartWideVec<i32, Arc> = SmartWideVec::new();
    /// assert_eq!(vec.capacity(), 0);
    /// let vec = SmartWideVec::<_, Arc>::from(vec![1, 2, 3]);
    /// assert!(vec.capacity() >= 3);
    /// ```
    #[must_use]
    #[inline]
    pub const fn capacity(&self) -> usize {
        match self.0.as_ref() {
            Some(inner) => inner.cap,
            None => 0,
        }
    }

    /// Returns the number of elements in the vector, also referred to as its 'length'.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::vecs::wide::SmartWideVec;
    /// # use hipstr::Arc;
    /// let vec: SmartWideVec<i32, Arc> = SmartWideVec::new();
    /// assert_eq!(vec.len(), 0);
    /// let vec = SmartWideVec::<_, Arc>::from(vec![1, 2, 3]);
    /// assert_eq!(vec.len(), 3);
    /// ```
    #[must_use]
    pub const fn len(&self) -> usize {
        match self.0.as_ref() {
            Some(inner) => inner.len,
            None => 0,
        }
    }

    /// Returns `true` if the vector contains no elements.
    ///
    /// # Examples
    /// ```
    /// # use hipstr::vecs::wide::SmartWideVec;
    /// # use hipstr::Arc;
    /// let vec: SmartWideVec<i32, Arc> = SmartWideVec::new();
    /// assert!(vec.is_empty());
    /// let vec = SmartWideVec::<_, Arc>::from(vec![1, 2, 3]);
    /// assert!(!vec.is_empty());
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns a slice containing all elements of the vector.
    ///
    /// Also used for `AsRef` and `Deref` implementations.
    ///
    /// # Examples
    /// ```
    /// # use hipstr::vecs::wide::SmartWideVec;
    /// # use hipstr::Arc;
    /// let vec: SmartWideVec<i32, Arc> = SmartWideVec::from(vec![1, 2, 3]);
    /// assert_eq!(vec.as_slice(), &[1, 2, 3]);
    /// ```
    #[must_use]
    #[inline]
    pub const fn as_slice(&self) -> &[T] {
        unsafe { core::slice::from_raw_parts(self.as_ptr(), self.len()) }
    }

    /// Returns `true` if the vector is uniquely owned (i.e. no other references
    /// to the same data exist).
    ///
    /// By convention, an empty and not allocated vector is always considered
    /// unique.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::vecs::wide::SmartWideVec;
    /// # use hipstr::Arc;
    /// let mut vec: SmartWideVec<i32, Arc> = SmartWideVec::from(vec![1, 2, 3]);
    /// assert!(vec.is_unique());
    /// let vec2 = vec.clone();
    /// assert!(!vec.is_unique());
    /// drop(vec2);
    /// assert!(vec.is_unique());
    /// ```
    #[must_use]
    #[inline]
    pub fn is_unique(&self) -> bool {
        self.0.as_ref().is_none_or(|inner| inner.prefix.is_unique())
    }

    /// Gets a mutable reference to the underlying vector if it is uniquely owned.
    /// Otherwise, returns `None`.
    ///
    /// If the vector is not yet allocated (typically, constructed with
    /// [`SmartWideVec::new`]), it is considered uniquely owned and a mutable
    /// reference to an empty vector is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::vecs::wide::SmartWideVec;
    /// # use hipstr::Arc;
    /// let mut vec: SmartWideVec<i32, Arc> = SmartWideVec::from(vec![1, 2, 3]);
    /// {
    ///     let mut r = vec.as_mut().unwrap();
    ///     r.push(4);
    ///     assert_eq!(r.len(), 4);
    /// }
    /// assert_eq!(vec.len(), 4);
    /// ```
    pub fn as_mut(&mut self) -> Option<RefMut<'_, T, B>> {
        if self.is_unique() {
            Some(unsafe { self.as_mut_unchecked() })
        } else {
            None
        }
    }

    /// Gets a mutable reference to the underlying vector without
    /// checking for uniqueness.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the vector is uniquely owned, i.e. no other
    /// references (clones) to the same data exist. Failing to do so may
    /// result in undefined behavior.
    #[must_use]
    pub unsafe fn as_mut_unchecked(&mut self) -> RefMut<'_, T, B> {
        let vec = self.0.as_mut().map_or_else(Vec::new, |inner| unsafe {
            Vec::from_raw_parts(inner.ptr.as_ptr(), inner.len, inner.cap)
        });
        RefMut {
            vec: ManuallyDrop::new(vec),
            origin: self,
        }
    }

    pub fn mutate(&mut self) -> RefMut<'_, T, B>
    where
        T: Clone,
    {
        self.detach();
        unsafe { self.as_mut_unchecked() }
    }

    pub fn mutate_copy(&mut self) -> RefMut<'_, T, B>
    where
        T: Clone,
    {
        self.detach_copy();
        unsafe { self.as_mut_unchecked() }
    }

    pub(crate) fn detach(&mut self)
    where
        T: Clone,
    {
        if let Some(inner) = self.0.as_ref() {
            if !inner.prefix.is_unique() {
                let vec = self.as_slice().to_vec();
                let new = Self::from_vec(vec);
                *self = new;
            }
        }
    }

    pub(crate) fn detach_copy(&mut self)
    where
        T: Clone,
    {
        self.detach(); // slice::to_vec is already specialized
    }

    /// Returns a clone of this [`SmartWideVec<T, B>`] if it is possible without
    /// allocating or cloning.
    ///
    /// If the reference count overflows, returns `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::vecs::wide::SmartWideVec;
    /// # use hipstr::Arc;
    /// let vec: SmartWideVec<i32, Arc> = SmartWideVec::from(vec![1, 2, 3]);
    /// let vec2 = vec.try_clone().unwrap();
    /// assert_eq!(vec.as_slice(), vec2.as_slice());
    /// ```
    #[must_use]
    pub fn try_clone(&self) -> Option<Self> {
        if let Some(inner) = self.0.as_ref() {
            if inner.prefix.incr() == UpdateResult::Overflow {
                return None;
            }
            // now when can copy the repr
        } else {
            // empty vector's repr is copyable
        }
        Some(unsafe { self.copy() })
    }

    const unsafe fn copy(&self) -> Self {
        Self(self.0)
    }

    unsafe fn update_inner(&mut self, mut vec: Vec<T>) {
        let cap = vec.capacity();
        let len = vec.len();
        let ptr = unsafe { NonNull::new_unchecked(vec.as_mut_ptr()) };

        if let Some(inner) = self.0.as_mut() {
            let _ = ManuallyDrop::new(vec);

            inner.len = len;
            inner.cap = cap;
            inner.ptr = ptr;
        } else if cap > 0 {
            let inner = Box::new(WideInner {
                prefix: B::DEFAULT,
                len,
                cap,
                ptr,
            });

            let inner = Box::into_raw(inner);
            // SAFETY: Box pointer is not null
            let inner = unsafe { NonNull::new_unchecked(inner) };

            // transfer the ownership of the vector to the inner
            let _ = ManuallyDrop::new(vec);
            self.0 = WideRepr::new(inner);
        }
    }
}

impl<T, B: Backend> Drop for SmartWideVec<T, B> {
    fn drop(&mut self) {
        if let Some(mut inner) = self.0.get() {
            let prefix = unsafe { &mut inner.as_mut().prefix };
            if prefix.decr() == UpdateResult::Overflow {
                // SAFETY: inner is valid by the type invariant
                unsafe {
                    drop_inner(inner);
                }
            }
        }
    }
}

impl<T, C: Counter> Clone for SmartWideVec<T, BackendImpl<C, PanicOnOverflow>> {
    #[track_caller]
    fn clone(&self) -> Self {
        let Some(clone) = self.try_clone() else {
            panic!("count overflow");
        };
        clone
    }
}

impl<T: Clone, C: Counter> Clone for SmartWideVec<T, BackendImpl<C, CloneOnOverflow>> {
    fn clone(&self) -> Self {
        self.try_clone()
            .unwrap_or_else(|| Self::from_vec(self.as_slice().to_vec()))
    }
}

#[rules_derive(
    Deref(Vec<T>, Self::as_ref, Self::as_mut),
    AsRef(Vec<T>, Self::as_ref, Self::as_mut),
    Borrow(Vec<T>, Self::as_ref, Self::as_mut),
)]
pub struct RefMut<'a, T, B: Backend> {
    vec: ManuallyDrop<Vec<T>>,
    origin: &'a mut SmartWideVec<T, B>,
}

impl<T, B: Backend> RefMut<'_, T, B> {
    /// Returns a reference to the underlying vector.
    #[must_use]
    pub const fn as_ref(&self) -> &Vec<T> {
        manually_drop_as_ref(&self.vec)
    }

    /// Returns a mutable reference to the underlying vector.
    #[must_use]
    pub const fn as_mut(&mut self) -> &mut Vec<T> {
        manually_drop_as_mut(&mut self.vec)
    }
}

impl<T, B: Backend> Drop for RefMut<'_, T, B> {
    #[inline]
    fn drop(&mut self) {
        unsafe {
            self.origin.update_inner(ManuallyDrop::take(&mut self.vec));
        }
    }
}

impl<T: Clone, B: Backend> Mutate for SmartWideVec<T, B> {
    type MutVector<'a>
        = Vec<T>
    where
        Self: 'a;

    type RefMut<'a>
        = RefMut<'a, T, B>
    where
        Self: 'a;

    #[inline]
    fn mutate(&mut self) -> Self::RefMut<'_> {
        self.mutate()
    }
}
