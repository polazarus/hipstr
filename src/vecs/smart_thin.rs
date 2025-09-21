//! Smart thin vector.
//!
//! This module provides a smart vector [`SmartThinVec`] that can be either
//! unique or shared (reference counted, atomically or not), with possible
//! copy-on-write semantics. As a wrapper around [`ThinVec`], [`SmartThinVec`]
//! is *thin*, i.e., the handle is one pointer wide.
//!
//! A [`SmartThinVec`]'s contents may be modified through [`as_mut`] if not
//! shared or [`mutate`] even if shared, provided the data is `Clone`.
//!
//! [`as_mut`]: SmartThinVec::as_mut
//! [`mutate`]: SmartThinVec::mutate
//!
//! # Examples
//!
//! ```
//! use hipstr::smart_thin_vec;
//!
//! let mut v = smart_thin_vec![1, 2, 3];
//!
//! // SmartThinVec is thin
//! assert_eq!(size_of_val(&v), size_of::<*const ()>());
//!
//! assert_eq!(v.as_slice(), &[1, 2, 3]);
//! let w = v.clone();
//!
//! assert_eq!(v.as_slice(), w.as_slice());
//! assert_eq!(v.as_ptr(), w.as_ptr());
//!
//! {
//!    let mut v_mut = v.mutate(); // Copy-on-write
//!    v_mut.push(4);
//! }
//!
//! assert_eq!(v.as_slice(), &[1, 2, 3, 4]);
//! assert_eq!(w.as_slice(), &[1, 2, 3]);
//! ```

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::borrow::BorrowMut;
use core::mem::ManuallyDrop;
use core::ptr;

use const_default::ConstDefault;
use rules_derive::rules_derive;

use super::thin::{Reserved, ThinVec};
use crate::backend::{
    Backend, BackendImpl, CloneOnOverflow, Counter, PanicOnOverflow, UpdateResult,
};
use crate::common::derives::{AsRef, Deref, Vector};
use crate::common::traits::{MutVector, Mutate};
use crate::macros::trait_impls;
use crate::vecs::reprs::ThinRepr;

#[cfg(test)]
mod tests;

/// Creates a new smart vector, [`SmartThinVec`], with array-like syntax.
///
/// # Examples
///
/// ```
/// use hipstr::{smart_thin_vec, Arc, Rc};
/// let v = smart_thin_vec![1, 2, 3];       // SmartThinVec<i32, Arc>
/// assert_eq!(v.as_slice(), &[1, 2, 3]);
/// let w = smart_thin_vec![42; 5];         // SmartThinVec<i32, Arc>
/// assert_eq!(w.as_slice(), &[42, 42, 42, 42, 42]);
///
/// let p = smart_thin_vec![Rc: 1, 2, 3];   // SmartThinVec<i32, Rc>
/// assert_eq!(p.as_slice(), &[1, 2, 3]);
/// ```
#[macro_export]
macro_rules! smart_thin_vec {

    [ $t:ty : $($rest:tt)* ] => {
        {
            use $crate::thin_vec;
            $crate::vecs::smart_thin::SmartThinVec::<_, $t>::from(
                thin_vec![ $( $rest )* ]
            )
        }
    };

    [ $($rest:tt)* ] => {
        smart_thin_vec![$crate::Arc : $($rest)*]
    }

}

/// A smart thin vector that can be either unique, reference counted or
/// atomically reference counted.
///
/// It is a wrapper around [`ThinVec`] that provides reference counting. It is
/// used to store data in a way that allows for efficient sharing and mutation.
///
/// # Examples
///
/// ```
/// # use hipstr::smart_thin_vec;
/// let mut v = smart_thin_vec![1, 2, 3];
/// assert_eq!(v.as_slice(), &[1, 2, 3]);
/// let mut v2 = v.clone();
/// assert!(!v.is_unique());
/// assert_eq!(v.as_ptr(), v2.as_ptr());
/// ```
#[repr(transparent)]
#[rules_derive(
    Deref(ThinVec<T,C>, Self::as_thin_vec),
    AsRef(ThinVec<T,C>, Self::as_thin_vec),
    Vector(T),
)]
pub struct SmartThinVec<T, C: Backend>(ThinRepr<T, C>);

impl<T, B: Backend> SmartThinVec<T, B> {
    const EMPTY: Self = {
        let tv = ThinVec::new();
        unsafe { Self::from_thin_vec_unchecked(tv) }
    };

    pub(super) const unsafe fn from_repr(repr: ThinRepr<T, B>) -> Self {
        Self(repr)
    }

    pub(super) const unsafe fn into_repr(self) -> ThinRepr<T, B> {
        let repr = self.0;
        let _ = ManuallyDrop::new(self);
        repr
    }

    /// Returns the number of elements in the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::vecs::smart_thin::SmartThinVec;
    /// # use hipstr::{Arc, smart_thin_vec};
    /// let v: SmartThinVec<i32, Arc>  = smart_thin_vec![1, 2, 3];
    /// assert_eq!(v.len(), 3);
    /// ```
    #[must_use]
    #[inline]
    pub const fn len(&self) -> usize {
        self.as_thin_vec().len()
    }

    /// Returns the capacity of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::vecs::smart_thin::SmartThinVec;
    /// # use hipstr::vecs::ThinVec;
    /// # use hipstr::Arc;
    /// let v: SmartThinVec<i32, Arc> = SmartThinVec::from(ThinVec::with_capacity(100));
    /// assert!(v.capacity() >= 100);
    /// ```
    #[must_use]
    #[inline]
    pub const fn capacity(&self) -> usize {
        self.as_thin_vec().capacity()
    }

    /// Returns `true` if the vector contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::vecs::smart_thin::SmartThinVec;
    /// # use hipstr::Arc;
    /// let v: SmartThinVec<i32, Arc> = SmartThinVec::new();
    /// assert!(v.is_empty());
    /// let w: SmartThinVec<i32, Arc> = SmartThinVec::from([1, 2, 3]);
    /// assert!(!w.is_empty());
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.as_thin_vec().is_empty()
    }

    /// Returns a raw pointer to the vector's buffer.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::vecs::smart_thin::SmartThinVec;
    /// # use hipstr::Arc;
    /// let v: SmartThinVec<i32, Arc> = SmartThinVec::from([1, 2, 3]);
    /// let p = v.as_ptr();
    /// assert!(!p.is_null());
    /// let w = v.clone();
    /// assert_eq!(v.as_ptr(), w.as_ptr());
    /// ```
    #[must_use]
    #[inline]
    pub const fn as_ptr(&self) -> *const T {
        self.as_thin_vec().as_ptr()
    }

    /// Copies the smart vector without checking or updating the reference
    /// count.
    const unsafe fn copy(&self) -> Self {
        Self(self.0)
    }

    /// Creates a new empty vector.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::vecs::SmartThinVec;;
    /// # use hipstr::Arc;
    /// let v = SmartThinVec::<u8, Arc>::new();
    /// assert_eq!(v.len(), 0);
    /// assert!(v.is_unique());
    /// ```
    #[must_use]
    pub const fn new() -> Self {
        Self::EMPTY
    }

    /// Creates a new empty vector with at least the specified capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::vecs::SmartThinVec;
    /// # use hipstr::Arc;
    /// let v = SmartThinVec::<u8, Arc>::with_capacity(10);
    /// assert_eq!(v.len(), 0);
    /// assert!(v.capacity() >= 10);
    /// assert!(v.is_unique());
    /// ```
    #[inline]
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        let tv = ThinVec::with_capacity(capacity);
        unsafe { Self::from_thin_vec_unchecked(tv) }
    }

    const fn count(&self) -> Option<&B> {
        self.as_thin_vec().prefix()
    }

    /// Checks if this reference is unique.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::smart_thin_vec;
    /// let v = smart_thin_vec![1, 2, 3];
    /// assert_eq!(v.as_slice(), &[1, 2, 3]);
    /// assert!(v.is_unique());
    ///
    /// let mut v2 = v.clone();
    /// assert!(!v.is_unique());
    /// ```
    #[inline]
    #[must_use]
    pub fn is_unique(&self) -> bool {
        if let Some(count) = self.count() {
            count.is_unique()
        } else {
            true // no counter is present
        }
    }

    /// Returns a mutable reference to the vector if it is unique. Otherwise,
    /// returns `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::smart_thin_vec;
    /// let mut v = smart_thin_vec![1, 2, 3];
    /// assert_eq!(v.as_slice(), &[1, 2, 3]);
    /// {
    ///     let v_mut = v.as_mut().unwrap();
    ///     assert_eq!(v_mut.as_slice(), &[1, 2, 3]);
    ///     v_mut.push(4);
    /// }
    /// assert_eq!(v.as_slice(), &[1, 2, 3, 4]);
    ///
    /// let mut v2 = v.clone();
    /// assert!(!v.is_unique());
    /// assert!(v.as_mut().is_none());
    /// ```
    pub fn as_mut(&mut self) -> Option<&mut ThinVec<T, B>> {
        if self.is_unique() {
            Some(unsafe { self.as_mut_unchecked() })
        } else {
            None
        }
    }

    /// Returns a mutable reference to the vector without checking if it is
    /// unique.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it allows mutable access to the vector
    /// even if it is not unique. The caller must ensure that no other
    /// references to the vector exist while this function is used.
    pub const unsafe fn as_mut_unchecked(&mut self) -> &mut ThinVec<T, B> {
        // SAFETY: cast is legit
        // - SmartThinVec and ThinVec are both transparent ThinRepr wrappers
        // - the vector is unique by the above precondition
        unsafe { &mut *ptr::from_mut(self).cast() }
    }

    /// Returns a mutable reference to the vector, possibly cloning the data if
    /// shared.
    ///
    /// If the vector is not unique, the data will be cloned.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::smart_thin_vec;
    /// let mut v = smart_thin_vec![1, 2, 3];
    /// assert_eq!(v.as_slice(), &[1, 2, 3]);
    ///
    /// let mut v2 = v.clone();
    /// assert!(!v.is_unique());
    /// {
    ///     let v_mut = v.mutate();
    ///     assert_eq!(v_mut.as_slice(), &[1, 2, 3]);
    ///     v_mut.push(4);
    /// }
    /// assert!(v.is_unique());
    /// assert_eq!(v.as_slice(), &[1, 2, 3, 4]);
    /// ```
    #[doc(alias = "make_mut")]
    pub fn mutate(&mut self) -> &mut ThinVec<T, B>
    where
        T: Clone,
    {
        if !self.is_unique() {
            self.detach();
        }
        unsafe { self.as_mut_unchecked() }
    }

    pub fn mutate_copy(&mut self) -> &mut ThinVec<T, B>
    where
        T: Copy,
    {
        if !self.is_unique() {
            self.detach_copy();
        }
        unsafe { self.as_mut_unchecked() }
    }

    fn detach(&mut self)
    where
        T: Clone,
    {
        let thin_vec: ThinVec<_, _> = self.as_thin_vec().fresh_clone();
        // SAFETY: thin_vec is fresh
        *self = unsafe { Self::from_thin_vec_unchecked(thin_vec) };
    }

    fn detach_copy(&mut self)
    where
        T: Copy,
    {
        let thin_vec: ThinVec<_, _> = self.as_thin_vec().fresh_copy();
        // SAFETY: thin_vec is fresh
        *self = unsafe { Self::from_thin_vec_unchecked(thin_vec) };
    }

    /// Creates a new `SmartThinVec` from a `ThinVec` without additional checks.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it assumes the input `ThinVec` has a consistent counter.
    /// Typically, this is the case when the `ThinVec` is created with a default counter.
    pub(crate) const unsafe fn from_thin_vec_unchecked(t: ThinVec<T, B>) -> Self {
        let result = Self(t.0);
        let _ = ManuallyDrop::new(t);
        result
    }

    /// Returns a reference to the underlying `ThinVec`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::smart_thin_vec;
    /// # use hipstr::ThinVec;
    /// let v = smart_thin_vec![1, 2, 3];
    /// let t: &ThinVec<_, _> = v.as_thin_vec();
    /// assert_eq!(t.as_slice(), &[1, 2, 3]);
    /// ```
    #[inline]
    #[must_use]
    pub const fn as_thin_vec(&self) -> &ThinVec<T, B> {
        // SAFETY: SmartThinVec and ThinVec are transparent ThinRepr wrappers
        unsafe { &*ptr::from_ref(self).cast() }
    }

    #[inline]
    #[must_use]
    pub(crate) fn from_thin_vec<P: ConstDefault>(thin_vec: ThinVec<T, P>) -> Self {
        let thin_vec = ThinVec::fresh_move(thin_vec);
        // SAFETY: thin_vec is fresh
        unsafe { Self::from_thin_vec_unchecked(thin_vec) }
    }

    #[inline]
    #[must_use]
    pub(crate) fn from_mut_vector(vector: impl MutVector<Item = T>) -> Self {
        let thin_vec = ThinVec::from_mut_vector(vector);
        // SAFETY: thin_vec is fresh
        unsafe { Self::from_thin_vec_unchecked(thin_vec) }
    }

    #[inline]
    #[must_use]
    pub(crate) fn from_array<const N: usize>(array: [T; N]) -> Self {
        let thin_vec = ThinVec::from_array(array);
        // SAFETY: thin_vec is fresh
        unsafe { Self::from_thin_vec_unchecked(thin_vec) }
    }

    #[inline]
    #[must_use]
    pub(crate) fn from_boxed_slice(slice: Box<[T]>) -> Self {
        Self::from_mut_vector(slice.into_vec())
    }

    #[inline]
    #[must_use]
    pub(crate) fn from_slice_clone(slice: &[T]) -> Self
    where
        T: Clone,
    {
        let thin_vec = ThinVec::from_slice_clone(slice);
        unsafe { Self::from_thin_vec_unchecked(thin_vec) }
    }

    /// Tries to clone the reference without cloning the data.
    ///
    /// If the reference count overflows ([`Unique`] always does), it returns `None`.
    ///
    /// [`Unique`]: crate::Unique
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::smart_thin_vec;
    /// # use hipstr::Unique;
    /// let v = smart_thin_vec![1, 2, 3];
    /// assert_eq!(v.as_slice(), &[1, 2, 3]);
    ///
    /// let v2 = v.try_clone().unwrap();
    /// assert_eq!(v.as_slice(), v2.as_slice());
    /// assert_eq!(v.as_ptr(), v2.as_ptr());
    ///
    /// let v = smart_thin_vec![Unique: 1, 2, 3];
    /// assert_eq!(v.as_slice(), &[1, 2, 3]);
    ///
    /// assert!(v.try_clone().is_none());
    /// ```
    #[must_use]
    pub fn try_clone(&self) -> Option<Self> {
        if let Some(count) = self.count() {
            if count.incr() == UpdateResult::Overflow {
                return None;
            }
        }
        Some(unsafe { self.copy() })
    }

    /// Converts into a [`ThinVec`] if the reference is unique.
    ///
    /// # Errors
    ///
    /// If the reference is not unique, it returns `Err(self)`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::smart_thin_vec;
    /// let v = smart_thin_vec![1, 2, 3];
    /// assert_eq!(v.as_slice(), &[1, 2, 3]);
    /// let t = v.into_thin_vec().unwrap();
    /// ```
    pub fn into_thin_vec(self) -> Result<ThinVec<T>, Self> {
        if self.is_unique() {
            let tv: ThinVec<T, B> = ThinVec(self.0);
            let _ = ManuallyDrop::new(self);
            Ok(tv.fresh_move())
        } else {
            Err(self)
        }
    }

    pub fn push(&mut self, value: T)
    where
        T: Clone,
    {
        self.mutate().push(value);
    }

    pub fn push_copy(&mut self, value: T)
    where
        T: Copy,
    {
        self.mutate_copy().push(value);
    }

    pub fn pop(&mut self) -> Option<T>
    where
        T: Clone,
    {
        self.mutate().pop()
    }

    pub fn pop_copy(&mut self) -> Option<T>
    where
        T: Copy,
    {
        self.mutate_copy().pop()
    }

    pub fn pop_if<F>(&mut self, f: F) -> Option<T>
    where
        T: Clone,
        F: FnMut(&mut T) -> bool,
    {
        self.mutate().pop_if(f)
    }

    pub fn pop_if_copy<F>(&mut self, f: F) -> Option<T>
    where
        T: Copy,
        F: FnMut(&mut T) -> bool,
    {
        self.mutate_copy().pop_if(f)
    }

    pub fn extend_from_slice(&mut self, other: &[T])
    where
        T: Clone,
    {
        if !other.is_empty() {
            self.mutate().extend_from_slice(other);
        }
    }

    pub fn extend_from_slice_copy(&mut self, other: &[T])
    where
        T: Copy,
    {
        if !other.is_empty() {
            self.mutate_copy().extend_from_slice_copy(other);
        }
    }

    pub fn append(&mut self, other: &mut impl Mutate<Item = T>)
    where
        T: Clone,
    {
        if !other.is_empty() {
            self.mutate().append(other.mutate().borrow_mut());
        }
    }
}

impl<T, C: Counter> Clone for SmartThinVec<T, BackendImpl<C, PanicOnOverflow>> {
    #[track_caller]
    fn clone(&self) -> Self {
        let Some(clone) = self.try_clone() else {
            panic!("count overflow");
        };
        clone
    }
}

impl<T: Clone, C: Counter> Clone for SmartThinVec<T, BackendImpl<C, CloneOnOverflow>> {
    fn clone(&self) -> Self {
        self.try_clone().unwrap_or_else(|| {
            let thin_vec: ThinVec<_, _> = self.as_thin_vec().fresh_clone();
            unsafe { Self::from_thin_vec_unchecked(thin_vec) }
        })
    }
}

impl<T, B: Backend> Drop for SmartThinVec<T, B> {
    fn drop(&mut self) {
        if let Some(count) = self.count() {
            // Decrement the reference count
            if count.decr() == UpdateResult::Overflow {
                // rewrap the repr into ThinVec to drop it
                let _: ThinVec<T, B> = ThinVec(self.0);
            }
        }
    }
}

impl<T, C: Backend> TryFrom<SmartThinVec<T, C>> for ThinVec<T, Reserved> {
    type Error = SmartThinVec<T, C>;

    fn try_from(value: SmartThinVec<T, C>) -> Result<Self, Self::Error> {
        value.into_thin_vec()
    }
}

impl<T, C: Backend> Default for SmartThinVec<T, C> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T, C: Backend> AsRef<[T]> for SmartThinVec<T, C> {
    fn as_ref(&self) -> &[T] {
        self.as_thin_vec().as_slice()
    }
}

trait_impls! {
    [T, C] where [C: Backend] {
        From {
            Vec<T> => SmartThinVec<T, C> = Self::from_mut_vector;
            Box<[T]> => SmartThinVec<T, C> = Self::from_boxed_slice;
        }
    }

    [T, C] where [T: core::fmt::Debug, C: Backend] {
        Debug {
            SmartThinVec<T, C>;
        }
    }

    [T, C] where [T: Clone, C: Backend] {
        From {
            &[T] => SmartThinVec<T, C> = Self::from_slice_clone;
            &mut [T] => SmartThinVec<T, C> = Self::from_slice_clone;
        }
    }

    [T, P: ConstDefault, C] where [C: Backend] {
        From {
            ThinVec<T, P> => SmartThinVec<T, C> = Self::from_thin_vec;
        }
    }

    [T, C, const N: usize] where [C: Backend] {
        From {
            [T; N] => SmartThinVec<T, C> = Self::from_array;
        }

    }

    [T, C, const N: usize] where [T: Clone, C: Backend] {
        From {
            &[T; N] => SmartThinVec<T, C> = Self::from_slice_clone;
            &mut [T; N] => SmartThinVec<T, C> = Self::from_slice_clone;
        }
    }


    [T, U, C1, C2] where [T: PartialEq<U>, C1: Backend, C2: Backend] {
        PartialEq {
            SmartThinVec<T, C1>, SmartThinVec<U, C2>;
        }
    }

    [T, C1, C2] where [T: PartialOrd, C1: Backend, C2: Backend] {
        PartialOrd {
            SmartThinVec<T, C1>, SmartThinVec<T, C2>;
        }
    }

    [T, U, C: Backend, P: ConstDefault] where [T: PartialEq<U>] {
        PartialEq {
            SmartThinVec<T, C>, ThinVec<U, P>;
            ThinVec<T, P>, SmartThinVec<U, C>;
        }
    }

    [T, C: Backend, P: ConstDefault] where [T: PartialOrd] {
        PartialOrd {
            SmartThinVec<T, C>, ThinVec<T, P>;
            ThinVec<T, P>, SmartThinVec<T, C>;
        }
    }

    [T, U, C] where [T: PartialEq<U>, C: Backend] {
        PartialEq {
            [T], SmartThinVec<U, C>;
            &[T], SmartThinVec<U, C>;
            &mut [T], SmartThinVec<U, C>;
            Vec<T>, SmartThinVec<U, C>;

            SmartThinVec<T, C>, [U];
            SmartThinVec<T, C>, &[U];
            SmartThinVec<T, C>, &mut[U];
            SmartThinVec<T, C>, Vec<U>;
        }
    }

    [T, U, C, const N: usize] where [T: PartialEq<U>, C: Backend] {
        PartialEq {
            [T; N], SmartThinVec<U, C>;
            SmartThinVec<T, C>, [U; N];
        }
    }

    [T, C] where [T: PartialOrd, C: Backend] {
        PartialOrd {
            Vec<T>, SmartThinVec<T, C>;
            SmartThinVec<T, C>, Vec<T>;

            [T], SmartThinVec<T, C>;
            SmartThinVec<T, C>, [T];

            &[T], SmartThinVec<T, C>;
            SmartThinVec<T, C>, &[T];

            &mut [T], SmartThinVec<T, C>;
            SmartThinVec<T, C>, &mut [T];
        }
    }

    [T, C, const N: usize] where [T: PartialOrd, C: Backend] {
        PartialOrd {
            [T; N], SmartThinVec<T, C>;
            SmartThinVec<T, C>, [T; N];
        }
    }
}

impl<T: Clone, B: Backend> Mutate for SmartThinVec<T, B> {
    type MutVector<'a>
        = ThinVec<T, B>
    where
        Self: 'a;

    type RefMut<'a>
        = &'a mut ThinVec<T, B>
    where
        Self: 'a;

    fn mutate(&mut self) -> Self::RefMut<'_> {
        self.mutate()
    }
}
