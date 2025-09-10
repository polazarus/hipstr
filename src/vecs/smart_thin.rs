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
use core::mem::ManuallyDrop;
use core::ops::Deref;

use const_default::ConstDefault;

use super::thin::{Reserved, ThinVec};
use crate::backend::{
    Backend, BackendImpl, CloneOnOverflow, Counter, PanicOnOverflow, UpdateResult,
};
use crate::common::traits::MutVector;
use crate::common::{manually_drop_as_mut, manually_drop_as_ref};
use crate::macros::trait_impls;

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
pub struct SmartThinVec<T, C: Backend>(pub(super) ManuallyDrop<ThinVec<T, C>>);

impl<T, C: Backend> Deref for SmartThinVec<T, C> {
    type Target = ThinVec<T, C>;

    fn deref(&self) -> &Self::Target {
        self.as_thin_vec()
    }
}

impl<T, C: Backend> SmartThinVec<T, C> {
    const EMPTY: Self = {
        let tv = ThinVec::new();
        unsafe { Self::from_thin_vec_unchecked(tv) }
    };

    /// Copies the smart vector without checking or updating the reference count.
    const unsafe fn copy(&self) -> Self {
        Self(ManuallyDrop::new(ThinVec(manually_drop_as_ref(&self.0).0)))
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

    const fn count(&self) -> Option<&C> {
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
    pub fn as_mut(&mut self) -> Option<&mut ThinVec<T, C>> {
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
    /// This function is unsafe because it allows mutable access to the vector even if it is not unique.
    /// The caller must ensure that no other references to the vector exist while this function is used.
    pub const unsafe fn as_mut_unchecked(&mut self) -> &mut ThinVec<T, C> {
        manually_drop_as_mut(&mut self.0)
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
    pub fn mutate(&mut self) -> &mut ThinVec<T, C>
    where
        T: Clone,
    {
        if !self.is_unique() {
            self.detach();
        }
        unsafe { self.as_mut_unchecked() }
    }

    fn detach(&mut self)
    where
        T: Clone,
    {
        let thin_vec: ThinVec<_, _> = self.as_thin_vec().fresh_clone();
        *self = unsafe { Self::from_thin_vec_unchecked(thin_vec) };
    }

    /// Creates a new `SmartThinVec` from a `ThinVec` without additional checks.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it assumes the input `ThinVec` has a consistent counter.
    /// Typically, this is the case when the `ThinVec` is created with a default counter.
    pub(crate) const unsafe fn from_thin_vec_unchecked(t: ThinVec<T, C>) -> Self {
        let thin_vec = ManuallyDrop::new(t);
        Self(thin_vec)
    }

    #[inline]
    #[must_use]
    pub(crate) const fn as_thin_vec(&self) -> &ThinVec<T, C> {
        manually_drop_as_ref(&self.0)
    }

    #[inline]
    #[must_use]
    pub(crate) fn from_thin_vec<P: ConstDefault>(thin_vec: ThinVec<T, P>) -> Self {
        let thin_vec = ThinVec::fresh_move(thin_vec);
        unsafe { Self::from_thin_vec_unchecked(thin_vec) }
    }

    #[inline]
    #[must_use]
    pub(crate) fn from_mut_vector(vector: impl MutVector<Item = T>) -> Self {
        let thin_vec = ThinVec::from_mut_vector(vector);
        unsafe { Self::from_thin_vec_unchecked(thin_vec) }
    }

    #[inline]
    #[must_use]
    pub(crate) fn from_array<const N: usize>(array: [T; N]) -> Self {
        let thin_vec = ThinVec::from_array(array);
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
            let mut this = ManuallyDrop::new(self);
            let tv = unsafe { ManuallyDrop::take(&mut this.0) };
            Ok(tv.fresh_move())
        } else {
            Err(self)
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

impl<T, C: Backend> Drop for SmartThinVec<T, C> {
    fn drop(&mut self) {
        if let Some(count) = self.count() {
            // Decrement the reference count
            if count.decr() == UpdateResult::Overflow {
                // SAFETY: if the count reaches zero, there is no other reference
                unsafe {
                    ManuallyDrop::drop(&mut self.0);
                }
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

impl<T, C: Backend> AsRef<ThinVec<T, C>> for SmartThinVec<T, C> {
    fn as_ref(&self) -> &ThinVec<T, C> {
        self.as_thin_vec()
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
