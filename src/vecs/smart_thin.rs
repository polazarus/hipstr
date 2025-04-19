//! Smart thin vector.
//!
//! This module provides a smart vector [`SmartThinVec`] that can be either
//! unique or shared (reference counted, atomically or not), with possible
//! copy-on-write semantics. As a wrapper around [`ThinVec`], [`SmartThinVec`]
//! is *thin*, i.e., the handle is one pointer wide.
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
use core::ptr;
use core::ptr::NonNull;

use super::thin::{Header, Reserved, ThinVec};
use crate::common::traits::MutVector;
use crate::macros::trait_impls;
use crate::smart::{CloneOnOverflow, PanicOnOverflow, SmartKind, UpdateResult};

#[cfg(test)]
mod tests;

/// Creates a new smart vector, [`SmartThinVec`], with array-like syntax.
///
/// # Examples
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
pub struct SmartThinVec<T, C: SmartKind>(pub(super) NonNull<Header<T, C>>);

impl<T, C: SmartKind> Deref for SmartThinVec<T, C> {
    type Target = ThinVec<T, C>;

    fn deref(&self) -> &Self::Target {
        self.as_thin_vec()
    }
}

impl<T, C: SmartKind> SmartThinVec<T, C> {
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
    pub fn new() -> Self {
        let tv = ThinVec::new();
        unsafe { Self::from_thin_vec_unchecked(tv) }
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
    pub fn with_capacity(capacity: usize) -> Self {
        let tv = ThinVec::with_capacity(capacity);
        unsafe { Self::from_thin_vec_unchecked(tv) }
    }

    fn count(&self) -> &C {
        self.prefix()
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
    pub fn is_unique(&self) -> bool {
        self.prefix().is_unique()
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
    ///     let v_mut = v.as_mut_vec().unwrap();
    ///     assert_eq!(v_mut.as_slice(), &[1, 2, 3]);
    ///     v_mut.push(4);
    /// }
    /// assert_eq!(v.as_slice(), &[1, 2, 3, 4]);
    ///
    /// let mut v2 = v.clone();
    /// assert!(!v.is_unique());
    /// assert!(v.as_mut_vec().is_none());
    /// ```
    pub fn as_mut_vec(&mut self) -> Option<&mut ThinVec<T, C>> {
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
    pub unsafe fn as_mut_unchecked(&mut self) -> &mut ThinVec<T, C> {
        unsafe { &mut *(self as *mut Self as *mut ThinVec<T, C>) }
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
    pub fn mutate(&mut self) -> &mut ThinVec<T, C>
    where
        T: Clone,
    {
        if !self.count().is_unique() {
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
    pub(crate) unsafe fn from_thin_vec_unchecked(t: ThinVec<T, C>) -> Self {
        let thin_vec = ManuallyDrop::new(t);
        Self(thin_vec.0)
    }

    pub(crate) fn as_thin_vec(&self) -> &ThinVec<T, C> {
        unsafe { &*(self as *const Self as *const ThinVec<T, C>) }
    }

    pub(crate) fn from_thin_vec<P>(thin_vec: ThinVec<T, P>) -> SmartThinVec<T, C> {
        let thin_vec = ThinVec::fresh_move(thin_vec);
        return unsafe { Self::from_thin_vec_unchecked(thin_vec) };
    }

    pub(crate) fn from_mut_vector(vector: impl MutVector<Item = T>) -> Self {
        let thin_vec = ThinVec::from_mut_vector(vector);
        unsafe { Self::from_thin_vec_unchecked(thin_vec) }
    }

    pub(crate) fn from_array<const N: usize>(array: [T; N]) -> Self {
        let thin_vec = ThinVec::from_array(array);
        unsafe { Self::from_thin_vec_unchecked(thin_vec) }
    }

    pub(crate) fn from_boxed_slice(slice: Box<[T]>) -> Self {
        let thin_vec = ThinVec::from_boxed_slice(slice);
        unsafe { Self::from_thin_vec_unchecked(thin_vec) }
    }

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
    pub fn try_clone(&self) -> Option<Self> {
        if self.count().incr() == UpdateResult::Overflow {
            None
        } else {
            Some(Self(self.0))
        }
    }

    /// Converts into a [`ThinVec`] if the reference is unique. Otherwise, it
    /// returns `Err(self)`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::smart_thin_vec;
    /// let v = smart_thin_vec![1, 2, 3];
    /// assert_eq!(v.as_slice(), &[1, 2, 3]);
    /// let t = v.into_thin_vec().unwrap();
    /// ```
    pub fn into_thin_vec(self) -> Result<ThinVec<T>, SmartThinVec<T, C>> {
        if self.is_unique() {
            let this = ManuallyDrop::new(self);
            let tv = ThinVec(this.0);
            Ok(tv.fresh_move())
        } else {
            Err(self)
        }
    }
}

impl<T, C: SmartKind> Clone for SmartThinVec<T, PanicOnOverflow<C>> {
    fn clone(&self) -> Self {
        self.try_clone().unwrap_or_else(|| panic!("count overflow"))
    }
}

impl<T: Clone, C: SmartKind> Clone for SmartThinVec<T, CloneOnOverflow<C>> {
    fn clone(&self) -> Self {
        self.try_clone().unwrap_or_else(|| {
            let thin_vec: ThinVec<_, _> = self.as_thin_vec().fresh_clone();
            unsafe { Self::from_thin_vec_unchecked(thin_vec) }
        })
    }
}

impl<T, C: SmartKind> Drop for SmartThinVec<T, C> {
    fn drop(&mut self) {
        if self.count().decr() == UpdateResult::Overflow {
            unsafe {
                let thin_vec_ptr = self as *mut Self as *mut ThinVec<T, C>;
                ptr::drop_in_place(thin_vec_ptr);
            }
        }
    }
}

impl<T, C: SmartKind> TryFrom<SmartThinVec<T, C>> for ThinVec<T, Reserved> {
    type Error = SmartThinVec<T, C>;

    fn try_from(value: SmartThinVec<T, C>) -> Result<Self, Self::Error> {
        value.into_thin_vec()
    }
}

trait_impls! {
    [T, C] where [C: SmartKind] {
        From {
            Vec<T> => SmartThinVec<T, C> = Self::from_mut_vector;
            Box<[T]> => SmartThinVec<T, C> = Self::from_boxed_slice;
        }
    }

    [T, C] where [T: core::fmt::Debug, C: SmartKind] {
        Debug {
            SmartThinVec<T, C>;
        }
    }

    [T, C] where [T: Clone, C: SmartKind] {
        From {
            &[T] => SmartThinVec<T, C> = Self::from_slice_clone;
            &mut [T] => SmartThinVec<T, C> = Self::from_slice_clone;
        }
    }

    [T, P, C] where [C: SmartKind] {
        From {
            ThinVec<T, P> => SmartThinVec<T, C> = Self::from_thin_vec;
        }
    }

    [T, C, const N: usize] where [C: SmartKind] {
        From {
            [T; N] => SmartThinVec<T, C> = Self::from_array;
        }

    }

    [T, C, const N: usize] where [T: Clone, C: SmartKind] {
        From {
            &[T; N] => SmartThinVec<T, C> = Self::from_slice_clone;
            &mut [T; N] => SmartThinVec<T, C> = Self::from_slice_clone;
        }
    }


    [T, U, C1, C2] where [T: PartialEq<U>, C1: SmartKind, C2: SmartKind] {
        PartialEq {
            SmartThinVec<T, C1>, SmartThinVec<U, C2>;
        }
    }

    [T, C1, C2] where [T: PartialOrd, C1: SmartKind, C2: SmartKind] {
        PartialOrd {
            SmartThinVec<T, C1>, SmartThinVec<T, C2>;
        }
    }

    [T, U, C, P] where [T: PartialEq<U>, C: SmartKind] {
        PartialEq {
            SmartThinVec<T, C>, ThinVec<U, P>;
            ThinVec<T, P>, SmartThinVec<U, C>;
        }
    }

    [T, C, P] where [T: PartialOrd, C: SmartKind] {
        PartialOrd {
            SmartThinVec<T, C>, ThinVec<T, P>;
            ThinVec<T, P>, SmartThinVec<T, C>;
        }
    }

    [T, U, C] where [T: PartialEq<U>, C: SmartKind] {
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

    [T, U, C, const N: usize] where [T: PartialEq<U>, C: SmartKind] {
        PartialEq {
            [T; N], SmartThinVec<U, C>;
            SmartThinVec<T, C>, [U; N];
        }
    }

    [T, C] where [T: PartialOrd, C: SmartKind] {
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

    [T, C, const N: usize] where [T: PartialOrd, C: SmartKind] {
        PartialOrd {
            [T; N], SmartThinVec<T, C>;
            SmartThinVec<T, C>, [T; N];
        }
    }
}
