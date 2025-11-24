//! Inline vector and related types.
//!
//! This module provides an inline vector implementation that can store up to a
//! small and fixed number of elements inline.
//!
//! Particularly space efficient, this implementation may in some case be more
//! efficient than the standard library vectors.
//!
//! The actual size of the inline vector is set through a type-level number (see
//! [`typenum`] and [`generic_array`]). It must be a non-zero multiple of the
//! platform's pointer size (16, 32, or 64 bits for now).

use alloc::borrow::Cow;
use alloc::boxed::Box;
use alloc::vec::Vec;
use core::borrow::BorrowMut;
use core::fmt::{self};
use core::mem::MaybeUninit;
use core::ops::{Range, RangeBounds};
use core::ptr::NonNull;
use core::{error, iter, slice};

use const_default::ConstDefault;
use rules_derive::rules_derive;

use self::repr::InlineRepr;
use crate::common::derives::{
    AsRef, ConstDefault, Copy, DelegateDebug, DelegateHash, Deref, From, FromIterator,
    IntoIterator, MutVector,
};
use crate::common::drain::Drain;
use crate::common::into_iter::IntoIter;
use crate::common::methods::{
    append_impl, extend_from_array_impl, extend_from_slice_impl, from_array_impl,
    from_slice_clone_impl, pop_if_impl, pop_impl, push_within_capacity, remove_unchecked_impl,
    resize_impl, spare_capacity_mut_impl, split_off_impl, swap_remove_impl, truncate_impl,
};
use crate::common::traits::{MutVector, Mutate, Vector};
use crate::common::{drop_raw_slice, unwrap_display, SliceWriteGuard};
use crate::{common, macros};

pub(crate) mod length;
pub(crate) mod repr;

#[cfg(test)]
mod tests;

// Re-exported for documentation.
pub use self::length::{InlineLength, PointerSize};

/// A vector that can store a small number of elements inline.
///
/// This struct is designed to be used in situations where the maximum number of
/// elements is small and known at compile time. It uses a fixed-size array
/// internally to store the elements, and it can be more efficient than using a
/// heap-allocated vector for small collections.
///
/// # Generic parameters
///
/// - `T`, the type of the elements stored in the vector.
/// - `L`, the type of the tagged length, one of: `u8`, `u16`, `u32`, `u64`, and `usize`.
///
/// # Examples
///
/// ```
/// use hipstr::vecs::InlineVec;
/// use typenum::U8;
/// let mut inline = InlineVec::<u8, U8>::new();
/// assert_eq!(inline.len(), 0);
/// assert_eq!(inline.capacity(), 7);
/// inline.push(1);
/// assert_eq!(inline.len(), 1);
/// assert_eq!(inline.as_slice(), &[1]);
/// ```
///
/// # Zero-sized types
///
/// `InlineVec` is not well suited to store zero-sized types (ZSTs) like `()`.
/// This is because the maximal length is capped by `u8::MAX >> SHIFT`.
#[repr(C)]
#[rules_derive(
    ConstDefault(Self::new()),
    DelegateDebug(Self::as_slice where T: core::fmt::Debug),
    DelegateHash(Self::as_slice where T: core::hash::Hash),
    AsRef([T], Self::as_slice, Self::as_mut_slice),
    Deref([T], Self::as_slice, Self::as_mut_slice),
    MutVector(T),
    FromIterator(T, Self::from_iter),
    IntoIterator(T, IntoIter<Self>, IntoIter::new)
)]
pub struct InlineVec<T, L: InlineLength>(InlineRepr<T, L>);

impl<T, L: InlineLength> InlineVec<T, L> {
    /// The capacity of the inline vector, that is, the maximum number of elements
    /// it can hold.
    pub(crate) const CAPACITY: usize = InlineRepr::<T, L>::CAPACITY;

    /// Creates a new inline vector with the specified capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::InlineVec;
    /// use typenum::U8;
    /// let inline = InlineVec::<u8, U8>::new();
    /// assert_eq!(inline.len(), 0);
    /// assert_eq!(inline.capacity(), 7);
    /// ```
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self(InlineRepr::new())
    }

    /// Creates a new inline vector while checking the specified capacity.
    ///
    /// Provided for consistency with other vector types.
    ///
    /// # Panics
    ///
    /// Panics if the specified capacity exceeds the inline vector's capacity.
    ///
    /// # Examples
    ///
    /// ```should_panic
    /// use hipstr::vecs::InlineVec;
    /// use typenum::U8;
    /// let inline = InlineVec::<u8, U8>::with_capacity(8);
    /// // 8-byte sized vector cannnot hold 8 bytes
    /// ```
    #[inline]
    #[must_use]
    #[track_caller]
    pub const fn with_capacity(cap: usize) -> Self {
        assert!(
            cap <= Self::CAPACITY,
            "required capacity exceeds inline capacity"
        );
        Self::new()
    }

    /// Ensures that the inline vector has enough capacity to hold `additional` more elements.
    ///
    /// Provided for consistency with other vector types.
    ///
    /// # Panics
    ///
    /// Panics if the new length exceeds the capacity of the inline vector.
    ///
    /// # Examples
    ///
    /// ```should_panic
    /// use hipstr::vecs::InlineVec;
    /// use typenum::U8;
    /// let mut inline = InlineVec::<u8, U8>::new();
    /// inline.reserve(5); // ok
    /// inline.reserve(8); // panics
    /// ```
    #[inline]
    #[track_caller]
    pub const fn reserve(&mut self, additional: usize) {
        assert!(
            self.len() + additional <= Self::CAPACITY,
            "new length exceeds capacity"
        );
    }

    /// Creates a new inline vector with the specified length, initialized to
    /// zero.
    ///
    /// # Safety
    ///
    /// - The caller must ensure that the length is less than or equal to the
    ///   capacity of the inline vector.
    /// - The caller must ensure that the elements are initialized.
    #[inline]
    pub(crate) const unsafe fn zeroed(new_len: usize) -> Self {
        assert!(new_len <= Self::CAPACITY, "new length exceeds capacity");
        // SAFETY: the caller must ensure that the elements are zeroable
        let mut new = Self(unsafe { InlineRepr::<T, L>::zeroed() });
        // SAFETY: the elements are zeroed by construction
        unsafe {
            new.set_len(new_len);
        }
        new
    }

    /// Drops the contents of the inline vector.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the inline vector is not used after drop.
    #[inline]
    pub(super) unsafe fn drop_contents(&mut self) {
        unsafe { drop_raw_slice(self.as_mut_ptr(), self.len()) };
    }

    /// Creates a new inline vector from an array by moving the element.
    ///
    /// # Panics
    ///
    /// Panics if the array's length exceeds the capacity of the inline vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::InlineVec;
    /// use typenum::{U8, U16};
    /// let array = [1, 2, 3];
    /// let inline = InlineVec::<u8, U8>::from_array(array);
    /// assert_eq!(inline.as_slice(), array);
    ///
    /// let array = [Box::new(42)];
    /// let inline = InlineVec::<Box<u8>, U16>::from_array(array);
    /// assert_eq!(inline.len(), 1);
    /// assert_eq!(*inline[0], 42);
    /// ```
    #[inline]
    #[must_use]
    #[track_caller]
    pub const fn from_array<const N: usize>(array: [T; N]) -> Self {
        from_array_impl!(array)
    }

    /// Creates a new inline vector from a boxed slice by moving the elements.
    ///
    /// # Panics
    ///
    /// Panics if the boxed slice's length exceeds the capacity of the inline
    /// vector.
    #[must_use]
    pub(crate) fn from_boxed_slice(boxed: Box<[T]>) -> Self {
        Self::from_vector(boxed.into_vec())
    }

    #[must_use]
    pub(crate) fn from_vector(mut vec: impl Mutate<Item = T>) -> Self {
        let mut this = Self::new();
        this.append(&mut vec);
        this
    }

    #[must_use]
    pub(crate) fn from_iter(iterable: impl IntoIterator<Item = T>) -> Self {
        let iter = iterable.into_iter();
        let min = iter.size_hint().0;
        assert!(
            min <= Self::CAPACITY,
            "iterator's minimal length exceeds capacity"
        );
        let mut this = Self::new();
        for item in iter {
            this.push(item);
        }
        this
    }

    /// Returns the length of the inline vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::InlineVec;
    /// use typenum::U8;
    /// let mut inline = InlineVec::<u8, U8>::new();
    /// assert_eq!(inline.len(), 0);
    /// inline.push(1);
    /// assert_eq!(inline.len(), 1);
    /// inline.push(2);
    /// assert_eq!(inline.len(), 2);
    /// ```
    #[inline]
    #[must_use]
    pub const fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns `true` if the inline vector is empty, `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::InlineVec;
    /// use typenum::U8;
    /// let mut inline = InlineVec::<u8, U8>::new();
    /// assert!(inline.is_empty());
    /// inline.push(1);
    /// assert!(!inline.is_empty());
    /// ```
    #[inline]
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns a slice of the inline vector.
    #[inline]
    pub const fn as_slice(&self) -> &[T] {
        unsafe { slice::from_raw_parts(self.as_ptr(), self.len()) }
    }

    /// Returns a mutable slice of the inline vector.
    #[inline]
    pub const fn as_mut_slice(&mut self) -> &mut [T] {
        unsafe { slice::from_raw_parts_mut(self.as_mut_ptr(), self.len()) }
    }

    /// Returns the capacity of the inline vector, that is, `CAP`.
    ///
    /// Convenience method to get the capacity of the inline vector, like any
    /// other vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::InlineVec;
    /// use typenum::U8;
    /// let inline = InlineVec::<u8, U8>::new();
    /// assert_eq!(inline.capacity(), 7);
    /// ```
    #[inline]
    #[allow(clippy::unused_self, reason = "Vec-like behavior")]
    pub const fn capacity(&self) -> usize {
        Self::CAPACITY
    }

    /// Returns a pointer to the inline vector.
    ///
    /// The caller must ensure that the vector outlives the pointer this
    /// function returns, or else it will end up dangling. Moving the vector
    /// would also make any pointers to it invalid.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::InlineVec;
    /// use typenum::U8;
    /// let mut inline = InlineVec::<u8, U8>::new();
    /// inline.push(1);
    /// assert_eq!(inline.len(), 1);
    /// assert_eq!(unsafe { inline.as_ptr().read() }, 1);
    /// ```
    #[inline]
    pub const fn as_ptr(&self) -> *const T {
        self.0.as_ptr()
    }

    /// Returns a `NonNull` pointer to the inline vector data.
    ///
    /// The caller must ensure that the vector outlives the pointer this
    /// function returns, or else it will end up dangling. Moving the vector
    /// would also make any pointers to it invalid.
    #[inline]
    pub const fn as_non_null(&mut self) -> NonNull<T> {
        self.0.as_non_null()
    }

    /// Returns a mutable pointer to the inline vector.
    ///
    /// The caller must ensure that the vector outlives the pointer this
    /// function returns, or else it will end up dangling. Moving the vector
    /// would also make any pointers to it invalid.
    #[inline]
    pub const fn as_mut_ptr(&mut self) -> *mut T {
        self.0.as_mut_ptr()
    }

    /// Appends a value to the back of the inline vector if the vector is not
    /// full.
    ///
    /// # Errors
    ///
    /// Returns `Err(value)` if the inline vector is full, that is, the current
    /// [`len`] is equal to the vector's capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::inline_vec;
    /// let mut inline = inline_vec![8 => 1_u8, 2, 3, 4, 5, 6];
    /// assert_eq!(inline.capacity(), 7);
    /// assert_eq!(inline.push_within_capacity(7), Ok(()));
    /// assert_eq!(inline.push_within_capacity(8), Err(8));
    /// ```
    ///
    /// [`len`]: Self::len
    #[inline]
    #[doc(alias = "try_push")]
    pub const fn push_within_capacity(&mut self, value: T) -> Result<(), T> {
        push_within_capacity!(self, value)
    }

    /// Appends a value to the back of the inline vector.
    ///
    /// # Panics
    ///
    /// Panics if the inline vector is full, that is, the current [`len`] is
    /// equal to the vector's capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::InlineVec;
    /// use typenum::U8;
    /// let mut inline = InlineVec::<u8, U8>::new();
    /// inline.push(1);
    /// assert_eq!(inline.len(), 1);
    /// assert_eq!(inline.as_slice(), &[1]);
    /// ```
    ///
    /// [`len`]: Self::len
    #[inline]
    #[track_caller]
    pub fn push(&mut self, value: T) {
        assert!(
            self.push_within_capacity(value).is_ok(),
            "inline vector is full"
        );
    }

    /// Forces the length of the inline vector to `new_len`.
    ///
    /// This function is designed to work in combination with
    /// [`spare_capacity_mut`] or raw pointer shenanigans.
    ///
    /// <div class="warning">
    ///
    /// Other use cases include FFI, where FFI calls are responsible for
    /// initializing the elements. Note that this raises some serious security
    /// concerns: it exposes stack addresses to potentially unsafe and unsound
    /// code.
    ///
    /// </div>
    ///
    /// # Safety
    ///
    /// - `new_len` must be less than or equal to the capacity of the inline
    ///   vector.
    /// - The elements at `old_len..new_len` must be initialized.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::InlineVec;
    /// use typenum::U8;
    /// let mut inline = InlineVec::<u8, U8>::new();
    /// assert!(inline.capacity() >= 1);
    /// inline.spare_capacity_mut()[0].write(1);
    /// unsafe {
    ///     inline.set_len(1);
    /// }
    /// ```
    ///
    /// [`spare_capacity_mut`]: Self::spare_capacity_mut
    #[inline]
    pub const unsafe fn set_len(&mut self, new_len: usize) {
        debug_assert!(new_len <= Self::CAPACITY, "new length exceeds capacity");
        unsafe {
            self.0.set_len(new_len);
        }
    }

    /// Returns a mutable slice of the spare capacity of the inline vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::InlineVec;
    /// use typenum::U8;
    /// let mut inline = InlineVec::<u8, U8>::new();
    /// assert_eq!(inline.spare_capacity_mut().len(), 7);
    /// inline.spare_capacity_mut()[0].write(5);
    /// unsafe {
    ///     inline.set_len(1);
    /// }
    /// ```
    #[inline]
    pub const fn spare_capacity_mut(&mut self) -> &mut [MaybeUninit<T>] {
        spare_capacity_mut_impl!(self)
    }

    /// Removes the last element from the inline vector and returns it, or `None`
    /// if the array is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::InlineVec;
    /// use typenum::U8;
    /// let mut inline = InlineVec::<u8, U8>::new();
    /// inline.push(1);
    /// assert_eq!(inline.pop(), Some(1));
    /// assert_eq!(inline.pop(), None);
    /// ```
    pub const fn pop(&mut self) -> Option<T> {
        pop_impl!(self)
    }

    /// Removes and returns the last element from a vector if the predicate
    /// returns `true`, or [`None`] if the predicate returns false or the vector
    /// is empty.
    ///
    /// The predicate is not called if the vector is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::inline_vec;
    /// use typenum::U8;
    /// let mut inline = inline_vec![8 => 1_u8, 2, 3, 4];
    /// assert_eq!(inline.pop_if(|x| *x % 2 == 0), Some(4));
    /// assert_eq!(inline.as_slice(), &[1, 2, 3]);
    /// assert_eq!(inline.pop_if(|x| *x % 2 == 0), None);
    /// ```
    pub fn pop_if(&mut self, f: impl FnOnce(&mut T) -> bool) -> Option<T> {
        pop_if_impl!(self, f)
    }

    /// Moves all the elements of `other` into `self`, leaving `other` empty.
    ///
    /// # Panics
    ///
    /// Panics if the new length exceeds the capacity of the inline vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::inline_vec;
    /// let mut inline1 = inline_vec![8 => 1_u8, 2];
    /// let mut inline2 = inline_vec![8 => 3_u8, 4];
    /// let mut vec = vec![5 , 6];
    /// inline1.append(&mut inline2);
    /// assert_eq!(inline1, [1, 2, 3, 4]);
    /// assert!(inline2.is_empty());
    /// inline1.append(&mut vec);
    /// assert_eq!(inline1, [1, 2, 3, 4, 5, 6]);
    /// assert!(vec.is_empty());
    /// ```
    pub fn append(&mut self, other: &mut impl Mutate<Item = T>) {
        let mut other = other.mutate();
        let other = other.borrow_mut();

        append_impl!(self, other);
    }

    /// Moves all the elements of `other` into `self`, leaving `other` empty.
    ///
    /// This function is similar to [`append`] but is designed to be usable in
    /// constant contexts.
    ///
    /// [`append`]: Self::append
    ///
    /// # Panics
    ///
    /// Panics if the new length exceeds the capacity of the inline vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::inline_vec;
    /// let mut inline1 = inline_vec![8 => 1_u8, 2];
    /// let mut inline2 = inline_vec![8 => 3_u8, 4];
    /// inline1.const_append(&mut inline2);
    /// assert_eq!(inline1, [1, 2, 3, 4]);
    /// assert!(inline2.is_empty());
    /// ```
    pub const fn const_append<L2: InlineLength>(&mut self, other: &mut InlineVec<T, L2>) {
        append_impl!(self, other);
    }

    /// Clears the inline vector, removing all elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::InlineVec;
    /// use typenum::U8;
    /// let mut inline = InlineVec::<u8, U8>::new();
    /// inline.push(1);
    /// inline.push(2);
    /// assert_eq!(inline.len(), 2);
    /// inline.clear();
    /// assert_eq!(inline.len(), 0);
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        self.truncate(0);
    }

    /// Truncates the inline vector to the specified length, dropping any excess
    /// elements.
    ///
    /// Do nothing if the new length is greater than or equal to the current
    /// length.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::InlineVec;
    /// use typenum::U8;
    /// let mut inline = InlineVec::<u8, U8>::new();
    /// inline.push(1);
    /// inline.push(2);
    /// assert_eq!(inline.len(), 2);
    /// inline.truncate(1);
    /// assert_eq!(inline.len(), 1);
    /// inline.truncate(0);
    /// assert_eq!(inline.len(), 0);
    /// ```
    pub fn truncate(&mut self, new_len: usize) {
        truncate_impl!(self, new_len);
    }

    /// Removes and returns the element at the specified index, replacing it
    /// with the last element.
    ///
    /// This operation is useful for efficiently removing elements when the
    /// order of elements does not need to be preserved.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::InlineVec;
    /// use typenum::U8;
    /// let mut inline = InlineVec::<u8, U8>::new();
    /// inline.push(1);
    /// inline.push(2);
    /// inline.push(3);
    /// assert_eq!(inline.swap_remove(1), 2);
    /// assert_eq!(inline.as_slice(), &[1, 3]);
    /// ```
    #[track_caller]
    pub const fn swap_remove(&mut self, index: usize) -> T {
        swap_remove_impl!(self, index)
    }

    /// Inserts an element at the specified index, shifting all elements after
    /// it to the right.
    ///
    /// # Panics
    ///
    /// Panics if either:
    ///
    /// - `index` is out of bounds, i.e., strictly greater than [`len`],
    /// - the inline vector is full, i.e., [`len`] is already equal to the
    ///   vector capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::InlineVec;
    /// use typenum::U8;
    /// let mut inline = InlineVec::<u8, U8>::new();
    /// inline.push(1);
    /// inline.push(3);
    /// inline.insert(1, 2);
    /// assert_eq!(inline.as_slice(), &[1, 2, 3]);
    /// ```
    ///
    /// [`len`]: Self::len
    #[track_caller]
    pub fn insert(&mut self, index: usize, value: T) {
        if let Err(err) = self.try_insert(index, value) {
            panic!("{}", err.message());
        }
    }

    /// Attempts to insert an element at the specified index, shifting all
    /// elements after it to the right.
    ///
    /// # Errors
    ///
    /// Returns an `InsertError` if either:
    /// - `index` is out of bounds, i.e., strictly greater than [`len`]
    /// - the inline vector is full, i.e., [`len`] is already equal to `CAP`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::InlineVec;
    /// use typenum::U8;
    /// let mut inline = InlineVec::<u8, U8>::new();
    /// inline.try_insert(0, 1).unwrap();
    /// inline.try_insert(1, 2).unwrap();
    /// inline.try_insert(4, 3).expect_err("out of bounds");
    /// inline.try_insert(2, 3).unwrap();
    /// inline.try_insert(3, 4).unwrap();
    /// inline.try_insert(4, 5).unwrap();
    /// inline.try_insert(5, 6).unwrap();
    /// inline.try_insert(6, 7).unwrap();
    /// inline.try_insert(0, 8).expect_err("full");
    /// ```
    ///
    /// [`len`]: Self::len
    pub const fn try_insert(&mut self, index: usize, value: T) -> Result<(), InsertError<T>> {
        let len = self.len();
        if index > len {
            return Err(InsertError::new(value, InsertErrorKind::OutOfBounds));
        } else if len == Self::CAPACITY {
            // inline vector is full
            return Err(InsertError::new(value, InsertErrorKind::Full));
        }

        // SAFETY: inline vector has enough capacity to hold the new element
        unsafe {
            let ptr = self.as_mut_ptr().add(index);

            ptr.copy_to(ptr.add(1), len - index);
            ptr.write(value);

            self.set_len(len + 1);
        }
        Ok(())
    }

    /// Removes and returns the element at the specified index, shifting all
    /// elements after it to the left.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::InlineVec;
    /// use typenum::U8;
    /// let mut inline = InlineVec::<u8, U8>::new();
    /// inline.push(1);
    /// inline.push(2);
    /// inline.push(3);
    /// assert_eq!(inline.remove(1), 2);
    /// assert_eq!(inline.as_slice(), &[1, 3]);
    /// ```
    #[track_caller]
    #[inline]
    pub const fn remove(&mut self, index: usize) -> T {
        assert!(index < self.len(), "index out of bounds");
        // SAFETY: index checked above
        unsafe { self.remove_unchecked(index) }
    }

    /// Removes and returns the element at the specified index, shifting all
    /// elements after it to the left, without doing any bounds checking.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `index` is less than the current length of
    /// the inline vector.
    pub const unsafe fn remove_unchecked(&mut self, index: usize) -> T {
        remove_unchecked_impl!(self, index)
    }

    /// Splits the inline vector into two at the given index.
    ///
    /// Returns a new `InlineVec` containing the elements after the given index.
    /// The original `InlineVec` will be truncated to the given index.
    ///
    /// # Panics
    ///
    /// Panics if `at` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::InlineVec;
    /// use typenum::U8;
    /// let mut inline = InlineVec::<u8, U8>::new();
    /// inline.push(1);
    /// inline.push(2);
    /// inline.push(3);
    /// let other = inline.split_off(1);
    /// assert_eq!(inline.as_slice(), &[1]);
    /// assert_eq!(other.as_slice(), &[2, 3]);
    /// ```
    #[must_use = "use .truncate() if you don't need the other part"]
    pub const fn split_off(&mut self, at: usize) -> Self {
        split_off_impl!(self, at)
    }

    /// Resizes the inline vector to the specified length using a closure to
    /// generate new values.
    ///
    /// If the new length is greater than the current length, the vector is
    /// extended with values generated by the closure. If the new length is
    /// less than the current length, the vector is truncated.
    ///
    /// # Panics
    ///
    /// Panics if the new length exceeds the capacity of the inline vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::InlineVec;
    /// use typenum::U8;
    /// let mut inline = InlineVec::<u8, U8>::new();
    /// inline.resize_with(3, || 42);
    /// assert_eq!(inline.as_slice(), &[42, 42, 42]);
    /// inline.resize_with(1, || 0);
    /// assert_eq!(inline.as_slice(), &[42]);
    /// ```
    pub fn resize_with<F>(&mut self, new_len: usize, f: F)
    where
        F: FnMut() -> T,
    {
        resize_impl!(self, new_len, iter::repeat_with(f));
    }

    /// Appends an array of elements to the inline vector, by moving the
    /// elements from the array into the inline vector.
    ///
    /// The array's length `N` is checked at compile time to be less than or
    /// equal to the `CAP` generic const parameter.
    ///
    /// # Panics
    ///
    /// Panics if the new length exceeds the capacity of the inline vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::inline_vec;
    /// let mut inline = inline_vec![8 => 1_u8, 2];
    /// inline.extend_from_array([3, 4]);
    /// assert_eq!(inline.as_slice(), &[1, 2, 3, 4]);
    /// ```
    #[doc(alias = "push_array")]
    #[track_caller]
    pub const fn extend_from_array<const N: usize>(&mut self, array: [T; N]) {
        extend_from_array_impl!(self, array);
    }

    /// Removes the subslice indicated by the given range from the inline
    /// vector, returning a double-ended iterator over the removed subslice.
    ///
    /// If the iterator is dropped before being fully consumed, it drops the
    /// remaining removed elements.
    ///
    /// The returned iterator keeps a mutable borrow on the vector to optimize
    /// its implementation.
    ///
    /// # Panics
    ///
    /// Panics if the starting point is greater than the end point or if the end
    /// point is greater than the length of the vector.
    ///
    /// # Leaking
    ///
    /// If the returned iterator goes out of scope without being dropped (due to
    /// [`std::mem::forget`], for example), the vector may have lost and leaked
    /// elements arbitrarily, including elements outside the range.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::vecs::InlineVec;
    /// # use hipstr::inline_vec;
    /// # use typenum::U8;
    /// let mut v: InlineVec<u8, U8> = inline_vec![1, 2, 3];
    /// let u: InlineVec<u8, U8> = v.drain(1..).collect();
    /// assert_eq!(v, &[1]);
    /// assert_eq!(u, &[2, 3]);
    ///
    /// // A full range clears the vector, like `clear()` does
    /// v.drain(..);
    /// assert_eq!(v, &[]);
    /// ```
    pub fn drain(&mut self, range: impl RangeBounds<usize>) -> Drain<'_, Self> {
        unwrap_display(Drain::new(self, range))
    }
}

impl<T, L: InlineLength> InlineVec<T, L>
where
    T: Clone,
{
    /// Creates a new inline vector from a slice by cloning the element.
    ///
    /// # Panics
    ///
    /// Panics if the length of the slice exceeds the capacity of the inline
    /// vector.
    #[inline]
    #[track_caller]
    pub(crate) fn from_slice_clone(slice: &[T]) -> Self {
        from_slice_clone_impl!(slice)
    }

    pub(crate) fn from_cow(cow: Cow<'_, [T]>) -> Self
    where
        T: Clone,
    {
        match cow {
            Cow::Borrowed(slice) => Self::from_slice_clone(slice),
            Cow::Owned(vec) => Self::from_vector(vec),
        }
    }

    /// Appends a slice of elements to the inline vector.
    ///
    /// If `T` implements `Copy`, see [`extend_from_slice_copy`] for a more
    /// efficient version.
    ///
    /// # Panics
    ///
    /// Panics if the new length exceeds the capacity of the inline vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::inline_vec;
    /// let mut inline = inline_vec![8 => 1_u8, 2];
    /// inline.extend_from_slice_copy(&[3, 4]);
    /// assert_eq!(inline.as_slice(), &[1, 2, 3, 4]);
    /// ```
    ///
    /// [`extend_from_slice_copy`]: Self::extend_from_slice_copy
    #[doc(alias = "push_slice_clone")]
    #[track_caller]
    pub fn extend_from_slice(&mut self, slice: &[T]) {
        extend_from_slice_impl!(self, slice);
    }

    /// Given a range `src`, clones a slice of elements in that range and
    /// appends it to the end.
    ///
    /// # Panics
    ///
    /// Panics if the source range is invalid or if the new length exceeds the
    /// capacity of the inline vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::inline_vec;
    /// let mut characters = inline_vec![48 => 'a', 'b', 'c', 'd', 'e'];
    /// characters.extend_from_within(2..);
    /// assert_eq!(characters, ['a', 'b', 'c', 'd', 'e', 'c', 'd', 'e']);
    ///
    /// let mut numbers = inline_vec![8 => 0_u8, 1, 2, 3, 4];
    /// numbers.extend_from_within(..2);
    /// assert_eq!(numbers, [0, 1, 2, 3, 4, 0, 1]);
    ///
    /// let mut strings = inline_vec![128 => String::from("hello"), String::from("world"), String::from("!")];
    /// strings.extend_from_within(1..=2);
    /// assert_eq!(strings, ["hello", "world", "!", "world", "!"]);
    /// ```
    #[track_caller]
    pub fn extend_from_within(&mut self, range: impl RangeBounds<usize>) {
        let range = common::range(range, self.len()).unwrap_or_else(|err| {
            panic!("{err}");
        });
        // SAFETY: valid range
        unsafe {
            self.extend_from_within_range(range);
        }
    }

    /// # Safety
    ///
    /// Valid range.
    unsafe fn extend_from_within_range(&mut self, range: Range<usize>) {
        let len = self.len();
        let range_len = range.len();
        let new_len = len + range_len;
        assert!(new_len <= Self::CAPACITY, "new length exceeds capacity");

        let ptr = self.as_mut_ptr();
        let mut slice_guard = SliceWriteGuard::new(unsafe { ptr.add(len) }, range_len);

        for src in range {
            // SAFETY: valid range
            let value = unsafe { &*ptr.add(src) };
            let clone = value.clone();
            // SAFETY: the source and destination are in the initialized range
            unsafe {
                slice_guard.write(clone);
            }
        }

        slice_guard.complete();
        unsafe {
            self.set_len(new_len);
        }
    }

    /// Resizes the inline vector to the specified length.
    ///
    /// If the new length is greater than the current length, the array is
    /// extended with the given value. If the new length is less than the
    /// current length, the array is truncated.
    ///
    /// # Panics
    ///
    /// Panics if the new length exceeds the capacity of the inline vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::InlineVec;
    /// use typenum::U8;
    /// let mut inline = InlineVec::<u8, U8>::new();
    /// inline.resize(3, 42);
    /// assert_eq!(inline.as_slice(), &[42, 42, 42]);
    /// inline.resize(1, 0);
    /// assert_eq!(inline.as_slice(), &[42]);
    /// ```
    pub fn resize(&mut self, new_len: usize, value: T) {
        resize_impl!(
            self,
            new_len,
            iter::repeat_n(value, new_len.saturating_sub(self.len()))
        );
    }
}

impl<T, L: InlineLength> InlineVec<T, L>
where
    T: Copy,
{
    /// Creates a new inline vector from a slice by copying the element.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::InlineVec;
    /// use typenum::U8;
    /// let array = [1, 2, 3];
    /// let inline = InlineVec::<u8, U8>::from_slice_copy(&array);
    /// assert_eq!(inline.as_slice(), array);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the length of the slice exceeds the capacity of the inline
    /// vector.
    pub const fn from_slice_copy(slice: &[T]) -> Self {
        let mut this = Self::with_capacity(slice.len());
        this.extend_from_slice_copy(slice);
        this
    }

    /// Creates a new inline vector from a slice by copying the element.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::InlineVec;
    /// use typenum::U8;
    /// let array = [1, 2, 3];
    /// let inline = InlineVec::<u8, U8>::from_slice_copy(&array);
    /// assert_eq!(inline.as_slice(), array);
    /// ```
    ///
    /// # Safety
    ///
    /// The caller must ensure the length of the slice is less than or equal to
    /// the capacity of the inline vector.
    pub const unsafe fn from_slice_copy_unchecked(slice: &[T]) -> Self {
        let mut this = Self::new();
        // SAFETY: function precondition
        unsafe {
            this.extend_from_slice_copy_unchecked(slice);
        }
        this
    }

    /// Appends a slice of elements to the inline vector, by copying the
    /// elements from the slice into the inline vector.
    ///
    /// This function is only available for types that implement the `Copy`
    /// trait. See [`extend_from_slice`] for a version that works with types that
    /// only implement the `Clone` trait. See [`extend_from_array`] for a
    /// version that moves ownership from an array.
    ///
    /// # Panics
    ///
    /// Panics if the new length exceeds the capacity of the inline vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::inline_vec;
    /// let mut inline = inline_vec![8 => 1_u8, 2];
    /// inline.extend_from_slice_copy(&[3, 4]);
    /// assert_eq!(inline.as_slice(), &[1, 2, 3, 4]);
    /// ```
    ///
    /// [`extend_from_slice`]: Self::extend_from_slice
    /// [`extend_from_array`]: Self::extend_from_array
    #[doc(alias = "push_slice_copy")]
    #[track_caller]
    pub const fn extend_from_slice_copy(&mut self, slice: &[T]) {
        let len = self.len();
        let new_len = len + slice.len();
        assert!(new_len <= Self::CAPACITY, "new length exceeds capacity");
        unsafe {
            self.extend_from_slice_copy_unchecked(slice);
        }
    }

    /// Appends a slice of elements to the inline vector, by copying the
    /// elements from the slice into the inline vector.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the new length does not exceed the capacity
    /// of the inline vector.
    pub const unsafe fn extend_from_slice_copy_unchecked(&mut self, slice: &[T]) {
        let len = self.len();
        let new_len = len + slice.len();
        debug_assert!(new_len <= Self::CAPACITY, "new length exceeds capacity");
        unsafe {
            self.set_len(new_len);
            self.as_mut_ptr()
                .add(len)
                .copy_from_nonoverlapping(slice.as_ptr(), slice.len());
        }
    }

    /// Returns a copy of the inline vector.
    ///
    /// This function is only available for types that implement the `Copy`
    /// trait. See [`clone`] for a version that works with types that only
    /// implement the `Clone` trait.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::InlineVec;
    /// use typenum::U8;
    /// let inline = InlineVec::<u8, U8>::from_slice_copy(&[1, 2, 3]);
    /// let copy = inline.copy();
    /// assert_eq!(copy.as_slice(), &[1, 2, 3]);
    /// ```
    ///
    /// [`clone`]: Self::clone
    #[must_use]
    pub const fn copy(&self) -> Self {
        unsafe {
            let mut this: MaybeUninit<Self> = MaybeUninit::uninit();
            this.as_mut_ptr().copy_from_nonoverlapping(self, 1);
            this.assume_init()
        }
    }

    /// Given a range `src`, copies a slice of elements in that range and
    /// appends it to the end.
    ///
    /// # Panics
    ///
    /// Panics if the source range is invalid or if the new length exceeds the
    /// capacity of the inline vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::inline_vec;
    /// let mut characters = inline_vec![40 => 'a', 'b', 'c', 'd', 'e'];
    /// characters.extend_from_within_copy(2..);
    /// assert_eq!(characters, ['a', 'b', 'c', 'd', 'e', 'c', 'd', 'e']);
    ///
    /// let mut numbers = inline_vec![8 => 0_u8, 1, 2, 3, 4];
    /// numbers.extend_from_within_copy(..2);
    /// assert_eq!(numbers, [0, 1, 2, 3, 4, 0, 1]);
    /// ```
    #[track_caller]
    pub fn extend_from_within_copy(&mut self, range: impl RangeBounds<usize>) {
        let range = common::range(range, self.len()).unwrap_or_else(|err| {
            panic!("{err}");
        });
        self.extend_from_within_range_copy(range);
    }

    fn extend_from_within_range_copy(&mut self, range: Range<usize>) {
        let len = self.len();
        let new_len = len + range.len();
        assert!(new_len <= Self::CAPACITY, "new length exceeds capacity");

        let data_slice: &mut [MaybeUninit<T>] = unsafe {
            let ptr = self.as_mut_ptr().cast();
            slice::from_raw_parts_mut(ptr, Self::CAPACITY)
        };

        // SAFETY: the range is valid and the source elements are initialized
        let (current, spare) = unsafe { data_slice.split_at_mut_unchecked(len) };

        // SAFETY: the range is valid and the source elements are initialized
        // the destination and the source do not overlap
        unsafe {
            spare
                .as_mut_ptr()
                .copy_from_nonoverlapping(current.as_mut_ptr().add(range.start), range.len());
            self.set_len(new_len);
        }
    }
}

impl<T, L: InlineLength> Clone for InlineVec<T, L>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        Self::from_slice_clone(self.as_slice())
    }
}

impl<T, L: InlineLength> Drop for InlineVec<T, L> {
    fn drop(&mut self) {
        unsafe {
            self.drop_contents();
        }
    }
}

impl<T, L: InlineLength> Extend<T> for InlineVec<T, L> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        // May be improve by specialization if Rust offers it one day. Is it
        // worth it for such small sized vectors?
        let iter = iter.into_iter();
        for item in iter {
            self.push(item);
        }
    }
}

impl<T: Eq, L: InlineLength> Eq for InlineVec<T, L> {}

macros::trait_impls! {
    [T, U, L1: InlineLength, L2: InlineLength]
    where [T: PartialEq<U>]
    {
        PartialEq {
            InlineVec<T, L1>, InlineVec<U, L2>;
        }
    }

    [T, U, L: InlineLength]
    where [T: PartialEq<U>]
    {
        PartialEq {
            InlineVec<T, L>, [U];
            InlineVec<T, L>, &[U];
            InlineVec<T, L>, &mut [U];
            InlineVec<T, L>, Vec<U>;


            [T], InlineVec<U, L>;
            &[T], InlineVec<U, L>;
            &mut [T], InlineVec<U, L>;
            Vec<T>, InlineVec<U, L>;

        }
    }

    [T, U, L: InlineLength]
    where [T: PartialEq<U>, U: Clone]
    {
        PartialEq {
            InlineVec<T, L>, alloc::borrow::Cow<'_, [U]>;
        }
    }

    [T, U, L: InlineLength]
    where [T: PartialEq<U>, T: Clone]
    {
        PartialEq {
            alloc::borrow::Cow<'_, [T]>, InlineVec<U, L>;
        }
    }

    [T, U, L: InlineLength, const N: usize]
    where [T: PartialEq<U>]
    {
        PartialEq {
            [T; N], InlineVec<U, L>;
            InlineVec<T, L>, [U; N];

            &[T; N], InlineVec<U, L>;
            InlineVec<T, L>, &[U; N];

            &mut [T; N], InlineVec<U, L>;
            InlineVec<T, L>, &mut [U; N];
        }
    }

    [T, L1: InlineLength, L2: InlineLength]
    where [T: PartialOrd]
    {
        PartialOrd {
            InlineVec<T, L1>, InlineVec<T, L2>;
        }
    }

    [T, L: InlineLength, const N: usize]
    {
        From {
            [T; N] => InlineVec<T, L> = Self::from_array;
        }
    }

    [T, L: InlineLength]
    {
        From {
            Box<[T]> => InlineVec<T, L> = Self::from_boxed_slice;
            Vec<T> => InlineVec<T, L> = Self::from_vector;
        }
    }

    [T, P: ConstDefault, L: InlineLength]
    {
        From {
            crate::vecs::thin::ThinVec<T, P> => InlineVec<T, L> = Self::from_vector;
        }
    }

    [T, L: InlineLength]
    where [T: Clone]
    {
        From {
            &[T] => InlineVec<T, L> = Self::from_slice_clone;
            &mut [T] => InlineVec<T, L> = Self::from_slice_clone;
            Cow<'_, [T]> => InlineVec<T, L> = Self::from_cow;
        }
    }

    [T, L: InlineLength, const N: usize]
    where [T: Clone]
    {
        From {
            &[T; N] => InlineVec<T, L> = Self::from_slice_clone;
            &mut [T; N] => InlineVec<T, L> = Self::from_slice_clone;
        }
    }
}

impl<T: Ord, L: InlineLength> Ord for InlineVec<T, L> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.as_slice().cmp(other.as_slice())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InsertErrorKind {
    Full,
    OutOfBounds,
}

impl InsertErrorKind {
    #[inline]
    #[must_use]
    pub const fn message(&self) -> &str {
        match self {
            Self::Full => "inline vector is full",
            Self::OutOfBounds => "index out of bounds",
        }
    }
}

/// Error type for [`InlineVec::try_insert`].
///
/// This error type is returned when an attempt to insert an element into an
/// [`InlineVec`] fails. It contains the value that was attempted to be
/// inserted and the kind of error that occurred.
#[must_use]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InsertError<T> {
    pub value: T,
    pub kind: InsertErrorKind,
}

impl<T> InsertError<T> {
    #[inline]
    pub(crate) const fn new(value: T, kind: InsertErrorKind) -> Self {
        Self { value, kind }
    }

    #[inline]
    pub const fn message(&self) -> &str {
        self.kind.message()
    }
}

impl<T: fmt::Debug> error::Error for InsertError<T> {}

impl<T> fmt::Display for InsertError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.message())
    }
}

/// Creates an inline vector in a syntax similar to array literal expressions.
/// The inline vector's payload size in bytes is either explicitly specified or
/// inferred by the compiler.
///
/// They are multiple forms of this macros:
///
/// - Creates an inline vector with the given elements and a specified capacity:
///
///   ```
///   # use hipstr::inline_vec;
///   let v1 = inline_vec![8 => 1_u8, 2, 3];
///   assert_eq!(v1, [1, 2, 3]);
///   ```
///
/// - Creates an inline vector with the given elements and an inferred capacity:
///
///   ```
///   # use hipstr::inline_vec;
///   # use hipstr::vecs::InlineVec;
///   # use typenum::U8;
///   let v2: InlineVec<u8, U8> = inline_vec![1_u8, 2, 3];
///   assert_eq!(v2, [1, 2, 3]);
///   ```
///
/// - Creates an inline vector from a given element and size with a specified
///   capacity:
///
///   ```
///   # use hipstr::inline_vec;
///   let v3 = inline_vec![8 => 0_u8; 7];
///   assert_eq!(v3, [0, 0, 0, 0, 0, 0, 0]);
///   ```
///
/// - Creates an inline vector from a given element and size with an inferred
///   capacity:
///
///   ```
///   # use hipstr::inline_vec;
///   # use hipstr::vecs::InlineVec;
///   # use typenum::U8;
///   let v4: InlineVec<u8, U8> = inline_vec![0_u8; 7];
///   assert_eq!(v4, [0, 0, 0, 0, 0, 0, 0]);
///   ```
#[macro_export]
macro_rules! inline_vec {
    [$cap:expr => $($e:expr),* $(,)?] => {
        {
            const {
                assert!($cap % size_of::<*const()>() == 0, "capacity must be a multiple of pointer size");
            }
            $crate::vecs::inline::InlineVec::<_, $crate::typenum::U<{ $cap }>>::from_array([$($e),*])
        }
    };
    [$($e:expr),* $(,)?] => {
        {
            $crate::vecs::inline::InlineVec::from_array([$($e),*])
        }
    };
    [$cap:expr => $e:expr; $n:expr] => {
        {
            const {
                assert!($cap % size_of::<*const()>() == 0, "capacity must be a multiple of pointer size");
            }
            $crate::vecs::inline::InlineVec::<_,  $crate::typenum::U< { $cap }>>::from_array([$e; $n])
        }
    };
    [$e:expr; $n:expr] => {
        {
            $crate::vecs::InlineVec::from_array([$e; $n])
        }
    };
}
