//! An inline vector for all types and related functionalities.
//!
//! This is intended to be the main implementation of inline vectors.
//! See the [`inline::copy`] module for a specialization for `Copy` types, which is more efficient in some cases.
//!
//! [`inline::copy`]: crate::inline::copy

use core::ptr::NonNull;
use core::{fmt, ops};

use const_default::ConstDefault;

use super::base::Base;
use super::layouts::Layout;
use crate::common::drain::Drain;
use crate::common::utils::drop_raw_slice;
use crate::inline::copy;
use crate::traits::{MutableVector, impl_vector};

#[cfg(test)]
mod tests;

/// An inline vector for all types.
///
/// This is the main implementation of inline vectors.
/// See [`inline::copy::InlineVec`] for a specialization for `Copy` types, which is more efficient in some cases.
///
/// [`inline::copy::InlineVec`]: crate::inline::copy::InlineVec
///
/// # Examples
///
/// ```
/// # use hipvec::inline::InlineVec;
/// let mut vec = InlineVec::<i32>::new();
/// vec.push(1);
/// vec.push(2);
/// assert_eq!(vec.as_slice(), &[1, 2]);
/// vec.pop();
/// assert_eq!(vec.as_slice(), &[1]);
/// vec.clear();
/// assert!(vec.is_empty());
/// ```
#[repr(transparent)]
pub struct InlineVec<T, L: Layout<T>> {
    pub(super) base: Base<T, L>,
}

impl<T, L: Layout<T>> ConstDefault for InlineVec<T, L> {
    const DEFAULT: Self = Self::new();
}

impl<T, L: Layout<T>> Default for InlineVec<T, L> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T, L: Layout<T>> InlineVec<T, L> {
    /// Constructs a new, empty inline vector.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline::InlineVec;
    /// let vec = InlineVec::<i32>::new();
    /// assert!(vec.is_empty());
    /// ```
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self { base: Base::new() }
    }

    /// Constructs a new, empty inline vector with at least the specified capacity.
    ///
    /// This method is provided for compatibility with standard vecs. Since [`CAPACITY`] is fixed at
    /// compile time, this method will panic if the requested capacity exceeds the inline capacity.
    ///
    /// [`CAPACITY`]: Self::CAPACITY
    ///
    /// # Panics
    ///
    /// Panics if the requested capacity exceeds [`CAPACITY`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline::InlineVec;
    /// let mut vec = InlineVec::<u8>::with_capacity(10);
    ///
    /// // The vector contains no items, even though it has capacity for more
    /// assert_eq!(vec.len(), 0);
    /// assert!(vec.capacity() >= 10);
    ///
    /// for i in 0..10 {
    ///     vec.push(i);
    /// }
    /// assert_eq!(vec.len(), 10);
    /// assert!(vec.capacity() >= 10);
    /// ```
    ///
    /// The following example will always panic:
    ///
    /// ```should_panic
    /// # use hipvec::inline::InlineVec;
    /// let mut vec = InlineVec::<u8>::with_capacity(InlineVec::<u8>::CAPACITY + 1);
    /// ```
    #[inline]
    #[must_use]
    pub const fn with_capacity(capacity: usize) -> Self {
        assert!(
            capacity <= Self::CAPACITY,
            "required capacity exceeds maximum"
        );
        Self::new()
    }

    /// Returns the number of elements in the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline::InlineVec;
    /// let mut vec = InlineVec::<i32>::new();
    /// assert_eq!(vec.len(), 0);
    /// vec.push(1);
    /// vec.push(2);
    /// assert_eq!(vec.len(), 2);
    /// ```
    #[inline]
    #[must_use]
    pub const fn len(&self) -> usize {
        self.base.len()
    }

    /// Returns `true` if the vector contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline::InlineVec;
    /// let vec = InlineVec::<i32>::new();
    /// assert!(vec.is_empty());
    ///
    /// let mut vec = InlineVec::<i32>::new();
    /// vec.push(1);
    /// assert!(!vec.is_empty());
    /// ```
    #[inline]
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.base.is_empty()
    }

    /// Sets the length of the vector.
    ///
    /// # Safety
    ///
    /// `new_len` must be less than or equal to capacity, and elements in
    /// `old_len..new_len` (if any) must be initialized.
    pub const unsafe fn set_len(&mut self, new_len: usize) {
        unsafe {
            self.base.set_len(new_len);
        }
    }

    /// Returns the contents as a mutable slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline::InlineVec;
    /// let mut vec = InlineVec::<i32>::from([1, 2]);
    /// vec.as_mut_slice()[0] = 9;
    /// assert_eq!(vec.as_slice(), &[9, 2]);
    /// ```
    #[inline]
    #[must_use]
    pub const fn as_mut_slice(&mut self) -> &mut [T] {
        self.base.as_mut_slice()
    }

    /// Returns the remaining spare capacity of the vector as a slice of
    /// `MaybeUninit<T>`.
    ///
    /// The returned slice can be used to fill the vector with data (e.g. by
    /// reading from a file) before marking the data as initialized using the
    /// [`set_len`] method.
    ///
    /// [`set_len`]: Self::set_len
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline::InlineVec;
    /// // Allocate vector big enough for 5 elements.
    /// let mut v = InlineVec::with_capacity(5);
    ///
    /// // Fill in the first 3 elements.
    /// let uninit = v.spare_capacity_mut();
    /// uninit[0].write(0);
    /// uninit[1].write(1);
    /// uninit[2].write(2);
    ///
    /// // Mark the first 3 elements of the vector as being initialized.
    /// unsafe {
    ///     v.set_len(3);
    /// }
    ///
    /// assert_eq!(v.as_slice(), [0, 1, 2]);
    /// ```
    #[inline]
    #[must_use]
    pub const fn spare_capacity_mut(&mut self) -> &mut [core::mem::MaybeUninit<T>] {
        self.base.spare_capacity_mut()
    }

    /// Extracts a slice containing the entire vector.
    ///
    /// Equivalent to `&vec[..]`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline::InlineVec;
    /// let vec = InlineVec::<i32>::from([1, 2]);
    /// assert_eq!(vec.as_slice(), &[1, 2]);
    /// ```
    #[inline]
    #[must_use]
    pub const fn as_slice(&self) -> &[T] {
        self.base.as_slice()
    }

    /// Returns a raw mutable pointer to the vector's buffer, or a dangling raw pointer valid for zero
    /// sized reads if the vector alignment is insufficient for the element type `T`.
    ///
    /// The caller must ensure that the vector outlives the pointer this
    /// function returns, or else it will end up dangling.
    ///
    /// This method guarantees that for the purpose of the aliasing model, this method
    /// does not materialize a reference to the underlying slice, and thus the returned pointer
    /// will remain valid when mixed with other calls to [`as_ptr`], [`as_mut_ptr`],
    /// and [`as_non_null`].
    /// Note that calling other methods that materialize references to the slice,
    /// or references to specific elements you are planning on accessing through this pointer,
    /// may still invalidate this pointer.
    /// See the second example below for how this guarantee can be used.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline::InlineVec;
    /// // Creates the vector.
    /// let size = 4;
    /// let mut x: InlineVec<i32> = InlineVec::with_capacity(size);
    /// let x_ptr = x.as_mut_ptr();
    ///
    /// // Initialize elements via raw pointer writes, then set length.
    /// unsafe {
    ///     for i in 0..size {
    ///         *x_ptr.add(i) = i as i32;
    ///     }
    ///     x.set_len(size);
    /// }
    /// assert_eq!(x.as_slice(), &[0, 1, 2, 3]);
    /// ```
    #[inline]
    #[must_use]
    pub const fn as_mut_ptr(&mut self) -> *mut T {
        self.base.as_mut_ptr()
    }

    /// Returns a `NonNull` pointer to the vector's buffer, or a dangling
    /// `NonNull` pointer valid for zero sized reads if the vector didn't allocate.
    ///
    /// The caller must ensure that the vector outlives the pointer this
    /// function returns, or else it will end up dangling.
    /// Modifying the vector may cause its buffer to be reallocated,
    /// which would also make any pointers to it invalid.
    ///
    /// This method guarantees that for the purpose of the aliasing model, this method
    /// does not materialize a reference to the underlying slice, and thus the returned pointer
    /// will remain valid when mixed with other calls to [`as_ptr`], [`as_mut_ptr`],
    /// and [`as_non_null`].
    /// Note that calling other methods that materialize references to the slice,
    /// or references to specific elements you are planning on accessing through this pointer,
    /// may still invalidate this pointer.
    /// See the second example below for how this guarantee can be used.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline::InlineVec;
    ///
    /// let mut x: InlineVec<i32> = InlineVec::new();
    /// let x_ptr = x.as_non_null();
    /// let size = 4;
    ///
    /// // Initialize elements via raw pointer writes, then set length.
    /// unsafe {
    ///     for i in 0..size {
    ///         x_ptr.add(i).write(i as i32);
    ///     }
    ///     x.set_len(size);
    /// }
    /// assert_eq!(&*x, &[0, 1, 2, 3]);
    /// ```
    ///
    /// [`as_mut_ptr`]: Self::as_mut_ptr
    /// [`as_ptr`]: Self::as_ptr
    /// [`as_non_null`]: Self::as_non_null
    #[inline]
    #[must_use]
    pub const fn as_non_null(&mut self) -> NonNull<T> {
        self.base.as_non_null()
    }

    /// Returns a raw const pointer to the vector's buffer, or a dangling raw pointer valid for zero
    /// sized reads if the vector alignment is insufficient for the element type `T`.
    ///
    /// The caller must ensure that the vector outlives the pointer this
    /// function returns, or else it will end up dangling.
    ///
    /// The caller must also ensure that the memory the pointer (non-transitively) points to
    /// is never written to (except inside an `UnsafeCell`) using this pointer or any pointer
    /// derived from it. If you need to mutate the contents of the slice, use [`as_mut_ptr`].
    ///
    /// This method guarantees that for the purpose of the aliasing model, this method
    /// does not materialize a reference to the underlying slice, and thus the returned pointer
    /// will remain valid when mixed with other calls to [`as_ptr`], [`as_mut_ptr`],
    /// and [`as_non_null`].
    /// Note that calling other methods that materialize mutable references to the slice,
    /// or mutable references to specific elements you are planning on accessing through this pointer,
    /// as well as writing to those elements, may still invalidate this pointer.
    /// See the second example below for how this guarantee can be used.
    ///
    /// [`as_ptr`]: Self::as_ptr
    /// [`as_mut_ptr`]: Self::as_mut_ptr
    /// [`as_non_null`]: Self::as_non_null
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline_vec;
    /// let x = inline_vec![1, 2, 4];
    /// let x_ptr = x.as_ptr();
    ///
    /// unsafe {
    ///     for i in 0..x.len() {
    ///         assert_eq!(*x_ptr.add(i), 1 << i);
    ///     }
    /// }
    /// ```
    #[inline]
    #[must_use]
    pub const fn as_ptr(&self) -> *const T {
        self.base.as_ptr()
    }

    /// The maximum number of elements the vector can hold.
    pub const CAPACITY: usize = L::CAPACITY;

    /// Returns the maximum number of elements the vector can hold.
    ///
    /// The capacity is determined by the layout and is a compile-time constant.
    ///
    /// This method is provided for compatibility with standard vecs.
    ///
    /// See [`CAPACITY`] for the compile-time constant capacity.
    ///
    /// [`CAPACITY`]: Self::CAPACITY
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline::InlineVec;
    /// let vec = InlineVec::<i32>::new();
    /// assert_eq!(vec.capacity(), InlineVec::<i32>::CAPACITY);
    /// ```
    #[inline]
    #[must_use]
    pub const fn capacity(&self) -> usize {
        self.base.capacity()
    }

    /// Asserts the vector has enough spare space for `additional` more elements.
    ///
    /// This method is provided for compatibility with standard vecs. Since the capacity is fixed at
    /// compile time, this method will panic if the new length exceeds the capacity.
    ///
    /// # Panics
    ///
    /// Panics if `self.len() + additional > self.capacity()`.
    ///
    /// # Examples
    ///
    /// The following will panic because the new length exceeds the capacity:
    ///
    /// ```should_panic
    /// # use hipvec::inline::InlineVec;
    /// let mut vec = InlineVec::<i32>::new();
    /// vec.reserve(vec.capacity() + 1);
    /// ```
    #[inline]
    #[track_caller]
    pub const fn reserve(&mut self, additional: usize) {
        self.base.reserve(additional);
    }

    /// Asserts the vector has enough spare space for `additional` more elements.
    ///
    /// This method is provided for compatibility with standard vecs. Since the capacity is fixed at
    /// compile time, this method will panic if the new length exceeds the capacity.
    ///
    /// # Panics
    ///
    /// Panics if `self.len() + additional > self.capacity()`.
    ///
    /// # Examples
    ///
    /// The following will panic because the new length exceeds the capacity:
    ///
    /// ```should_panic
    /// # use hipvec::inline::InlineVec;
    /// let mut vec = InlineVec::<i32>::new();
    /// vec.reserve_exact(vec.capacity() + 1);
    /// ```
    #[inline]
    #[track_caller]
    pub const fn reserve_exact(&mut self, additional: usize) {
        self.base.reserve_exact(additional);
    }

    /// Appends an element to the back of a collection.
    ///
    /// # Panics
    ///
    /// Panics if the new length would exceed [`CAPACITY`].
    ///
    /// [`CAPACITY`]: Self::CAPACITY
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline_vec;
    /// let mut vec = inline_vec![1, 2];
    /// vec.push(3);
    /// assert_eq!(vec.as_slice(), [1, 2, 3]);
    /// ```
    #[inline]
    #[track_caller]
    pub const fn push(&mut self, value: T) {
        self.base.push(value);
    }

    /// Appends an element to the back of a collection, returning a reference to it.
    ///
    /// # Panics
    ///
    /// Panics if the new length would exceed [`CAPACITY`].
    ///
    /// [`CAPACITY`]: Self::CAPACITY
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline_vec;
    /// let mut vec = inline_vec![1_u8, 2];
    /// let last = vec.push_mut(3);
    /// assert_eq!(*last, 3);
    /// assert_eq!(vec.as_slice(), [1, 2, 3]);
    ///
    /// let last = vec.push_mut(3);
    /// *last += 1;
    /// assert_eq!(vec.as_slice(), [1, 2, 3, 4]);
    /// ```
    #[inline]
    #[must_use]
    #[track_caller]
    pub const fn push_mut(&mut self, value: T) -> &mut T {
        self.base.push_mut(value)
    }

    /// Removes and returns the last element, if any.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline::InlineVec;
    /// let mut vec = InlineVec::<i32>::from([1, 2]);
    /// assert_eq!(vec.pop(), Some(2));
    /// assert_eq!(vec.pop(), Some(1));
    /// assert_eq!(vec.pop(), None);
    /// ```
    #[inline]
    pub const fn pop(&mut self) -> Option<T> {
        self.base.pop()
    }

    /// Removes and returns the last element from a vector if the predicate
    /// returns `true`, or [`None`] if the predicate returns false or the vector
    /// is empty (the predicate will not be called in that case).
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline_vec;
    /// let mut vec = inline_vec![1_u8, 2, 3, 4];
    /// let pred = |x: &mut u8| *x % 2 == 0;
    ///
    /// assert_eq!(vec.pop_if(pred), Some(4));
    /// assert_eq!(vec.as_slice(), [1, 2, 3]);
    /// assert_eq!(vec.pop_if(pred), None);
    /// ```
    #[inline]
    pub fn pop_if(&mut self, f: impl FnOnce(&mut T) -> bool) -> Option<T> {
        self.base.pop_if(f)
    }

    /// Removes and returns the element at position `index` within the vector,
    /// shifting all elements after it to the left.
    ///
    /// Note: Because this shifts over the remaining elements, it has a
    /// worst-case performance of *O*(*n*). If you don't need the order of elements
    /// to be preserved, use [`swap_remove`] instead.
    ///
    /// [`swap_remove`]: Self::swap_remove
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline_vec;
    /// let mut v = inline_vec![b'a', b'b', b'c'];
    /// assert_eq!(v.remove(1), b'b');
    /// assert_eq!(v.as_slice(), [b'a', b'c']);
    /// ```
    #[inline]
    #[track_caller]
    pub const fn remove(&mut self, index: usize) -> T {
        self.base.remove(index)
    }

    /// Removes an element from the vector and returns it.
    ///
    /// The removed element is replaced by the last element of the vector.
    ///
    /// This does not preserve ordering of the remaining elements, but is *O*(1).
    /// If you need to preserve the element order, use [`remove`] instead.
    ///
    /// [`remove`]: Self::remove
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline_vec;
    /// let mut v = inline_vec![0, 1, 2, 3];
    ///
    /// assert_eq!(v.swap_remove(1), 1);
    /// assert_eq!(v.as_slice(), [0, 3, 2]);
    ///
    /// assert_eq!(v.swap_remove(0), 0);
    /// assert_eq!(v.as_slice(), [2, 3]);
    /// ```
    #[inline]
    #[track_caller]
    pub const fn swap_remove(&mut self, index: usize) -> T {
        self.base.swap_remove(index)
    }

    /// Inserts an element at `index`, shifting later elements to the right.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds or if the new length would exceed [`CAPACITY`].
    ///
    /// [`CAPACITY`]: Self::CAPACITY
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline::InlineVec;
    /// let mut vec = InlineVec::<i32>::from([1, 3]);
    /// vec.insert(1, 2);
    /// assert_eq!(vec.as_slice(), &[1, 2, 3]);
    /// ```
    #[inline]
    #[track_caller]
    pub const fn insert(&mut self, index: usize, value: T) {
        self.base.insert(index, value);
    }

    /// Inserts an element at position `index` within the vector, shifting all
    /// elements after it to the right, and returning a reference to the new
    /// element.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds or if the new length would exceed [`CAPACITY`].
    ///
    /// [`CAPACITY`]: Self::CAPACITY
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline_vec;
    /// let mut vec = inline_vec![1_u8, 3, 5, 9];
    /// let x = vec.insert_mut(3, 6);
    /// *x += 1;
    /// assert_eq!(vec.as_slice(), [1, 3, 5, 7, 9]);
    /// ```
    #[inline]
    #[must_use]
    #[track_caller]
    pub const fn insert_mut(&mut self, index: usize, value: T) -> &mut T {
        self.base.insert_mut(index, value)
    }

    /// Shortens the vector, keeping the first `new_len` elements.
    ///
    /// This function does nothing if the new length is greater than or equal to the current length.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline::InlineVec;
    /// let mut vec = InlineVec::<i32>::from([1, 2, 3]);
    /// vec.truncate(2);
    /// assert_eq!(vec.as_slice(), &[1, 2]);
    /// vec.truncate(5);
    /// assert_eq!(vec.as_slice(), &[1, 2]);
    /// ```
    #[inline]
    pub fn truncate(&mut self, new_len: usize) {
        self.base.truncate(new_len)
    }

    /// Clears the vector, removing all elements.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline::InlineVec;
    /// let mut vec = InlineVec::<i32>::from([1, 2, 3]);
    /// vec.clear();
    /// assert!(vec.is_empty());
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        *self = Self::new();
    }

    /// Removes the subslice indicated by the given range from the vector,
    /// returning a double-ended iterator over the removed subslice.
    ///
    /// If the iterator is dropped before being fully consumed,
    /// it drops the remaining removed elements.
    ///
    /// The returned iterator keeps a mutable borrow on the vector to optimize
    /// its implementation.
    ///
    /// # Panics
    ///
    /// Panics if the range is invalid.
    ///
    /// # Leaking
    ///
    /// If the returned iterator goes out of scope without being dropped (due to
    /// [`mem::forget`], for example), the vector may have lost elements
    /// arbitrarily, including elements outside the range.
    ///
    /// [`mem::forget`]: core::mem::forget
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline_vec;
    /// let mut v = inline_vec![1_u8, 2, 3];
    /// let u: Vec<_> = v.drain(1..).collect();
    /// assert_eq!(v.as_slice(), &[1]);
    /// assert_eq!(u.as_slice(), &[2, 3]);
    ///
    /// // A full range clears the vector, like `clear()` does
    /// v.drain(..);
    /// assert_eq!(v.as_slice(), &[]);
    /// ```
    #[inline]
    #[track_caller]
    pub fn drain(&mut self, range: impl ops::RangeBounds<usize>) -> Drain<'_, Self> {
        Drain::new(self, range).unwrap()
    }

    /// Appends all elements of the array to the vector.
    ///
    /// The elements are moved and not cloned.
    ///
    /// # Panics
    ///
    /// Panics if the new length would exceed [`CAPACITY`].
    ///
    /// [`CAPACITY`]: Self::CAPACITY
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline_vec;
    /// let mut vec = inline_vec![1_u8];
    /// vec.extend_from_array([2, 3, 4]);
    /// assert_eq!(vec.as_slice(), [1, 2, 3, 4]);
    /// ```
    #[inline]
    #[track_caller]
    pub const fn extend_from_array<const N: usize>(&mut self, array: [T; N]) {
        self.base.extend_from_array(array);
    }

    /// Moves all the elements of `other` into `self`, leaving `other` empty.
    ///
    /// See [`const_append`] for a const specialization for inline vectors.
    ///
    /// [`const_append`]: Self::append
    ///
    /// # Panics
    ///
    /// Panics if the new length would exceed [`CAPACITY`].
    ///
    /// [`CAPACITY`]: Self::CAPACITY
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline_vec;
    /// # use std::vec;
    /// let mut vec = inline_vec![1_u8, 2, 3];
    /// let mut vec2 = vec![4_u8, 5, 6];
    /// vec.append(&mut vec2);
    /// assert_eq!(vec.as_slice(), [1, 2, 3, 4, 5, 6]);
    /// assert_eq!(vec2.as_slice(), []);
    /// ```
    #[inline]
    #[track_caller]
    pub fn append(&mut self, other: &mut impl MutableVector<Item = T>) {
        self.base.append(other);
    }

    /// Moves all the elements of `other` into `self`, leaving `other` empty.
    ///
    /// This a const specialization if `other` is an inline vector.
    /// See [`append`] for the general version.
    ///
    /// [`append`]: Self::append
    ///
    /// # Panics
    ///
    /// Panics if the new length would exceed [`CAPACITY`].
    ///
    /// [`CAPACITY`]: Self::CAPACITY
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline_vec;
    /// let mut vec = inline_vec![1_u8, 2, 3];
    /// let mut vec2 = inline_vec![4_u8, 5, 6];
    /// vec.append(&mut vec2);
    /// assert_eq!(vec.as_slice(), [1, 2, 3, 4, 5, 6]);
    /// assert_eq!(vec2.as_slice(), []);
    /// ```
    #[inline]
    #[track_caller]
    pub const fn const_append(&mut self, other: &mut Self) {
        self.base.const_append(&mut other.base);
    }
}

impl<T: Clone, L: Layout<T>> InlineVec<T, L> {
    // const fn from_slice:
    // not available since it needs to clone elements

    /// Clones and appends all elements in a slice to the vector.
    ///
    /// # Panics
    ///
    /// Panics if the new length would exceed [`CAPACITY`].
    ///
    /// [`CAPACITY`]: Self::CAPACITY
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline::InlineVec;
    /// let mut vec = InlineVec::<i32>::from([1, 2]);
    /// vec.extend_from_slice(&[3, 4]);
    /// assert_eq!(vec.as_slice(), &[1, 2, 3, 4]);
    /// ```
    #[inline]
    #[track_caller]
    pub fn extend_from_slice(&mut self, value: &[T]) {
        self.base.extend_from_slice(value);
    }

    /// Resizes the vector in-place so that `len` is equal to `new_len`.
    ///
    /// If `new_len` is greater than `len`, the vector is extended by the
    /// difference, with each additional slot filled with `value`.
    /// If `new_len` is less than `len`, the vector is simply truncated.
    ///
    /// This method requires `T` to implement [`Clone`],
    /// in order to be able to clone the passed value.
    /// If you need more flexibility (or want to rely on [`Default`] instead of
    /// [`Clone`]), use [`resize_with`].
    /// If you only need to resize to a smaller size, use [`truncate`].
    ///
    /// [`resize_with`]: Self::resize_with
    /// [`truncate`]: Self::truncate
    ///
    /// # Panics
    ///
    /// Panics if the new length exceeds [`CAPACITY`].
    ///
    /// [`CAPACITY`]: Self::CAPACITY
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline_vec;
    /// let mut vec = inline_vec![1_u8, 2];
    /// vec.resize(4, 0);
    /// assert_eq!(vec.as_slice(), [1, 2, 0, 0]);
    ///
    /// let mut vec = inline_vec![1_u16, 2, 3];
    /// vec.resize(2, 0);
    /// assert_eq!(vec.as_slice(), [1, 2]);
    /// ```
    #[inline]
    #[track_caller]
    pub fn resize(&mut self, new_len: usize, value: T)
    where
        T: Clone,
    {
        self.base.resize(new_len, value);
    }

    /// Resizes the vector in-place so that `len` is equal to `new_len`.
    ///
    /// If `new_len` is greater than `len`, the vector is extended by the
    /// difference, with each additional slot filled with the result of
    /// calling the closure `f`. The return values from `f` will end up
    /// in the vector in the order they have been generated.
    ///
    /// If `new_len` is less than `len`, the vector is simply truncated.
    ///
    /// This method uses a closure to create new values on every push. If
    /// you'd rather [`Clone`] a given value, use [`resize`]. If you
    /// want to use the [`Default`] trait to generate values, you can
    /// pass [`Default::default`] as the second argument.
    ///
    /// [`resize`]: Self::resize
    ///
    /// # Panics
    ///
    /// Panics if the new length exceeds [`CAPACITY`].
    ///
    /// [`CAPACITY`]: Self::CAPACITY
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline_vec;
    /// let mut vec = inline_vec![1_u8, 2, 3];
    /// vec.resize_with(5, Default::default);
    /// assert_eq!(vec.as_slice(), [1, 2, 3, 0, 0]);
    ///
    /// let mut vec = inline_vec![];
    /// let mut p = 1_u8;
    /// vec.resize_with(4, || { p *= 2; p });
    /// assert_eq!(vec.as_slice(), [2, 4, 8, 16]);
    /// ```
    #[inline]
    #[track_caller]
    pub fn resize_with(&mut self, new_len: usize, f: impl FnMut() -> T) {
        self.base.resize_with(new_len, f);
    }
}

impl<T, L: Layout<T>> Drop for InlineVec<T, L> {
    fn drop(&mut self) {
        unsafe {
            drop_raw_slice(self.as_mut_ptr(), self.len());
        }
    }
}

impl<T, L: Layout<T>, const N: usize> From<[T; N]> for InlineVec<T, L> {
    fn from(value: [T; N]) -> Self {
        Self {
            base: Base::from_array(value),
        }
    }
}

impl<T: Clone, L: Layout<T>> From<&[T]> for InlineVec<T, L> {
    fn from(value: &[T]) -> Self {
        let mut this = Self::new();
        this.extend_from_slice(value);
        this
    }
}

impl<T: Copy, L: Layout<T>> From<copy::InlineVec<T, L>> for InlineVec<T, L> {
    fn from(value: copy::InlineVec<T, L>) -> Self {
        Self { base: value.base }
    }
}

// no Copy for InlineVec<T, L>

impl<T: Clone, L: Layout<T>> Clone for InlineVec<T, L> {
    fn clone(&self) -> Self {
        let mut this = Self::new();
        this.extend_from_slice(self.as_slice());
        this
    }
}

impl<T, L: Layout<T>> ops::Deref for InlineVec<T, L> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T, L: Layout<T>> ops::DerefMut for InlineVec<T, L> {
    fn deref_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}

impl<T: fmt::Debug, L: Layout<T>> fmt::Debug for InlineVec<T, L> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_slice().fmt(f)
    }
}

impl_vector!(impl(T, L: Layout<T>) Vector<Item=T> for InlineVec<T, L>);
impl_vector!(impl(T, L: Layout<T>) MutableVector<Item=T> for InlineVec<T, L>);
impl_vector!(impl(T: Clone, L: Layout<T>) GrowableVector<Item=T> for InlineVec<T, L>);
