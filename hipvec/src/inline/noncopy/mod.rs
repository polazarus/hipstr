//! An inline vector for all types and related functionalities.
//!
//! This is intended to be the main implementation of inline vectors.
//! See the [`inline::copy`] module for a specialization for `Copy` types, which is more efficient in some cases.
//!
//! [`inline::copy`]: crate::inline::copy
use core::{mem, ptr};

use const_default::ConstDefault;

use super::base::Base;
use super::layouts::Layout;
use crate::common::methods;
use crate::common::utils::drop_raw_slice;
use crate::inline::copy;
use crate::traits::impl_vector;

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
    /// Creates a new empty inline vector.
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
    /// let mut vec = CopyInlineVec::<u8>::with_capacity(CopyInlineVec::<u8>::CAPACITY + 1);
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
    /// assert_eq!(vec.len(), 1);
    /// ```
    #[inline]
    #[must_use]
    pub const fn len(&self) -> usize {
        self.base.len()
    }

    /// Returns `true` if the vector is empty.
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

    /// Returns the contents as a shared slice.
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

    /// Returns a raw mutable pointer to the vector's buffer.
    #[inline]
    #[must_use]
    pub const fn as_mut_ptr(&mut self) -> *mut T {
        self.base.as_mut_ptr()
    }

    /// Returns a raw const pointer to the vector's buffer.
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
    /// vec.reserve(InlineVec::<i32>::CAPACITY + 1);
    /// ```
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
    /// vec.reserve_exact(InlineVec::<i32>::CAPACITY + 1);
    /// ```
    pub const fn reserve_exact(&mut self, additional: usize) {
        self.base.reserve_exact(additional);
    }

    /// Appends an element to the end of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline::InlineVec;
    /// let mut vec = InlineVec::<i32>::new();
    /// vec.push(7);
    /// assert_eq!(vec.as_slice(), &[7]);
    /// ```
    #[inline]
    pub const fn push(&mut self, value: T) {
        self.base.push(value);
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
    pub fn clear(&mut self) {
        *self = Self::new();
    }
}

impl<T: Clone, L: Layout<T>> InlineVec<T, L> {
    /// Clones and appends all elements in a slice to the vector.
    ///
    /// # Panics
    ///
    /// Panics if the new length exceeds the capacity.
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
    pub fn extend_from_slice(&mut self, value: &[T]) {
        self.base.extend_from_slice(value);
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

impl<T: Copy, L: Layout<T>> From<copy::InlineVec<T, L>> for InlineVec<T, L>
where
    T: Copy,
{
    fn from(value: copy::InlineVec<T, L>) -> Self {
        Self { base: value.base }
    }
}

impl<T: Clone, L: Layout<T>> From<&[T]> for InlineVec<T, L> {
    fn from(value: &[T]) -> Self {
        let mut this = Self::new();
        this.extend_from_slice(value);
        this
    }
}

impl<T, L: Layout<T>> Clone for InlineVec<T, L>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        let mut this = Self::new();
        this.extend_from_slice(self.as_slice());
        this
    }
}

impl_vector!(impl(T, L: Layout<T>) Vector<Item=T> for InlineVec<T, L>);
