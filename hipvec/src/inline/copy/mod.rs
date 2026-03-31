//! An inline vector for `Copy` types and related functionalities.
//!
//! This is intended to be the specialized implementation of inline vectors for
//! `Copy` element types. See the [`inline::noncopy`] module for the general-
//! purpose implementation that supports all types.
//!
//! [`inline::noncopy`]: crate::inline::noncopy
use core::mem::ManuallyDrop;

use const_default::ConstDefault;

use super::base::Base;
use super::layouts::Layout;
use crate::inline::noncopy;
use crate::traits::impl_vector;

#[cfg(test)]
mod tests;

/// An inline vector specialized for `Copy` types.
///
/// This is the specialized implementation of inline vectors for `Copy` types.
/// See [`inline::noncopy::InlineVec`] for the general-purpose implementation
/// that supports all types.
///
/// [`inline::noncopy::InlineVec`]: crate::inline::noncopy::InlineVec
///
/// # Examples
///
/// ```
/// # use hipvec::inline::CopyInlineVec;
/// let mut vec = CopyInlineVec::<i32>::new();
/// vec.push(1);
/// vec.push(2);
/// assert_eq!(vec.as_slice(), &[1, 2]);
/// vec.pop();
/// assert_eq!(vec.as_slice(), &[1]);
/// vec.clear();
/// assert!(vec.is_empty());
/// ```
#[repr(transparent)]
pub struct InlineVec<T: Copy, L: Layout<T>> {
    pub(super) base: Base<T, L>,
}

impl<T: Copy, L: Layout<T>> ConstDefault for InlineVec<T, L> {
    const DEFAULT: Self = Self::new();
}

impl<T: Copy, L: Layout<T>> Default for InlineVec<T, L> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Copy, L: Layout<T>> InlineVec<T, L> {
    /// Creates a new empty inline vector.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline::CopyInlineVec;
    /// let vec = CopyInlineVec::<i32>::new();
    /// assert!(vec.is_empty());
    /// ```
    pub const fn new() -> Self {
        Self { base: Base::new() }
    }

    /// Returns the number of elements in the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline::CopyInlineVec;
    /// let mut vec = CopyInlineVec::<i32>::new();
    /// vec.push(1);
    /// vec.push(2);
    /// assert_eq!(vec.len(), 2);
    /// ```
    pub const fn len(&self) -> usize {
        self.base.len()
    }

    /// Returns `true` if the vector contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline::CopyInlineVec;
    /// let vec = CopyInlineVec::<i32>::new();
    /// assert!(vec.is_empty());
    ///
    /// let mut vec = CopyInlineVec::<i32>::new();
    /// vec.push(1);
    /// assert!(!vec.is_empty());
    /// ```
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
    /// # use hipvec::inline::CopyInlineVec;
    /// let mut vec = CopyInlineVec::<i32>::from([1, 2]);
    /// vec.as_mut_slice()[0] = 9;
    /// assert_eq!(vec.as_slice(), &[9, 2]);
    /// ```
    pub const fn as_mut_slice(&mut self) -> &mut [T] {
        self.base.as_mut_slice()
    }

    /// Returns the contents as a shared slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline::CopyInlineVec;
    /// let vec = CopyInlineVec::<i32>::from([1, 2]);
    /// assert_eq!(vec.as_slice(), &[1, 2]);
    /// ```
    pub const fn as_slice(&self) -> &[T] {
        self.base.as_slice()
    }

    /// Returns a raw mutable pointer to the vector's buffer.
    pub const fn as_mut_ptr(&mut self) -> *mut T {
        self.base.as_mut_ptr()
    }

    /// Returns a raw const pointer to the vector's buffer.
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
    /// # use hipvec::inline::CopyInlineVec;
    /// let vec = CopyInlineVec::<i32>::new();
    /// assert_eq!(vec.capacity(), CopyInlineVec::<i32>::CAPACITY);
    /// ```
    pub const fn capacity(&self) -> usize {
        self.base.capacity()
    }

    /// Reserves capacity for at least `additional` more elements.
    ///
    /// This method is provided for compatibility with standard vecs. Since the
    /// capacity is fixed at compile time, this method will panic if the new
    /// length exceeds the capacity.
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
    /// # use hipvec::inline::CopyInlineVec;
    /// let mut vec = CopyInlineVec::<i32>::new();
    /// vec.reserve(vec.capacity() + 1);
    /// ```
    pub const fn reserve(&mut self, additional: usize) {
        self.base.reserve(additional);
    }

    /// Reserves exactly `additional` more elements.
    ///
    /// This method is provided for compatibility with standard vecs. Since the
    /// capacity is fixed at compile time, this method will panic if the new
    /// length exceeds the capacity.
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
    /// # use hipvec::inline::CopyInlineVec;
    /// let mut vec = CopyInlineVec::<i32>::new();
    /// vec.reserve_exact(vec.capacity() + 1);
    /// ```
    pub const fn reserve_exact(&mut self, additional: usize) {
        self.base.reserve_exact(additional);
    }

    /// Appends an element to the end of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline::CopyInlineVec;
    /// let mut vec = CopyInlineVec::<i32>::new();
    /// vec.push(7);
    /// assert_eq!(vec.as_slice(), &[7]);
    /// ```
    pub const fn push(&mut self, value: T) {
        self.base.push(value);
    }

    /// Removes and returns the last element, if any.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline::CopyInlineVec;
    /// let mut vec = CopyInlineVec::<i32>::from([1, 2]);
    /// assert_eq!(vec.pop(), Some(2));
    /// assert_eq!(vec.pop(), Some(1));
    /// assert_eq!(vec.pop(), None);
    /// ```
    pub const fn pop(&mut self) -> Option<T> {
        self.base.pop()
    }

    /// Inserts an element at `index`, shifting later elements to the right.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline::CopyInlineVec;
    /// let mut vec = CopyInlineVec::<i32>::from([1, 3]);
    /// vec.insert(1, 2);
    /// assert_eq!(vec.as_slice(), &[1, 2, 3]);
    /// ```
    pub const fn insert(&mut self, index: usize, value: T) {
        self.base.insert(index, value);
    }

    /// Shortens the vector, keeping the first `new_len` elements.
    ///
    /// This function does nothing if the new length is greater than or equal to
    /// the current length.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline::CopyInlineVec;
    /// let mut vec = CopyInlineVec::<i32>::from([1, 2, 3]);
    /// vec.truncate(2);
    /// assert_eq!(vec.as_slice(), &[1, 2]);
    /// vec.truncate(5);
    /// assert_eq!(vec.as_slice(), &[1, 2]);
    /// ```
    pub const fn truncate(&mut self, new_len: usize) {
        let len = self.len();
        if new_len < len {
            unsafe {
                self.set_len(new_len);
            }
        }
    }

    /// Clears the vector, removing all elements.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline::CopyInlineVec;
    /// let mut vec = CopyInlineVec::<i32>::from([1, 2, 3].as_slice());
    /// vec.clear();
    /// assert!(vec.is_empty());
    /// ```
    pub const fn clear(&mut self)
    where
        L: Copy,
    {
        *self = Self::new();
    }

    #[inline]
    pub(crate) const fn from_slice(slice: &[T]) -> Self {
        assert!(slice.len() <= L::CAPACITY, "slice length exceeds capacity");

        let mut base = Self::new();
        unsafe {
            base.set_len(slice.len());
            let dst = base.as_mut_ptr();
            let src = slice.as_ptr();
            dst.copy_from_nonoverlapping(src, slice.len());
        }
        base
    }

    /// Copies and appends all elements in a slice to the vector.
    ///
    /// # Panics
    ///
    /// Panics if the new length exceeds the capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::inline::CopyInlineVec;
    /// let mut vec = CopyInlineVec::<i32>::from([1, 2]);
    /// vec.extend_from_slice(&[3, 4]);
    /// assert_eq!(vec.as_slice(), &[1, 2, 3, 4]);
    /// ```
    #[inline]
    pub const fn extend_from_slice(&mut self, slice: &[T]) {
        let additional = slice.len();
        self.reserve(additional);
        let len = self.len();
        unsafe {
            self.set_len(len + additional);
            let dst = self.as_mut_ptr().add(len);
            let src = slice.as_ptr();
            dst.copy_from_nonoverlapping(src, additional);
        }
    }

    #[inline]
    pub const fn spare_capacity_mut(&mut self) -> &mut [core::mem::MaybeUninit<T>] {
        self.base.spare_capacity_mut()
    }
}

impl<T: Copy, L: Layout<T>, const N: usize> From<[T; N]> for InlineVec<T, L> {
    fn from(value: [T; N]) -> Self {
        Self {
            base: Base::from_array(value),
        }
    }
}

impl<T: Copy, L: Layout<T>> From<&[T]> for InlineVec<T, L> {
    fn from(value: &[T]) -> Self {
        Self::from_slice(value)
    }
}

impl<T: Copy, L: Layout<T> + Copy> From<noncopy::InlineVec<T, L>> for InlineVec<T, L> {
    fn from(value: noncopy::InlineVec<T, L>) -> Self {
        let value = ManuallyDrop::new(value);
        Self { base: value.base }
    }
}

impl<T: Copy, L: Layout<T> + Copy> Copy for InlineVec<T, L> {}

impl<T: Copy, L: Layout<T> + Copy> Clone for InlineVec<T, L> {
    fn clone(&self) -> Self {
        *self
    }
}

impl_vector!(impl(T: Copy, L: Layout<T> + Copy) MutVector<Item=T> for InlineVec<T, L>);
