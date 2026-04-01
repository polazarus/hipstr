use core::fmt;
use core::ptr::NonNull;

use const_default::ConstDefault;

use super::base::Base;
use crate::common::methods;

#[repr(transparent)]
pub struct ThinVec<T, P> {
    base: Base<T, P>,
}

impl<T, P> Default for ThinVec<T, P> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T, P> ConstDefault for ThinVec<T, P> {
    const DEFAULT: Self = Self::new();
}

impl<T, P> ThinVec<T, P> {
    /// Constructs a new, empty vector.
    ///
    /// The vector will not allocate until elements are pushed onto it.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(unused_mut)]
    /// # use hipvec::thin::CopyThinVec;
    /// let mut vec: CopyThinVec<i32> = CopyThinVec::new();
    /// ```
    #[inline]
    pub const fn new() -> Self {
        Self { base: Base::new() }
    }

    /// Returns the number of elements in the vector, also referred to as its 'length'.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::copy_thin_vec;
    /// let a = copy_thin_vec![1, 2, 3];
    /// assert_eq!(a.len(), 3);
    /// ```
    #[inline]
    pub const fn len(&self) -> usize {
        self.base.len()
    }

    /// Returns `true` if the vector contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::thin::CopyThinVec;
    /// let mut v = CopyThinVec::new();
    /// assert!(v.is_empty());
    ///
    /// v.push(1);
    /// assert!(!v.is_empty());
    /// ```
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.base.is_empty()
    }

    /// Returns the total number of elements the vector can hold without
    /// reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::thin::CopyThinVec;
    /// let mut vec: CopyThinVec<i32> = CopyThinVec::with_capacity(10);
    /// vec.push(42);
    /// assert!(vec.capacity() >= 10);
    /// ```
    #[inline]
    pub const fn capacity(&self) -> usize {
        self.base.capacity()
    }

    /// Returns a raw pointer to the vector's buffer, or a dangling raw pointer
    /// valid for zero sized reads if the vector didn't allocate.
    ///
    /// The caller must ensure that the vector outlives the pointer this
    /// function returns, or else it will end up dangling.
    /// Modifying the vector may cause its buffer to be reallocated,
    /// which would also make any pointers to it invalid.
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
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::copy_thin_vec;
    /// let x = copy_thin_vec![1, 2, 4];
    /// let x_ptr = x.as_ptr();
    ///
    /// unsafe {
    ///     for i in 0..x.len() {
    ///         assert_eq!(*x_ptr.add(i), 1 << i);
    ///     }
    /// }
    /// ```
    ///
    /// Due to the aliasing guarantee, the following code is legal:
    ///
    /// ```rust
    ///  # use hipvec::copy_thin_vec;
    /// unsafe {
    ///     let mut v = copy_thin_vec![0, 1, 2];
    ///     let ptr1 = v.as_ptr();
    ///     let _ = ptr1.read();
    ///     let ptr2 = v.as_mut_ptr().offset(2);
    ///     ptr2.write(2);
    ///     // Notably, the write to `ptr2` did *not* invalidate `ptr1`
    ///     // because it mutated a different element:
    ///     let _ = ptr1.read();
    /// }
    /// ```
    ///
    /// [`as_mut_ptr`]: Self::as_mut_ptr
    /// [`as_ptr`]: Self::as_ptr
    /// [`as_non_null`]: Self::as_non_null
    #[inline]
    pub const fn as_ptr(&self) -> *const T {
        self.base.as_ptr()
    }

    /// Returns a raw mutable pointer to the vector's buffer, or a dangling
    /// raw pointer valid for zero sized reads if the vector didn't allocate.
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
    /// The method also guarantees that, as long as `T` is not zero-sized and the capacity is
    /// nonzero, the pointer may be passed into [`dealloc`] with a layout of
    /// `Layout::array::<T>(capacity)` in order to deallocate the backing memory. If this is done,
    /// be careful not to run the destructor of the `Vec`, as dropping it will result in
    /// double-frees. Wrapping the `Vec` in a [`ManuallyDrop`] is the typical way to achieve this.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::thin::CopyThinVec;
    /// // Allocate vector big enough for 4 elements.
    /// let size = 4;
    /// let mut x: CopyThinVec<i32> = CopyThinVec::with_capacity(size);
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
    ///
    /// Due to the aliasing guarantee, the following code is legal:
    ///
    /// ```rust
    /// # use hipvec::copy_thin_vec;
    /// unsafe {
    ///     let mut v = copy_thin_vec![0];
    ///     let ptr1 = v.as_mut_ptr();
    ///     ptr1.write(1);
    ///     let ptr2 = v.as_mut_ptr();
    ///     ptr2.write(2);
    ///     // Notably, the write to `ptr2` did *not* invalidate `ptr1`:
    ///     ptr1.write(3);
    /// }
    /// ```
    ///
    /// [`as_mut_ptr`]: Self::as_mut_ptr
    /// [`as_ptr`]: Self::as_ptr
    /// [`as_non_null`]: Self::as_non_null
    #[inline]
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
    /// # use hipvec::{copy_thin_vec, thin::CopyThinVec};
    /// // Allocate vector big enough for 4 elements.
    /// let size = 4;
    /// let mut x: CopyThinVec<i32> = CopyThinVec::with_capacity(size);
    /// let x_ptr = x.as_non_null();
    ///
    /// // Initialize elements via raw pointer writes, then set length.
    /// unsafe {
    ///     for i in 0..size {
    ///         x_ptr.add(i).write(i as i32);
    ///     }
    ///     x.set_len(size);
    /// }
    /// assert_eq!(x.as_slice(), &[0, 1, 2, 3]);
    /// ```
    ///
    /// Due to the aliasing guarantee, the following code is legal:
    ///
    /// ```rust
    /// # use hipvec::{copy_thin_vec, thin::CopyThinVec};
    ///
    /// unsafe {
    ///     let mut v = copy_thin_vec![0];
    ///     let ptr1 = v.as_non_null();
    ///     ptr1.write(1);
    ///     let ptr2 = v.as_non_null();
    ///     ptr2.write(2);
    ///     // Notably, the write to `ptr2` did *not* invalidate `ptr1`:
    ///     ptr1.write(3);
    /// }
    /// ```
    ///
    /// [`as_mut_ptr`]: Self::as_mut_ptr
    /// [`as_ptr`]: Self::as_ptr
    /// [`as_non_null`]: Self::as_non_null
    #[inline]
    pub const fn as_non_null(&mut self) -> NonNull<T> {
        self.base.as_non_null()
    }

    /// Extracts a slice containing the entire vector.
    ///
    /// Equivalent to `&s[..]`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::copy_thin_vec;
    /// use std::io::{self, Write};
    /// let buffer = copy_thin_vec![1, 2, 3, 5, 8];
    /// io::sink().write(buffer.as_slice()).unwrap();
    /// ```
    #[inline]
    pub const fn as_slice(&self) -> &[T] {
        self.base.as_slice()
    }

    /// Extracts a mutable slice of the entire vector.
    ///
    /// Equivalent to `&mut s[..]`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::copy_thin_vec;
    /// use std::io::{self, Read};
    /// let mut buffer = copy_thin_vec![0; 3];
    /// io::repeat(0b101).read_exact(buffer.as_mut_slice()).unwrap();
    /// ```
    #[inline]
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
    /// # use hipvec::thin::CopyThinVec;
    /// // Allocate vector big enough for 10 elements.
    /// let mut v = CopyThinVec::with_capacity(10);
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
    /// assert_eq!(v.as_slice(), &[0, 1, 2]);
    /// ```
    #[inline]
    pub const fn spare_capacity_mut(&mut self) -> &mut [core::mem::MaybeUninit<T>] {
        self.base.spare_capacity_mut()
    }

    /// Forces the length of the vector to `new_len`.
    ///
    /// # Safety
    ///
    /// - `new_len` must not exceed the current capacity of the vector.
    /// - If `new_len` is greater than the current length, the new elements must be properly initialized.
    ///
    /// # Examples
    ///
    /// See [`spare_capacity_mut()`] for an example with safe
    /// initialization of capacity elements and use of this method.
    ///
    /// [`spare_capacity_mut()`]: Self::spare_capacity_mut
    #[inline]
    pub unsafe fn set_len(&mut self, len: usize) {
        unsafe { self.base.set_len(len) };
    }

    /// Removes the last element from a vector and returns it, or [`None`] if it
    /// is empty.
    ///
    /// If you'd like to pop the first element, consider using
    /// [`VecDeque::pop_front`] instead.
    ///
    /// [`VecDeque::pop_front`]: crate::collections::VecDeque::pop_front
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::copy_thin_vec;
    /// let mut vec = copy_thin_vec![1, 2, 3];
    /// assert_eq!(vec.pop(), Some(3));
    /// assert_eq!(vec.as_slice(), &[1, 2]);
    /// ```
    ///
    /// # Time complexity
    ///
    /// Takes *O*(1) time.
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        self.base.pop()
    }

    /// Removes and returns the last element from a vector if the predicate
    /// returns `true`, or [`None`] if the predicate returns false or the vector
    /// is empty (the predicate will not be called in that case).
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::copy_thin_vec;
    /// let mut vec = copy_thin_vec![1, 2, 3, 4];
    /// let pred = |x: &mut i32| *x % 2 == 0;
    ///
    /// assert_eq!(vec.pop_if(pred), Some(4));
    /// assert_eq!(vec.as_slice(), &[1, 2, 3]);
    /// assert_eq!(vec.pop_if(pred), None);
    /// ```
    #[inline]
    pub fn pop_if(&mut self, predicate: impl FnOnce(&mut T) -> bool) -> Option<T> {
        self.base.pop_if(predicate)
    }
}

impl<T, P> ThinVec<T, P>
where
    P: ConstDefault,
{
    /// Constructs a new, empty vector with at least the specified capacity.
    ///
    /// The vector will be able to hold at least `capacity` elements without
    /// reallocating. This method is allowed to allocate for more elements than
    /// `capacity`. If `capacity` is zero, the vector will not allocate.
    ///
    /// It is important to note that although the returned vector has the
    /// minimum *capacity* specified, the vector will have a zero *length*. For
    /// an explanation of the difference between length and capacity, see
    /// *[Capacity and reallocation]*.
    ///
    /// If it is important to know the exact allocated capacity of a thin vector,
    /// always use the [`capacity`] method after construction.
    ///
    /// [Capacity and reallocation]: #capacity-and-reallocation
    /// [`capacity`]: Self::capacity
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` _bytes_.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::thin::CopyThinVec;
    /// let mut vec = CopyThinVec::with_capacity(10);
    ///
    /// // The vector contains no items, even though it has capacity for more
    /// assert_eq!(vec.len(), 0);
    /// assert!(vec.capacity() >= 10);
    ///
    /// // These are all done without reallocating...
    /// for i in 0..10 {
    ///     vec.push(i);
    /// }
    /// assert_eq!(vec.len(), 10);
    /// assert!(vec.capacity() >= 10);
    ///
    /// // ...but this may make the vector reallocate
    /// vec.push(11);
    /// assert_eq!(vec.len(), 11);
    /// assert!(vec.capacity() >= 11);
    ///
    /// // A vector of a zero-sized type with a non-zero capacity will always "over-allocate".
    /// let vec_units = CopyThinVec::<()>::with_capacity(10);
    /// assert_eq!(vec_units.capacity(), usize::MAX);
    /// ```
    #[inline]
    pub fn with_capacity(cap: usize) -> Self
    where
        P: ConstDefault,
    {
        Self {
            base: Base::with_capacity(cap),
        }
    }

    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the given vector. The collection may reserve more space to
    /// speculatively avoid frequent reallocations. After calling `reserve`,
    /// capacity will be greater than or equal to `self.len() + additional`.
    /// Does nothing if capacity is already sufficient.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` _bytes_.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::copy_thin_vec;
    /// let mut vec = copy_thin_vec![1];
    /// vec.reserve(10);
    /// assert!(vec.capacity() >= 11);
    /// ```
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        self.base.reserve(additional);
    }

    /// Reserves the minimum capacity for at least `additional` more elements to
    /// be inserted in the given vector. Unlike [`reserve`], this will not
    /// deliberately over-allocate to speculatively avoid frequent allocations.
    /// After calling `reserve_exact`, capacity will be greater than or equal to
    /// `self.len() + additional`. Does nothing if the capacity is already
    /// sufficient.
    ///
    /// Note that the allocator may give the collection more space than it
    /// requests. Therefore, capacity can not be relied upon to be precisely
    /// minimal. Prefer [`reserve`] if future insertions are expected.
    ///
    /// [`reserve`]: Self::reserve
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` _bytes_.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::copy_thin_vec;
    /// let mut vec = copy_thin_vec![1];
    /// vec.reserve_exact(10);
    /// assert!(vec.capacity() >= 11);
    /// ```
    pub fn reserve_exact(&mut self, additional: usize) {
        self.base.reserve_exact(additional);
    }

    /// Appends an element to the back of a collection.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows or if the reallocation fails.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::copy_thin_vec;
    /// let mut vec = copy_thin_vec![1, 2];
    /// vec.push(3);
    /// assert_eq!(vec.as_slice(), [1, 2, 3]);
    /// ```
    ///
    /// # Time complexity
    ///
    /// Takes amortized *O*(1) time. If the vector's length would exceed its
    /// capacity after the push, *O*(*capacity*) time is taken to copy the
    /// vector's elements to a larger allocation. This expensive operation is
    /// offset by the *capacity* *O*(1) insertions it allows.
    #[inline]
    pub fn push(&mut self, value: T) {
        self.base.push(value)
    }

    /// Appends an element to the back of a collection, returning a reference to it.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows or if the reallocation fails.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::copy_thin_vec;
    ///
    /// let mut vec = copy_thin_vec![1, 2];
    /// let last = vec.push_mut(3);
    /// assert_eq!(*last, 3);
    /// assert_eq!(vec.as_slice(), [1, 2, 3]);
    ///
    /// let last = vec.push_mut(3);
    /// *last += 1;
    /// assert_eq!(vec.as_slice(), [1, 2, 3, 4]);
    /// ```
    ///
    /// # Time complexity
    ///
    /// Takes amortized *O*(1) time. If the vector's length would exceed its
    /// capacity after the push, *O*(*capacity*) time is taken to copy the
    /// vector's elements to a larger allocation. This expensive operation is
    /// offset by the *capacity* *O*(1) insertions it allows.
    #[inline]
    pub fn push_mut(&mut self, value: T) -> &mut T {
        self.base.push_mut(value)
    }

    /// Inserts an element at position `index` within the vector, shifting all
    /// elements after it to the right.
    ///
    /// # Panics
    ///
    /// Panics if `index > len`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::copy_thin_vec;
    /// let mut vec = copy_thin_vec!['a', 'b', 'c'];
    /// vec.insert(1, 'd');
    /// assert_eq!(vec.as_slice(), ['a', 'd', 'b', 'c']);
    /// vec.insert(4, 'e');
    /// assert_eq!(vec.as_slice(), ['a', 'd', 'b', 'c', 'e']);
    /// ```
    ///
    /// # Time complexity
    ///
    /// Takes *O*([`Vec::len`]) time. All items after the insertion index must be
    /// shifted to the right. In the worst case, all elements are shifted when
    /// the insertion index is 0.
    #[inline]
    pub fn insert(&mut self, index: usize, value: T) {
        self.base.insert(index, value)
    }

    /// Inserts an element at position `index` within the vector, shifting all
    /// elements after it to the right, and returning a reference to the new
    /// element.
    ///
    /// # Panics
    ///
    /// Panics if `index > len`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::copy_thin_vec;
    /// let mut vec = copy_thin_vec![1, 3, 5, 9];
    /// let x = vec.insert_mut(3, 6);
    /// *x += 1;
    /// assert_eq!(vec.as_slice(), [1, 3, 5, 7, 9]);
    /// ```
    ///
    /// # Time complexity
    ///
    /// Takes *O*([`Vec::len`]) time. All items after the insertion index must be
    /// shifted to the right. In the worst case, all elements are shifted when
    /// the insertion index is 0.
    #[inline]
    pub fn insert_mut(&mut self, index: usize, value: T) -> &mut T {
        self.base.insert_mut(index, value)
    }

    /// Copies and appends all elements in a slice to the `Vec`.
    ///
    /// The `other` slice is traversed in-order.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows or if the reallocations fails.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = vec![1];
    /// vec.extend_from_slice(&[2, 3, 4]);
    /// assert_eq!(vec, [1, 2, 3, 4]);
    /// ```
    ///
    /// [`extend`]: Vec::extend
    pub fn extend_from_slice(&mut self, slice: &[T]) {
        methods::extend_from_slice_copy!(self, slice);
    }

    /// Appends all elements of the array to the `Vec`.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows or if the reallocations fails.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::copy_thin_vec;
    /// let mut vec = copy_thin_vec![1];
    /// vec.extend_from_array([2, 3, 4]);
    /// assert_eq!(vec.as_slice(), [1, 2, 3, 4]);
    /// ```
    ///
    /// [`extend`]: Vec::extend
    pub fn extend_from_array<const N: usize>(&mut self, array: [T; N]) {
        self.base.extend_from_array(array)
    }
}

impl<T: Copy, P: ConstDefault> From<&[T]> for ThinVec<T, P> {
    fn from(slice: &[T]) -> Self {
        let mut vec = Self::new();
        vec.extend_from_slice(slice);
        vec
    }
}

impl<T: Copy, P: ConstDefault, const N: usize> From<&[T; N]> for ThinVec<T, P> {
    fn from(arr_ref: &[T; N]) -> Self {
        Self::from(arr_ref.as_slice())
    }
}

impl<T: Copy, P: ConstDefault, const N: usize> From<[T; N]> for ThinVec<T, P> {
    fn from(array: [T; N]) -> Self {
        Self::from(array.as_slice())
    }
}

impl<T: fmt::Debug, P> fmt::Debug for ThinVec<T, P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_slice().fmt(f)
    }
}
