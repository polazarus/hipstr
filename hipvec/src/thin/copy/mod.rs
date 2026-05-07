use core::mem::transmute;
use core::ptr::NonNull;
use core::{fmt, ops};

use const_default::ConstDefault;

use super::TryReserveError;
use super::base::{Base, Reserved};
use crate::common::drain::Drain;
use crate::common::splice::Splice;
use crate::common::traits::impl_extend;
use crate::common::{methods, unwrap_display};
use crate::traits::{GrowableVector, impl_vector};

#[cfg(test)]
mod tests;

#[repr(transparent)]
pub struct ThinVec<T: Copy> {
    base: Base<T, Reserved>,
}

impl<T: Copy> Default for ThinVec<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Copy> ConstDefault for ThinVec<T> {
    const DEFAULT: Self = Self::new();
}

impl<T: Copy> ThinVec<T> {
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
    #[cfg_attr(debug_assertions, track_caller)]
    pub const unsafe fn set_len(&mut self, len: usize) {
        unsafe { self.base.set_len(len) };
    }

    /// Removes the last element from a vector and returns it, or [`None`] if it
    /// is empty.
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
    /// # use hipvec::copy_thin_vec;
    /// let mut v = copy_thin_vec![b'a', b'b', b'c'];
    /// assert_eq!(v.remove(1), b'b');
    /// assert_eq!(v.as_slice(), [b'a', b'c']);
    /// ```
    #[inline]
    pub fn remove(&mut self, index: usize) -> T {
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
    /// # use hipvec::copy_thin_vec;
    /// let mut v = copy_thin_vec!["foo", "bar", "baz", "qux"];
    ///
    /// assert_eq!(v.swap_remove(1), "bar");
    /// assert_eq!(v.as_slice(), ["foo", "qux", "baz"]);
    ///
    /// assert_eq!(v.swap_remove(0), "foo");
    /// assert_eq!(v.as_slice(), ["baz", "qux"]);
    /// ```
    #[inline]
    pub fn swap_remove(&mut self, index: usize) -> T {
        self.base.swap_remove(index)
    }

    /// Shortens the vector, keeping the first `len` elements and dropping
    /// the rest.
    ///
    /// If `len` is greater or equal to the vector's current length, this has
    /// no effect.
    ///
    /// The [`drain`] method can emulate `truncate`, but causes the excess
    /// elements to be returned instead of dropped.
    ///
    /// Note that this method has no effect on the allocated capacity
    /// of the vector.
    ///
    /// # Examples
    ///
    /// Truncating a five element vector to two elements:
    ///
    /// ```
    /// # use hipvec::copy_thin_vec;
    /// let mut vec = copy_thin_vec![1, 2, 3, 4, 5];
    /// vec.truncate(2);
    /// assert_eq!(vec.as_slice(), [1, 2]);
    /// ```
    ///
    /// No truncation occurs when `len` is greater than the vector's current
    /// length:
    ///
    /// ```
    /// # use hipvec::copy_thin_vec;
    /// let mut vec = copy_thin_vec![1, 2, 3];
    /// vec.truncate(8);
    /// assert_eq!(vec.as_slice(), [1, 2, 3]);
    /// ```
    ///
    /// Truncating when `len == 0` is equivalent to calling the [`clear`]
    /// method.
    ///
    /// ```
    /// # use hipvec::copy_thin_vec;
    /// let mut vec = copy_thin_vec![1, 2, 3];
    /// vec.truncate(0);
    /// assert!(vec.is_empty());
    /// ```
    ///
    /// [`clear`]: Self::clear
    /// [`drain`]: Self::drain
    #[inline]
    pub const fn truncate(&mut self, new_len: usize) {
        self.base.truncate_copy(new_len);
    }

    /// Clears the vector, removing all values.
    ///
    /// Note that this method has no effect on the allocated capacity
    /// of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::copy_thin_vec;
    /// let mut vec = copy_thin_vec![1, 2, 3];
    ///
    /// vec.clear();
    ///
    /// assert!(vec.is_empty());
    /// ```
    #[inline]
    pub const fn clear(&mut self) {
        self.base.clear_copy();
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
    /// # use hipvec::copy_thin_vec;
    /// let mut v = copy_thin_vec![1_u8, 2, 3];
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
        unwrap_display(Drain::new(self, range))
    }

    pub(crate) fn into_base(self) -> Base<T, Reserved> {
        unsafe { transmute::<Self, Base<T, Reserved>>(self) }
    }
}

impl<T: Copy> ThinVec<T> {
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
    pub fn with_capacity(cap: usize) -> Self {
        Self {
            base: Base::with_capacity(cap),
        }
    }

    /// Constructs a new, empty vector with at least the specified capacity.
    ///
    /// The vector will be able to hold at least `capacity` elements without
    /// reallocating. This method is allowed to allocate for more elements than
    /// `capacity`. If `capacity` is zero, the vector will not allocate.
    ///
    /// # Errors
    ///
    /// Returns an error if the capacity exceeds `isize::MAX` _bytes_,
    /// or if the allocator reports allocation failure.
    #[inline]
    pub fn try_with_capacity(capacity: usize) -> Result<Self, TryReserveError> {
        Ok(Self {
            base: Base::try_with_capacity(capacity)?,
        })
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
    #[inline]
    pub fn reserve_exact(&mut self, additional: usize) {
        self.base.reserve_exact(additional);
    }

    /// Tries to reserve capacity for at least `additional` more elements to be inserted
    /// in the given vector. The collection may reserve more space to speculatively avoid
    /// frequent reallocations. After calling `try_reserve`, capacity will be
    /// greater than or equal to `self.len() + additional` if it returns
    /// `Ok(())`. Does nothing if capacity is already sufficient. This method
    /// preserves the contents even if an error occurs.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error
    /// is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipvec::common::TryReserveError;
    /// use hipvec::thin::CopyThinVec;
    ///
    /// fn process_data(data: &[u32]) -> Result<CopyThinVec<u32>, TryReserveError> {
    ///     let mut output = CopyThinVec::new();
    ///
    ///     // Pre-reserve the memory, exiting if we can't
    ///     output.try_reserve(data.len())?;
    ///
    ///     // Now we know this can't OOM in the middle of our complex work
    ///     output.extend(data.iter().map(|&val| {
    ///         val * 2 + 5 // very complicated
    ///     }));
    ///
    ///     Ok(output)
    /// }
    /// # process_data(&[1, 2, 3]).expect("why is the test harness OOMing on 12 bytes?");
    /// ```
    #[inline]
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.base.try_reserve(additional)
    }

    /// Tries to reserve the minimum capacity for at least `additional`
    /// elements to be inserted in the given vector. Unlike [`try_reserve`],
    /// this will not deliberately over-allocate to speculatively avoid frequent
    /// allocations. After calling `try_reserve_exact`, capacity will be greater
    /// than or equal to `self.len() + additional` if it returns `Ok(())`.
    /// Does nothing if the capacity is already sufficient.
    ///
    /// Note that the allocator may give the collection more space than it
    /// requests. Therefore, capacity can not be relied upon to be precisely
    /// minimal. Prefer [`try_reserve`] if future insertions are expected.
    ///
    /// [`try_reserve`]: Self::try_reserve
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error
    /// is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipvec::common::TryReserveError;
    /// use hipvec::thin::CopyThinVec;
    ///
    /// fn process_data(data: &[u32]) -> Result<CopyThinVec<u32>, TryReserveError> {
    ///     let mut output = CopyThinVec::new();
    ///
    ///     // Pre-reserve the memory, exiting if we can't
    ///     output.try_reserve_exact(data.len())?;
    ///
    ///     // Now we know this can't OOM in the middle of our complex work
    ///     output.extend(data.iter().map(|&val| {
    ///         val * 2 + 5 // very complicated
    ///     }));
    ///
    ///     Ok(output)
    /// }
    /// # process_data(&[1, 2, 3]).expect("why is the test harness OOMing on 12 bytes?");
    /// ```
    #[inline]
    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.base.try_reserve_exact(additional)
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

    /// Appends an element and returns a reference to it if there is sufficient spare capacity,
    /// otherwise an error is returned with the element.
    ///
    /// Unlike [`push`] this method will not reallocate when there's insufficient capacity.
    /// The caller should use [`reserve`] or [`try_reserve`] to ensure that there is enough capacity.
    ///
    /// [`push`]: Self::push
    /// [`reserve`]: Self::reserve
    /// [`try_reserve`]: Self::try_reserve
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::copy_thin_vec;
    /// let mut vec = copy_thin_vec![0, 1];
    /// let capacity = vec.capacity();
    /// for i in 2..capacity {
    ///   vec.push_within_capacity(i).unwrap();
    /// }
    ///
    /// vec.push_within_capacity(capacity).unwrap_err();
    /// ```
    ///
    /// # Time complexity
    ///
    /// Takes *O*(1) time.
    #[inline]
    pub fn push_within_capacity(&mut self, value: T) -> Result<&mut T, T> {
        self.base.push_within_capacity(value)
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
    /// Takes *O*(length) time. All items after the insertion index must be
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
    /// Takes *O*(length) time. All items after the insertion index must be
    /// shifted to the right. In the worst case, all elements are shifted when
    /// the insertion index is 0.
    #[inline]
    pub fn insert_mut(&mut self, index: usize, value: T) -> &mut T {
        self.base.insert_mut(index, value)
    }

    /// Copies and appends all elements in a slice to the vector.
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
    /// # use hipvec::copy_thin_vec;
    /// let mut vec = copy_thin_vec![1];
    /// vec.extend_from_slice(&[2, 3, 4]);
    /// assert_eq!(vec.as_slice(), [1, 2, 3, 4]);
    /// ```
    pub fn extend_from_slice(&mut self, slice: &[T]) {
        methods::extend_from_slice_copy!(self, slice);
    }

    /// Appends all elements of the array to the vector.
    ///
    /// The elements are moved and not cloned.
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
    #[inline]
    pub fn extend_from_array<const N: usize>(&mut self, array: [T; N]) {
        self.base.extend_from_array(array)
    }

    /// Moves all the elements of `other` into `self`, leaving `other` empty.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` _bytes_.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::copy_thin_vec;
    /// # use std::vec;
    /// let mut vec = copy_thin_vec![1, 2, 3];
    /// let mut vec2 = vec![4, 5, 6];
    /// vec.append(&mut vec2);
    /// assert_eq!(vec.as_slice(), [1, 2, 3, 4, 5, 6]);
    /// assert_eq!(vec2.as_slice(), []);
    /// ```
    #[inline]
    pub fn append(&mut self, other: &mut impl GrowableVector<Item = T>) {
        self.base.append(other);
    }

    /// Splits the collection into two at the given index.
    ///
    /// Returns a newly allocated vector containing the elements in the range
    /// `[at, len)`. After the call, the original vector will be left containing
    /// the elements `[0, at)` with its previous capacity unchanged.
    ///
    /// - If you want to take ownership of the entire contents and capacity of
    ///   the vector, see [`std::mem::take`] or [`std::mem::replace`].
    /// - If you don't need the returned vector at all, see [`truncate`].
    /// - If you want to take ownership of an arbitrary subslice, or you don't
    ///   necessarily want to store the removed items in a vector, see [`drain`].
    ///
    /// # Panics
    ///
    /// Panics if `at > len`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::copy_thin_vec;
    /// let mut v = copy_thin_vec!['a', 'b', 'c'];
    /// let w = v.split_off(1);
    /// assert_eq!(v.as_slice(), ['a']);
    /// assert_eq!(w.as_slice(), ['b', 'c']);
    /// ```
    ///
    /// [`truncate`]: Self::truncate
    /// [`drain`]: Self::drain
    #[inline]
    #[track_caller]
    #[must_use = "use .truncate() if you don't need the returned vector"]
    pub fn split_off(&mut self, at: usize) -> Self {
        Self {
            base: self.base.split_off(at),
        }
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
    /// Panics if the new capacity overflows or if the reallocations fails.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::copy_thin_vec;
    /// let mut vec = copy_thin_vec!["hello"];
    /// vec.resize(3, "world");
    /// assert_eq!(vec.as_slice(), ["hello", "world", "world"]);
    ///
    /// let mut vec = copy_thin_vec!['a', 'b', 'c', 'd'];
    /// vec.resize(2, '_');
    /// assert_eq!(vec.as_slice(), ['a', 'b']);
    /// ```
    #[inline]
    pub fn resize(&mut self, new_len: usize, value: T)
    where
        T: Clone,
    {
        self.base.resize_copy(new_len, value);
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
    /// Panics if the new capacity overflows or if the reallocations fails.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::copy_thin_vec;
    /// let mut vec = copy_thin_vec![1, 2, 3];
    /// vec.resize_with(5, Default::default);
    /// assert_eq!(vec.as_slice(), [1, 2, 3, 0, 0]);
    ///
    /// let mut vec = copy_thin_vec![];
    /// let mut p = 1;
    /// vec.resize_with(4, || { p *= 2; p });
    /// assert_eq!(vec.as_slice(), [2, 4, 8, 16]);
    /// ```
    #[inline]
    pub fn resize_with(&mut self, new_len: usize, f: impl FnMut() -> T) {
        self.base.resize_with(new_len, f);
    }

    /// Creates a splicing iterator that replaces the specified range in the vector
    /// with the given `replace_with` iterator and yields the removed items.
    /// `replace_with` does not need to be the same length as `range`.
    ///
    /// `range` is removed even if the `Splice` iterator is not consumed before it is dropped.
    ///
    /// It is unspecified how many elements are removed from the vector
    /// if the `Splice` value is leaked.
    ///
    /// The input iterator `replace_with` is only consumed when the `Splice` value is dropped.
    ///
    /// This is optimal if:
    ///
    /// * The tail (elements in the vector after `range`) is empty,
    /// * or `replace_with` yields fewer or equal elements than `range`'s length
    /// * or the lower bound of its `size_hint()` is exact.
    ///
    /// Otherwise, a temporary vector is allocated and the tail is moved twice.
    ///
    /// # Panics
    ///
    /// Panics if the range has `start_bound > end_bound`, or, if the range is
    /// bounded on either end and past the length of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipvec::copy_thin_vec;
    /// let mut v = copy_thin_vec![1, 2, 3, 4];
    /// let new = [7, 8, 9];
    /// let u: Vec<_> = v.splice(1..3, new).collect();
    /// assert_eq!(v.as_slice(), [1, 7, 8, 9, 4]);
    /// assert_eq!(u.as_slice(), [2, 3]);
    /// ```
    ///
    /// Using `splice` to insert new items into a vector efficiently at a specific position
    /// indicated by an empty range:
    ///
    /// ```
    /// # use hipvec::copy_thin_vec;
    /// let mut v = copy_thin_vec![1, 5];
    /// let new = [2, 3, 4];
    /// v.splice(1..1, new);
    /// assert_eq!(v.as_slice(), [1, 2, 3, 4, 5]);
    /// ```
    #[inline]
    pub fn splice<I: Iterator<Item = T>>(
        &mut self,
        range: impl ops::RangeBounds<usize>,
        replace_with: impl IntoIterator<IntoIter = I>,
    ) -> Splice<'_, Self, I> {
        unwrap_display(Splice::new(self, range, replace_with))
    }
}

impl<T: Copy> Drop for ThinVec<T> {
    fn drop(&mut self) {
        unsafe {
            self.base.drop_copy();
        }
    }
}

impl<T: Copy> Clone for ThinVec<T> {
    fn clone(&self) -> Self {
        Self::from(self.as_slice())
    }
}

impl<T: Copy> From<&[T]> for ThinVec<T> {
    fn from(slice: &[T]) -> Self {
        Self {
            base: Base::from_slice_copy(slice),
        }
    }
}

impl<T: Copy, const N: usize> From<&[T; N]> for ThinVec<T> {
    fn from(arr_ref: &[T; N]) -> Self {
        Self::from(arr_ref.as_slice())
    }
}

impl<T: Copy, const N: usize> From<[T; N]> for ThinVec<T> {
    fn from(array: [T; N]) -> Self {
        Self {
            base: Base::from_array(array),
        }
    }
}

impl<T: fmt::Debug + Copy> fmt::Debug for ThinVec<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_slice().fmt(f)
    }
}

impl<T: Copy> ops::Deref for ThinVec<T> {
    type Target = [T];
    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<T: Copy> ops::DerefMut for ThinVec<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut_slice()
    }
}

impl_vector!(impl(T: Copy) Vector<Item=T> for ThinVec<T>);
impl_vector!(impl(T: Copy) MutableVector<Item=T> for ThinVec<T>);
impl_vector!(impl(T: Copy) GrowableVector<Item=T> for ThinVec<T>);

impl_extend!(ThinVec<T>, T, [T: Copy], []);
