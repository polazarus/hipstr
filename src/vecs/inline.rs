//! Inline vector implementation.
//!
//! This module provides an inline vector implementation that can store up to a
//! small and fixed number of elements inline.
//!
//! Particularly space efficient, this implementation may in some case be more
//! efficient than the standard library vectors.

use alloc::vec::Vec;
use core::fmt::{self};
use core::iter::FusedIterator;
use core::mem::{ManuallyDrop, MaybeUninit};
use core::num::NonZeroU8;
use core::ops::{Deref, DerefMut, Range, RangeBounds};
use core::ptr::NonNull;
use core::{error, hash, slice};

use crate::{common, macros};

#[cfg(test)]
mod tests;

pub const SHIFT_DEFAULT: u8 = 1;
pub const TAG_DEFAULT: u8 = 1;

#[repr(transparent)]
#[derive(Clone, Copy)]
struct TaggedU8<const SHIFT: u8, const TAG: u8>(NonZeroU8);

impl<const SHIFT: u8, const TAG: u8> TaggedU8<SHIFT, TAG> {
    const fn max() -> usize {
        const {
            assert!(SHIFT > 0, "SHIFT must be greater than 0");
            assert!(SHIFT < 8, "SHIFT must be less than 8");
        }
        u8::MAX as usize >> SHIFT
    }

    const fn new(len: usize) -> Self {
        const {
            assert!(SHIFT > 0, "SHIFT must be greater than 0");
            assert!(SHIFT < 8, "SHIFT must be less than 8");
            assert!(TAG > 0, "TAG must be greater than 0");
            assert!(TAG < (1 << SHIFT), "TAG must be less than 1 << SHIFT");
        }
        assert!(
            len <= Self::max(),
            "length exceeds maximal tagged length (`256 >> SHIFT`)"
        );
        let shifted = len << SHIFT;
        let value = shifted as u8 | TAG;
        Self(unsafe { NonZeroU8::new_unchecked(value) })
    }

    const fn get(self) -> usize {
        (self.0.get() >> SHIFT) as usize
    }
}

/// A vector that can store a small number of elements inline.
///
/// This struct is designed to be used in situations where the maximum number of
/// elements is small and known at compile time. It uses a fixed-size array
/// internally to store the elements, and it can be more efficient than using a
/// heap-allocated vector for small collections.
///
/// # Examples
///
/// ```
/// use hipstr::vecs::InlineVec;
/// let mut inline = InlineVec::<u8, 7>::new();
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
/// This is because the maximal length is capped by `u8::MAX >> TAG_SHIFT`.
///
/// The compiler will statically reject any `InlineVec` with `CAP` greater than
/// `u8::MAX >> TAG_SHIFT`.
#[repr(C)]
pub struct InlineVec<
    T,
    const CAP: usize,
    const SHIFT: u8 = SHIFT_DEFAULT,
    const TAG: u8 = TAG_DEFAULT,
> {
    #[cfg(target_endian = "little")]
    len: TaggedU8<SHIFT, TAG>,

    data: [MaybeUninit<T>; CAP],

    #[cfg(target_endian = "big")]
    len: TaggedU8<SHIFT, TAG>,
}

impl<T, const CAP: usize, const SHIFT: u8, const TAG: u8> InlineVec<T, CAP, SHIFT, TAG> {
    /// Creates a new inline vector with the specified capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::InlineVec;
    /// let inline = InlineVec::<u8, 7>::new();
    /// assert_eq!(inline.len(), 0);
    /// assert_eq!(inline.capacity(), 7);
    /// ```
    #[inline(always)]
    pub const fn new() -> Self {
        const {
            assert!(CAP != 0);
            assert!(CAP <= TaggedU8::<SHIFT, TAG>::max());
            Self {
                len: TaggedU8::new(0),
                data: unsafe { MaybeUninit::uninit().assume_init() },
            }
        }
    }

    #[inline(always)]
    pub const unsafe fn zeroed(new_len: usize) -> Self {
        const {
            assert!(CAP != 0);
            assert!(CAP <= TaggedU8::<SHIFT, TAG>::max());
        }
        Self {
            len: TaggedU8::new(new_len),
            data: unsafe { MaybeUninit::zeroed().assume_init() },
        }
    }

    /// Creates a new inline vector from an array by moving the element.
    ///
    /// The array's length `N` is checked at compile time. It must to be less
    /// than or equal to the `CAP` generic const parameter.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::InlineVec;
    /// let array = [1, 2, 3];
    /// let inline = InlineVec::<u8, 7>::from_array(array);
    /// assert_eq!(inline.as_slice(), array);
    ///
    /// let array = [Box::new(42)];
    /// let inline = InlineVec::<Box<u8>, 1>::from_array(array);
    /// assert_eq!(inline.len(), 1);
    /// assert_eq!(*inline[0], 42);
    /// ```
    #[inline]
    pub const fn from_array<const N: usize>(array: [T; N]) -> Self {
        let mut this = Self::new();
        this.extend_from_array(array);
        this
    }

    /// Returns the length of the inline vector.
    #[inline]
    pub const fn len(&self) -> usize {
        self.len.get()
    }

    /// Returns a slice of the inline vector.
    #[inline]
    pub const fn as_slice(&self) -> &[T] {
        unsafe { slice::from_raw_parts(self.data.as_ptr().cast(), self.len()) }
    }

    /// Returns a mutable slice of the inline vector.
    #[inline]
    pub const fn as_mut_slice(&mut self) -> &mut [T] {
        unsafe { slice::from_raw_parts_mut(self.data.as_mut_ptr().cast(), self.len()) }
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
    /// let inline = InlineVec::<u8, 7>::new();
    /// assert_eq!(inline.capacity(), 7);
    /// ```
    #[inline]
    pub const fn capacity(&self) -> usize {
        CAP
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
    /// let mut inline = InlineVec::<u8, 7>::new();
    /// inline.push(1);
    /// assert_eq!(inline.len(), 1);
    /// assert_eq!(unsafe { inline.as_ptr().read() }, 1);
    /// ```
    #[inline]
    pub const fn as_ptr(&self) -> *const T {
        self.data.as_ptr().cast()
    }

    /// Returns a `NonNull` pointer to the inline vector data.
    ///
    /// The caller must ensure that the vector outlives the pointer this
    /// function returns, or else it will end up dangling. Moving the vector
    /// would also make any pointers to it invalid.
    #[inline]
    pub const fn as_non_null(&mut self) -> NonNull<T> {
        unsafe { NonNull::new_unchecked(self.data.as_mut_ptr().cast()) }
    }

    /// Returns a mutable pointer to the inline vector.
    ///
    /// The caller must ensure that the vector outlives the pointer this
    /// function returns, or else it will end up dangling. Moving the vector
    /// would also make any pointers to it invalid.
    #[inline]
    pub const fn as_mut_ptr(&mut self) -> *mut T {
        self.data.as_mut_ptr().cast()
    }

    /// Attempts to push a value into the inline vector.
    ///
    /// # Errors
    ///
    /// Returns `Err(value)` if the inline vector is full, that is, the current
    /// [`len`] is greater than the `CAP`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::inline_vec;
    /// let mut inline = inline_vec![3 => 1, 2];
    /// assert_eq!(inline.try_push(1), Ok(()));
    /// assert_eq!(inline.try_push(2), Err(2));
    /// ```
    ///
    /// [`len`]: Self::len
    #[inline]
    pub const fn try_push(&mut self, value: T) -> Result<(), T> {
        let len = self.len();
        if len < CAP {
            self.data[len].write(value);
            unsafe {
                self.set_len(len + 1);
            }
            Ok(())
        } else {
            // If the inline vector is full, we need to return an error.
            // We can use a `Result` to indicate success or failure.
            Err(value)
        }
    }

    /// Appends a value to the back of the inline vector.
    ///
    /// # Panics
    ///
    /// Panics if the inline vector is full, that is, the current [`len`] is
    /// greater than `CAP`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::InlineVec;
    /// let mut inline = InlineVec::<u8, 7>::new();
    /// inline.push(1);
    /// assert_eq!(inline.len(), 1);
    /// assert_eq!(inline.as_slice(), &[1]);
    /// ```
    ///
    /// [`len`]: Self::len
    #[inline]
    #[track_caller]
    pub fn push(&mut self, value: T) {
        if self.try_push(value).is_err() {
            panic!("inline vector is full");
        }
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
    /// let mut inline = InlineVec::<u8, 7>::new();
    /// inline.spare_capacity_mut()[0].write(1);
    /// unsafe {
    ///     inline.set_len(1);
    /// }
    /// ```
    ///
    /// [`spare_capacity_mut`]: Self::spare_capacity_mut
    #[inline]
    pub const unsafe fn set_len(&mut self, new_len: usize) {
        debug_assert!(new_len <= CAP);
        self.len = TaggedU8::new(new_len);
    }

    /// Returns a mutable slice of the spare capacity of the inline vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::InlineVec;
    /// let mut inline = InlineVec::<u8, 7>::new();
    /// assert_eq!(inline.spare_capacity_mut().len(), 7);
    /// inline.spare_capacity_mut()[0].write(5);
    /// unsafe {
    ///     inline.set_len(1);
    /// }
    /// ```
    pub fn spare_capacity_mut(&mut self) -> &mut [MaybeUninit<T>] {
        let len = self.len();
        assert!(len <= CAP);
        unsafe { slice::from_raw_parts_mut(self.data.as_mut_ptr().add(len), CAP - len) }
    }

    /// Removes the last element from the inline vector and returns it, or `None`
    /// if the array is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::InlineVec;
    /// let mut inline = InlineVec::<u8, 7>::new();
    /// inline.push(1);
    /// assert_eq!(inline.pop(), Some(1));
    /// assert_eq!(inline.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        let len = self.len.get();
        if len == 0 {
            None
        } else {
            let value = unsafe { self.data[len - 1].assume_init_read() };
            self.len = TaggedU8::new(len - 1);
            Some(value)
        }
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
    /// let mut inline = inline_vec![7 => 1_u8, 2, 3, 4];
    /// assert_eq!(inline.pop_if(|x| *x % 2 == 0), Some(4));
    /// assert_eq!(inline.as_slice(), &[1, 2, 3]);
    /// assert_eq!(inline.pop_if(|x| *x % 2 == 0), None);
    /// ```
    pub fn pop_if(&mut self, predicate: impl FnOnce(&mut T) -> bool) -> Option<T> {
        let last = self.last_mut()?;

        if predicate(last) {
            self.pop()
        } else {
            None
        }
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
    /// let mut inline1 = inline_vec![7 => 1_u8, 2];
    /// let mut inline2 = inline_vec![7 => 3_u8, 4];
    /// inline1.append(&mut inline2);
    /// assert_eq!(inline1, [1, 2, 3, 4]);
    /// assert_eq!(inline2.len(), 0);
    /// ```
    pub const fn append(&mut self, other: &mut Self) {
        let len = self.len();
        let other_len = other.len();
        assert!(len + other_len <= CAP, "new length exceeds capacity");
        unsafe {
            self.data
                .as_mut_ptr()
                .add(len)
                .copy_from_nonoverlapping(other.data.as_ptr(), other_len);
            other.set_len(0);
            self.set_len(len + other_len);
        }
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
    /// let mut inline = inline_vec![7 => 1_u8, 2];
    /// let mut v = vec![3, 4, 5];
    /// inline.append_vec(&mut v);
    /// assert_eq!(inline, [1, 2, 3, 4, 5]);
    /// assert_eq!(v.len(), 0);
    /// ```
    pub fn append_vec(&mut self, other: &mut Vec<T>) {
        let len = self.len();
        let other_len = other.len();
        assert!(len + other_len <= CAP, "new length exceeds capacity");
        unsafe {
            self.data
                .as_mut_ptr()
                .add(len)
                .copy_from_nonoverlapping(other.as_ptr().cast(), other_len);
            other.set_len(0);
            self.set_len(len + other_len);
        }
    }

    /// Clears the inline vector, removing all elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::InlineVec;
    /// let mut inline = InlineVec::<u8, 7>::new();
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
    /// let mut inline = InlineVec::<u8, 7>::new();
    /// inline.push(1);
    /// inline.push(2);
    /// assert_eq!(inline.len(), 2);
    /// inline.truncate(1);
    /// assert_eq!(inline.len(), 1);
    /// inline.truncate(0);
    /// assert_eq!(inline.len(), 0);
    /// ```
    pub fn truncate(&mut self, new_len: usize) {
        let old_len = self.len();
        if new_len < old_len {
            self.len = TaggedU8::new(new_len);
            for i in new_len..old_len {
                unsafe { self.data[i].assume_init_drop() };
            }
        }
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
    /// let mut inline = InlineVec::<u8, 7>::new();
    /// inline.push(1);
    /// inline.push(2);
    /// inline.push(3);
    /// assert_eq!(inline.swap_remove(1), 2);
    /// assert_eq!(inline.as_slice(), &[1, 3]);
    /// ```
    pub const fn swap_remove(&mut self, index: usize) -> T {
        let len = self.len();
        assert!(index < len, "index out of bounds");
        self.data.swap(index, len - 1);

        // SAFETY: reduce the length of the vector
        unsafe {
            self.set_len(len - 1);
        }

        // SAFETY: initialized due to previous type invariant
        unsafe { self.data[len - 1].assume_init_read() }
    }

    /// Inserts an element at the specified index, shifting all elements after
    /// it to the right.
    ///
    /// # Panics
    ///
    /// Panics if either:
    /// - `index` is out of bounds, i.e., strictly greater than [`len`]
    /// - the inline vector is full, i.e., [`len`] is already equal to `CAP`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::InlineVec;
    /// let mut inline = InlineVec::<u8, 7>::new();
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
    /// let mut inline = InlineVec::<u8, 3>::new();
    /// inline.try_insert(0, 1).unwrap();
    /// inline.try_insert(1, 2).unwrap();
    /// inline.try_insert(4, 3).unwrap_err(); // out of bounds
    /// inline.try_insert(0, 0).unwrap();
    /// inline.try_insert(3, 4).unwrap_err(); // full
    /// ```
    ///
    /// [`len`]: Self::len
    pub const fn try_insert(&mut self, index: usize, value: T) -> Result<(), InsertError<T>> {
        let len = self.len();
        if index > len {
            return Err(InsertError::new(value, InsertErrorKind::OutOfBounds));
        } else if len == CAP {
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
    /// let mut inline = InlineVec::<u8, 7>::new();
    /// inline.push(1);
    /// inline.push(2);
    /// inline.push(3);
    /// assert_eq!(inline.remove(1), 2);
    /// assert_eq!(inline.as_slice(), &[1, 3]);
    /// ```
    #[track_caller]
    pub const fn remove(&mut self, index: usize) -> T {
        let len = self.len();

        assert!(index < len, "index out of bounds");

        // SAFETY: index checked above
        unsafe { self.remove_unchecked(index) }
    }

    /// Removes and returns the element at the specified index, shifting all
    /// elements after it to the left.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `index` is less than the current length of
    /// the inline vector.
    pub const unsafe fn remove_unchecked(&mut self, index: usize) -> T {
        let len = self.len();

        // SAFETY:
        // - index checked above
        // - type invariant ensures that the element is initialized
        // - the length is decremented after the element is removed
        unsafe {
            let ptr = self.data.as_mut_ptr().add(index);
            let value = (*ptr).assume_init_read();
            ptr.copy_from(ptr.add(1), len - index - 1);
            self.set_len(len - 1);
            value
        }
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
    /// let mut inline = InlineVec::<u8, 7>::new();
    /// inline.push(1);
    /// inline.push(2);
    /// inline.push(3);
    /// let other = inline.split_off(1);
    /// assert_eq!(inline.as_slice(), &[1]);
    /// assert_eq!(other.as_slice(), &[2, 3]);
    /// ```
    pub fn split_off(&mut self, at: usize) -> Self {
        assert!(at <= self.len(), "index out of bounds");

        let mut other = Self::new();
        let len = self.len();

        let remainder = len - at;
        unsafe {
            self.set_len(at);
            let ptr = self.data.as_ptr().add(at);
            other
                .data
                .as_mut_ptr()
                .copy_from_nonoverlapping(ptr, remainder);
            other.set_len(remainder);
        }
        other
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
    /// let mut inline = InlineVec::<u8, 7>::new();
    /// inline.resize_with(3, || 42);
    /// assert_eq!(inline.as_slice(), &[42, 42, 42]);
    /// inline.resize_with(1, || 0);
    /// assert_eq!(inline.as_slice(), &[42]);
    /// ```
    pub fn resize_with<F>(&mut self, new_len: usize, mut f: F)
    where
        F: FnMut() -> T,
    {
        let len = self.len();
        if new_len > len {
            assert!(new_len <= CAP, "new length exceeds capacity");
            for i in len..new_len {
                self.data[i].write(f());
                unsafe {
                    self.set_len(i + 1);
                }
            }
        } else {
            self.truncate(new_len);
        }
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
    /// let mut inline = inline_vec![7 => 1, 2];
    /// inline.extend_from_array([3, 4]);
    /// assert_eq!(inline.as_slice(), &[1, 2, 3, 4]);
    /// ```
    #[doc(alias = "push_array")]
    #[track_caller]
    pub const fn extend_from_array<const N: usize>(&mut self, array: [T; N]) {
        const {
            assert!(N <= CAP, "array larger than capacity");
        }
        let len = self.len();
        let new_len = len + N;
        assert!(new_len <= CAP, "new length exceeds capacity");
        unsafe {
            self.set_len(new_len);
            self.as_mut_ptr()
                .add(len)
                .copy_from_nonoverlapping(array.as_ptr().cast(), N);
        }
        core::mem::forget(array);
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
    /// Panics if the starting point is greater than the end point or if
    /// the end point is greater than the length of the vector.
    ///
    /// # Leaking
    ///
    /// If the returned iterator goes out of scope without being dropped (due to
    /// [`mem::forget`], for example), the vector may have lost and leaked
    /// elements arbitrarily, including elements outside the range.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::vecs::InlineVec;
    /// # use hipstr::inline_vec;
    /// let mut v: InlineVec<u8, 7> = inline_vec![1, 2, 3];
    /// let u: InlineVec<u8, 7> = v.drain(1..).collect();
    /// assert_eq!(v, &[1]);
    /// assert_eq!(u, &[2, 3]);
    ///
    /// // A full range clears the vector, like `clear()` does
    /// v.drain(..);
    /// assert_eq!(v, &[]);
    /// ```
    pub fn drain(&mut self, range: impl RangeBounds<usize>) -> Drain<T, CAP, SHIFT, TAG> {
        let range = common::range(range, self.len()).unwrap_or_else(|err| {
            panic!("{err}");
        });
        self.drain_range(range)
    }

    fn drain_range(&mut self, range: Range<usize>) -> Drain<T, CAP, SHIFT, TAG> {
        debug_assert!(range.start <= range.end);

        let old_len = self.len();
        unsafe {
            self.set_len(range.start);
            Drain {
                old_len,
                full: range.clone(),
                current: range,
                vec: self,
            }
        }
    }
}

impl<T, const CAP: usize, const SHIFT: u8, const TAG: u8> InlineVec<T, CAP, SHIFT, TAG>
where
    T: Clone,
{
    /// Creates a new inline vector from a slice by cloning the element.
    ///
    /// # Panics
    ///
    /// Panics if the length of the slice exceeds the capacity of the inline
    /// vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::InlineVec;
    /// let array = [Box::new(1), Box::new(2), Box::new(3)];
    /// let inline = InlineVec::<Box<u8>, 7>::from_slice_clone(&array);
    /// assert_eq!(inline.as_slice(), &array);
    /// ```
    #[inline]
    pub fn from_slice_clone(slice: &[T]) -> Self {
        let mut this = Self::new();
        this.extend_from_slice(slice);
        this
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
    /// let mut inline = inline_vec![7 => 1, 2];
    /// inline.extend_from_slice_copy(&[3, 4]);
    /// assert_eq!(inline.as_slice(), &[1, 2, 3, 4]);
    /// ```
    ///
    /// [`extend_from_slice_copy`]: Self::extend_from_slice_copy
    #[doc(alias = "push_slice_clone")]
    #[track_caller]
    pub fn extend_from_slice(&mut self, slice: &[T]) {
        let len = self.len();
        let new_len = len + slice.len();
        assert!(new_len <= CAP, "new length exceeds capacity");

        let dst = self.data[len..new_len].iter_mut();
        let src = slice.iter();
        for ((dst, src), l) in dst.zip(src).zip(len + 1..=new_len) {
            dst.write(src.clone());
            self.len = TaggedU8::new(l);
        }
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
    /// let mut characters = inline_vec![10 => 'a', 'b', 'c', 'd', 'e'];
    /// characters.extend_from_within(2..);
    /// assert_eq!(characters, ['a', 'b', 'c', 'd', 'e', 'c', 'd', 'e']);
    ///
    /// let mut numbers = inline_vec![7 => 0_u8, 1, 2, 3, 4];
    /// numbers.extend_from_within(..2);
    /// assert_eq!(numbers, [0, 1, 2, 3, 4, 0, 1]);
    ///
    /// let mut strings = inline_vec![6 => String::from("hello"), String::from("world"), String::from("!")];
    /// strings.extend_from_within(1..=2);
    /// assert_eq!(strings, ["hello", "world", "!", "world", "!"]);
    /// ```
    #[track_caller]
    pub fn extend_from_within(&mut self, range: impl RangeBounds<usize>) {
        let range = common::range(range, self.len()).unwrap_or_else(|err| {
            panic!("{err}");
        });
        self.extend_from_within_range(range);
    }

    fn extend_from_within_range(&mut self, range: Range<usize>) {
        let len = self.len();
        let range_len = range.len();
        let new_len = len + range_len;
        assert!(new_len <= CAP, "new length exceeds capacity");

        let (current, spare) = unsafe { self.data.split_at_mut_unchecked(len) };
        let dst = spare[0..range_len].iter_mut();
        let src = current[range].iter();
        for ((dst, src), l) in dst.zip(src).zip(len + 1..=new_len) {
            // SAFETY: the source is in the initialized range
            dst.write(unsafe { src.assume_init_ref() }.clone());
            self.len = TaggedU8::new(l);
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
    /// let mut inline = InlineVec::<u8, 7>::new();
    /// inline.resize(3, 42);
    /// assert_eq!(inline.as_slice(), &[42, 42, 42]);
    /// inline.resize(1, 0);
    /// assert_eq!(inline.as_slice(), &[42]);
    /// ```
    pub fn resize(&mut self, new_len: usize, value: T) {
        self.resize_with(new_len, || value.clone());
    }
}

impl<T, const CAP: usize, const SHIFT: u8, const TAG: u8> InlineVec<T, CAP, SHIFT, TAG>
where
    T: Copy,
{
    /// Creates a new inline vector from a slice by copying the element.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::InlineVec;
    /// let array = [1, 2, 3];
    /// let inline = InlineVec::<u8, 7>::from_slice_copy(&array);
    /// assert_eq!(inline.as_slice(), array);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the length of the slice exceeds the capacity of the inline
    /// vector.
    pub const fn from_slice_copy(slice: &[T]) -> Self {
        let mut this = Self::new();
        this.extend_from_slice_copy(slice);
        this
    }

    /// Creates a new inline vector from a slice by copying the element.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::InlineVec;
    /// let array = [1, 2, 3];
    /// let inline = InlineVec::<u8, 7>::from_slice_copy(&array);
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
    /// let mut inline = inline_vec![7 => 1, 2];
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
        assert!(new_len <= CAP, "new length exceeds capacity");
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
        unsafe {
            self.set_len(new_len);
            self.data
                .as_mut_ptr()
                .add(len)
                .copy_from_nonoverlapping(slice.as_ptr().cast(), slice.len());
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
    /// let inline = InlineVec::<u8, 7>::from_slice_copy(&[1, 2, 3]);
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
    /// let mut characters = inline_vec![10 => 'a', 'b', 'c', 'd', 'e'];
    /// characters.extend_from_within_copy(2..);
    /// assert_eq!(characters, ['a', 'b', 'c', 'd', 'e', 'c', 'd', 'e']);
    ///
    /// let mut numbers = inline_vec![7 => 0_u8, 1, 2, 3, 4];
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
        assert!(new_len <= CAP, "new length exceeds capacity");

        // SAFETY: the range is valid and the source elements are initialized
        let (current, spare) = unsafe { self.data.split_at_mut_unchecked(len) };

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

impl<T, const CAP: usize, const SHIFT: u8, const TAG: u8> Clone for InlineVec<T, CAP, SHIFT, TAG>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        Self::from_slice_clone(self.as_slice())
    }
}

impl<T, const CAP: usize, const SHIFT: u8, const TAG: u8> Drop for InlineVec<T, CAP, SHIFT, TAG> {
    fn drop(&mut self) {
        if core::mem::needs_drop::<T>() {
            let len = self.len();
            for i in 0..len {
                unsafe { self.data[i].assume_init_drop() };
            }
        }
    }
}

impl<T, const CAP: usize, const SHIFT: u8, const TAG: u8> Deref for InlineVec<T, CAP, SHIFT, TAG> {
    type Target = [T];

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<T, const CAP: usize, const SHIFT: u8, const TAG: u8> DerefMut
    for InlineVec<T, CAP, SHIFT, TAG>
{
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut_slice()
    }
}

impl<T, const CAP: usize, const SHIFT: u8, const TAG: u8> AsRef<[T]>
    for InlineVec<T, CAP, SHIFT, TAG>
{
    #[inline]
    fn as_ref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T, const CAP: usize, const SHIFT: u8, const TAG: u8> AsMut<[T]>
    for InlineVec<T, CAP, SHIFT, TAG>
{
    #[inline]
    fn as_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}

impl<T: fmt::Debug, const CAP: usize, const SHIFT: u8, const TAG: u8> fmt::Debug
    for InlineVec<T, CAP, SHIFT, TAG>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_slice().fmt(f)
    }
}

impl<T: hash::Hash, const CAP: usize, const SHIFT: u8, const TAG: u8> hash::Hash
    for InlineVec<T, CAP, SHIFT, TAG>
{
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.as_slice().hash(state);
    }
}

impl<T, const CAP: usize, const SHIFT: u8, const TAG: u8> FromIterator<T>
    for InlineVec<T, CAP, SHIFT, TAG>
{
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        // May be improve by specialization if Rust offers it one day. Is it
        // worth it for such small sized vectors?
        //
        // Also if one day, Rust can collect into an array (and specialized it),
        // we can use that to collect directly into the inline vector

        let iter = iter.into_iter();
        let mut this = Self::new();
        for item in iter {
            this.push(item);
        }
        this
    }
}

impl<T, const CAP: usize, const SHIFT: u8, const TAG: u8> Extend<T>
    for InlineVec<T, CAP, SHIFT, TAG>
{
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        // May be improve by specialization if Rust offers it one day. Is it
        // worth it for such small sized vectors?
        let iter = iter.into_iter();
        for item in iter {
            self.push(item);
        }
    }
}

impl<T, const CAP: usize, const SHIFT: u8, const TAG: u8> IntoIterator
    for InlineVec<T, CAP, SHIFT, TAG>
{
    type Item = T;
    type IntoIter = IntoIter<T, CAP, SHIFT, TAG>;

    fn into_iter(self) -> Self::IntoIter {
        let end = self.len();
        let vec = ManuallyDrop::new(self);
        IntoIter { start: 0, end, vec }
    }
}

pub struct IntoIter<T, const CAP: usize, const SHIFT: u8, const TAG: u8> {
    start: usize,
    end: usize,
    vec: ManuallyDrop<InlineVec<T, CAP, SHIFT, TAG>>,
}

impl<T, const CAP: usize, const SHIFT: u8, const TAG: u8> Iterator
    for IntoIter<T, CAP, SHIFT, TAG>
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.start < self.end {
            let value = unsafe { self.vec.data[self.start].assume_init_read() };
            self.start += 1;
            Some(value)
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.end - self.start;
        (len, Some(len))
    }
}

impl<T, const CAP: usize, const SHIFT: u8, const TAG: u8> ExactSizeIterator
    for IntoIter<T, CAP, SHIFT, TAG>
{
    fn len(&self) -> usize {
        self.end - self.start
    }
}

impl<T, const CAP: usize, const SHIFT: u8, const TAG: u8> Drop for IntoIter<T, CAP, SHIFT, TAG> {
    fn drop(&mut self) {
        if core::mem::needs_drop::<T>() {
            for i in self.start..self.end {
                unsafe { self.vec.data[i].assume_init_drop() };
            }
        }
    }
}

impl<T, const CAP: usize, const SHIFT: u8, const TAG: u8> DoubleEndedIterator
    for IntoIter<T, CAP, SHIFT, TAG>
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.start < self.end {
            self.end -= 1;
            let value = unsafe { self.vec.data[self.end].assume_init_read() };
            Some(value)
        } else {
            None
        }
    }
}

impl<T, const CAP: usize, const SHIFT: u8, const TAG: u8> FusedIterator
    for IntoIter<T, CAP, SHIFT, TAG>
{
}

impl<T: Eq, const CAP: usize, const SHIFT: u8, const TAG: u8> Eq for InlineVec<T, CAP, SHIFT, TAG> {}

impl<
        T: PartialEq,
        const CAP1: usize,
        const SHIFT1: u8,
        const TAG1: u8,
        const CAP2: usize,
        const SHIFT2: u8,
        const TAG2: u8,
    > PartialEq<InlineVec<T, CAP1, SHIFT1, TAG1>> for InlineVec<T, CAP2, SHIFT2, TAG2>
{
    fn eq(&self, other: &InlineVec<T, CAP1, SHIFT1, TAG1>) -> bool {
        self.as_slice().eq(other.as_slice())
    }
}

macros::partial_eq! {
    [T, U, const CAP: usize, const SHIFT: u8, const TAG: u8]
    where [T: PartialEq<U>]
    {
        ([T], InlineVec<U, CAP, SHIFT, TAG>);
        (InlineVec<T, CAP, SHIFT, TAG>, [U]);

        (&[T], InlineVec<U, CAP, SHIFT, TAG>);
        (InlineVec<T, CAP, SHIFT, TAG>, &[U]);

        (&mut [T], InlineVec<U, CAP, SHIFT, TAG>);
        (InlineVec<T, CAP, SHIFT, TAG>, &mut [U]);

        (Vec<T>, InlineVec<U, CAP, SHIFT, TAG>);
        (InlineVec<T, CAP, SHIFT, TAG>, Vec<U>);

    }

    [T, U, const CAP: usize, const SHIFT: u8, const TAG: u8]
    where [T: PartialEq<U>, T: Clone]
    (alloc::borrow::Cow<'_, [T]>, InlineVec<U, CAP, SHIFT, TAG>);

    [T, U, const CAP: usize, const SHIFT: u8, const TAG: u8]
    where [T: PartialEq<U>, U: Clone]
    (InlineVec<T, CAP, SHIFT, TAG>, alloc::borrow::Cow<'_, [U]>);

    [T, U, const CAP: usize, const SHIFT: u8, const TAG: u8, const N: usize]
    where [T: PartialEq<U>]
    {
        ([T; N], InlineVec<U, CAP, SHIFT, TAG>);
        (InlineVec<T, CAP, SHIFT, TAG>, [U; N]);

        (&[T; N], InlineVec<U, CAP, SHIFT, TAG>);
        (InlineVec<T, CAP, SHIFT, TAG>, &[U; N]);

        (&mut [T; N], InlineVec<U, CAP, SHIFT, TAG>);
        (InlineVec<T, CAP, SHIFT, TAG>, &mut [U; N]);
    }
}

impl<
        T: PartialOrd,
        const CAP1: usize,
        const SHIFT1: u8,
        const TAG1: u8,
        const CAP2: usize,
        const SHIFT2: u8,
        const TAG2: u8,
    > PartialOrd<InlineVec<T, CAP1, SHIFT1, TAG1>> for InlineVec<T, CAP2, SHIFT2, TAG2>
{
    fn partial_cmp(&self, other: &InlineVec<T, CAP1, SHIFT1, TAG1>) -> Option<core::cmp::Ordering> {
        self.as_slice().partial_cmp(other.as_slice())
    }
}

impl<T: Ord, const CAP: usize, const SHIFT: u8, const TAG: u8> Ord
    for InlineVec<T, CAP, SHIFT, TAG>
{
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
/// The inlive vector's fixed capacity is either explicity specified or
/// inferred by the compiler.
///
/// They are multiple forms of this macros:
///
/// - Creates an inline vector with the given elements and a specified capacity:
///
///   ```
///   # use hipstr::inline_vec;
///   let v1 = inline_vec![7 => 1_u8, 2, 3];
///   assert_eq!(v1, [1, 2, 3]);
///   ```
///
/// - Creates an inline vector with the given elements and an inferred capacity:
///
///   ```
///   # use hipstr::inline_vec;
///   # use hipstr::vecs::InlineVec;
///   let v2: InlineVec<u8, 7> = inline_vec![1, 2, 3];
///   assert_eq!(v2, [1, 2, 3]);
///   ```
///
/// - Creates an inline vector from a given element and size with a specified
///   capacity:
///
///   ```
///   # use hipstr::inline_vec;
///   let v3 = inline_vec![7 => 0; 7];
///   assert_eq!(v3, [0, 0, 0, 0, 0, 0, 0]);
///   ```
///
/// - Creates an inline vector from a given element and size with an inferred
///   capacity:
///
///   ```
///   # use hipstr::inline_vec;
///   # use hipstr::vecs::InlineVec;
///   let v4: InlineVec<u8, 7> = inline_vec![0; 7];
///   assert_eq!(v4, [0, 0, 0, 0, 0, 0, 0]);
///   ```
///
/// This macro is a convenience wrapper around [`InlineVec::from_array`].
#[macro_export]
macro_rules! inline_vec {
    [$cap:expr => $($e:expr),* $(,)?] => {
        {
            $crate::vecs::InlineVec::<_, { $cap }>::from_array([$($e),*])
        }
    };
    [$($e:expr),* $(,)?] => {
        {
            $crate::vecs::InlineVec::from_array([$($e),*])
        }
    };
    [$cap:expr => $e:expr; $n:expr] => {
        {
            $crate::vecs::InlineVec::<_, { $cap }>::from_array([$e; $n])
        }
    };
    [$e:expr; $n:expr] => {
        {
            $crate::vecs::InlineVec::from_array([$e; $n])
        }
    };
}

pub struct Drain<'a, T, const CAP: usize, const SHIFT: u8, const TAG: u8> {
    /// Full range
    full: Range<usize>,
    /// Current range
    current: Range<usize>,
    old_len: usize,
    vec: &'a mut InlineVec<T, CAP, SHIFT, TAG>,
}

impl<T, const CAP: usize, const SHIFT: u8, const TAG: u8> Drop for Drain<'_, T, CAP, SHIFT, TAG> {
    fn drop(&mut self) {
        if core::mem::needs_drop::<T>() {
            for i in &mut self.current {
                unsafe { self.vec.data[i].assume_init_drop() };
            }
        }

        let start = self.full.start;
        let end = self.full.end;
        let old_len = self.old_len;
        let ptr = self.vec.data.as_mut_ptr();

        unsafe {
            // move the suffix, overwriting the drained range
            ptr.add(start).copy_from(ptr.add(end), old_len - end);
            // set the new length
            self.vec.set_len(old_len - (end - start));
        }
    }
}

impl<T, const CAP: usize, const SHIFT: u8, const TAG: u8> Iterator
    for Drain<'_, T, CAP, SHIFT, TAG>
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        let index = self.current.next()?;
        let value = unsafe { self.vec.data.get_unchecked(index).assume_init_read() };
        Some(value)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.current.size_hint()
    }
}

impl<T, const CAP: usize, const SHIFT: u8, const TAG: u8> DoubleEndedIterator
    for Drain<'_, T, CAP, SHIFT, TAG>
{
    fn next_back(&mut self) -> Option<Self::Item> {
        let index = self.current.next_back()?;
        let value = unsafe { self.vec.data.get_unchecked(index).assume_init_read() };
        Some(value)
    }
}

impl<T, const CAP: usize, const SHIFT: u8, const TAG: u8> FusedIterator
    for Drain<'_, T, CAP, SHIFT, TAG>
{
}

impl<T, const CAP: usize, const SHIFT: u8, const TAG: u8> ExactSizeIterator
    for Drain<'_, T, CAP, SHIFT, TAG>
{
    fn len(&self) -> usize {
        self.current.len()
    }
}
