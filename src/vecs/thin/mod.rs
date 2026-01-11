//! Thin vectors and related types.
//!
//! This module provides two main types:
//! - [`ThinVec`], which is the thin vector itself,
//! - [`SmartThinVec`], which is a smart pointer to a [`ThinVec`].
//!
//! # [`ThinVec`]
//!
//! A thin vector [`ThinVec`] is a contiguous growable array type with
//! heap-allocated metadata (prefix, capacity, length) and contents. The prefix
//! is an arbitrary data associated with the vector to support the reference
//! counted vector type.
//!
//! Whereas [`Vec`] is three-word wide, this vector is one-word wide. It
//! consists in a single pointer to a heap-allocated area containing both the
//! capacity, the length, and the actual data.
//!
//! With respect to [`WideVec`], the thin vector offers more efficient access to
//! the data but cannot be obtained from [`Vec`] without copy.
//!
//! [`WideVec`]: crate::vecs::wide::WideVec
//!
//! # [`SmartThinVec`]
//!
//! The smart vector [`SmartThinVec`] that can be either unique or shared
//! (reference counted, atomically or not), with possible copy-on-write
//! semantics. Like [`ThinVec`], [`SmartThinVec`] is *thin*, i.e., the handle
//! is one pointer wide.
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

use alloc::alloc::{alloc, dealloc, realloc, Layout};
use alloc::borrow::Cow;
use alloc::boxed::Box;
use alloc::vec::Vec;
use core::borrow::BorrowMut;
use core::mem::{offset_of, ManuallyDrop, MaybeUninit};
use core::ops::{Range, RangeBounds};
use core::ptr::NonNull;
use core::{cmp, iter, mem, ptr, slice};

use const_default::ConstDefault;
use rules_derive::rules_derive;

use self::repr::{ThinHeader, ThinRepr};
use crate::backend::{BackendImpl, CloneOnOverflow, Counter, PanicOnOverflow, UpdateResult};
use crate::common::derives::{
    AsRef, Borrow, ConstDefault, DelegateDebug, DelegateHash, Deref, From, FromIterator,
    IntoIterator, MutVector, Vector,
};
use crate::common::drain::Drain;
use crate::common::into_iter::IntoIter;
use crate::common::methods::{
    append_impl, extend_from_array_impl, extend_from_slice_impl, from_array_impl,
    from_slice_clone_impl, insert_impl, pop_if_impl, pop_impl, push_within_capacity,
    remove_unchecked_impl, resize_impl, spare_capacity_mut_impl, split_off_impl, swap_remove_impl,
    truncate_impl,
};
use crate::common::traits::{MutVector, Mutate, Vector};
use crate::common::{
    check_alloc, drop_raw_slice, maybe_uninit_write_copy_of_slice, unwrap_display, RangeError,
    ZeroUsize,
};
use crate::macros::trait_impls;
use crate::{common, macros, Backend};

pub(crate) mod repr;

#[cfg(test)]
mod shared_tests;
#[cfg(test)]
mod unique_tests;

/// A reserved prefix type for thin vectors that do not need a prefix but can be
/// easily converted to shared thin vectors.
pub type Reserved = ZeroUsize;

/// A macro to create a [`ThinVec`] with the given elements.
///
/// # Examples
///
/// ```
/// use hipstr::thin_vec;
/// let v = thin_vec![1, 2, 3];
/// assert_eq!(v, [1, 2, 3]);
///
/// let v = thin_vec![1; 5];
/// assert_eq!(v, [1, 1, 1, 1, 1]);
/// ```
#[macro_export]
macro_rules! thin_vec {
    [] => {
        $crate::vecs::ThinVec::new()
    };
    [ $e:expr ; $l:expr ] => {{
        let len = $l;
        let mut vec = $crate::vecs::ThinVec::with_capacity(len);
        vec.resize(len, $e);
        vec
    }};
    [ $($e:expr),+ $(,)? ] => {{
        let cap = $crate::thin_vec!(@count $( ($e) )+);
        let mut vec = $crate::vecs::ThinVec::with_capacity(cap);
        $(
            vec.push($e);
        )+
        vec
    }};

    (@count) => {
        0
    };
    (@count $( $a:tt $b:tt )*) => {
        $crate::thin_vec!(@count $( $a )* ) << 1
    };
    (@count $_odd:tt $( $a:tt $_b:tt )*) => {
        ($crate::thin_vec!(@count $( $a )* ) << 1) | 1
    };
}

/// A thin vector, that is, a contiguous growable array type with heap-allocated
/// metadata (prefix, capacity, length) and contents.
///
/// Whereas [`Vec`] is three-word wide, this vector is one-word wide. It
/// consists in a single pointer to a heap-allocated area containing both the
/// capacity, the length, and the actual data.
///
/// The prefix of `ThinVec` is an arbitrary associated data of type `P`.
///
/// [`Vec`]: alloc::vec::Vec
#[repr(transparent)]
#[rules_derive(
    MutVector(T),
    ConstDefault(Self(ThinRepr::NULL)),
    // Delegated traits: debug and hash
    DelegateDebug(Self::as_slice where T: core::fmt::Debug),
    DelegateHash(Self::as_slice where T: core::hash::Hash),
    // AsRef, Deref, Borrow
    AsRef([T], Self::as_slice, Self::as_mut_slice),
    Deref([T], Self::as_slice, Self::as_mut_slice),
    Borrow([T], Self::as_slice, Self::as_mut_slice),
    // Iterators
    IntoIterator(T, IntoIter<Self>, IntoIter::new),
    FromIterator(T, Self::from_iter),
    // From conversions
    From(Vec<T>, Self::from_vector),
    From(Box<[T]>, Self::from_boxed_slice),
    From([T; N], Self::from_array, (const N: usize)),
    From(&[T], Self::from_slice_clone, () where (T: Clone)),
    From(&mut [T], Self::from_slice_clone, () where (T: Clone)),
    From(&[T; N], Self::from_slice_clone, (const N: usize) where (T: Clone)),
    From(&mut [T;N], Self::from_slice_clone, (const N: usize) where (T: Clone)),
)]
pub struct ThinVec<T, P: ConstDefault = Reserved>(pub(super) ThinRepr<T, P>);

impl<T, P: ConstDefault> ThinVec<T, P> {
    const MINIMAL_CAPACITY: usize = minimal_capacity::<T, P>();

    #[inline]
    const fn ptr(&self) -> NonNull<T> {
        self.0.data()
    }

    /// Creates a new empty thin vector.
    ///
    /// This method does not allocate any memory.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::ThinVec;
    /// let vec: ThinVec<i32> = ThinVec::new();
    /// assert!(vec.is_empty());
    /// ```
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self::DEFAULT
    }

    /// Returns the capacity of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::ThinVec;
    /// let vec: ThinVec<i32> = ThinVec::with_capacity(10);
    /// assert!(vec.capacity() >= 10);
    ///
    /// let vec: ThinVec<i32> = ThinVec::new();
    /// assert_eq!(vec.capacity(), 0);
    ///
    /// let vec: ThinVec<()> = ThinVec::with_capacity(1);
    /// assert_eq!(vec.capacity(), usize::MAX);
    /// ```
    #[inline]
    #[must_use]
    pub const fn capacity(&self) -> usize {
        if let Some(header) = self.0.as_ref() {
            header.cap
        } else {
            0
        }
    }

    /// Returns the number of elements in the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::ThinVec;
    /// let mut vec = ThinVec::new();
    /// vec.push(1);
    /// vec.push(2);
    /// assert_eq!(vec.len(), 2);
    /// ```
    #[inline]
    #[must_use]
    pub const fn len(&self) -> usize {
        if let Some(header) = self.0.as_ref() {
            header.len
        } else {
            0
        }
    }

    /// Returns `true` if the vector contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::ThinVec;
    /// let vec: ThinVec<i32> = ThinVec::new();
    /// assert!(vec.is_empty());
    /// ```
    #[inline]
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the current prefix associated with this thin vector.
    ///
    /// If the vector is empty (capacity 0), returns `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::thin::ThinVec;
    /// let vec: ThinVec<i32, u32> = ThinVec::new();
    /// assert!(vec.prefix().is_none());
    ///
    /// let mut vec: ThinVec<i32, u32> = ThinVec::with_capacity(4);
    /// assert!(vec.prefix().is_some());
    /// ```
    #[must_use]
    pub const fn prefix(&self) -> Option<&P> {
        if let Some(header) = self.0.as_ref() {
            Some(&header.prefix)
        } else {
            None
        }
    }

    /// Returns a raw pointer to the vector's first element.
    ///
    /// The caller must ensure that the vector outlives the pointer this
    /// function returns, or else it will end up dangling. Modification of the
    /// vector (e.g. pushing elements) may cause the buffer to be reallocated,
    /// which would also make any pointers to it invalid.
    ///
    /// The caller must also ensure that the memory the pointer
    /// (non-transitively) points to is never written to (except inside an
    /// `UnsafeCell`) using this pointer or any pointer derived from it. If you
    /// need to mutate the contents of the slice, use [`as_mut_ptr`].
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::ThinVec;
    /// let mut vec = ThinVec::new();
    /// vec.push(1);
    /// let ptr = vec.as_ptr();
    /// unsafe {
    ///    assert_eq!(*ptr, 1);
    /// }
    /// ```
    ///
    /// [`as_mut_ptr`]: Self::as_mut_ptr
    #[inline]
    #[must_use]
    pub const fn as_ptr(&self) -> *const T {
        self.ptr().as_ptr()
    }

    /// Returns a raw mutable pointer to the vector's first element.
    ///
    /// The caller must ensure that the vector outlives the pointer this
    /// function returns, or else it will end up dangling. Modifying the vector
    /// may cause its buffer to be reallocated, which would also make any
    /// pointers to it invalid.
    ///
    /// This method guarantees that for the purpose of the aliasing model, this
    /// method does not materialize a reference to the underlying slice, and
    /// thus the returned pointer will remain valid when mixed with other calls
    /// to [`as_ptr`], [`as_mut_ptr`], and [`as_non_null`]. Note that calling
    /// other methods that materialize references to the slice, or references to
    /// specific elements you are planning on accessing through this pointer,
    /// may still invalidate this pointer. See the second example below for how
    /// this guarantee can be used.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::ThinVec;
    /// let mut vec = ThinVec::with_capacity(4);
    /// let ptr: *mut i32 = vec.as_mut_ptr();
    /// unsafe {
    ///     for i in 0..4 {
    ///         ptr.add(i as usize).write(i);
    ///     }
    ///     vec.set_len(4);
    /// }
    /// assert_eq!(vec.as_slice(), [0, 1, 2, 3]);
    /// ```
    ///
    /// [`as_mut_ptr`]: ThinVec::as_mut_ptr
    /// [`as_ptr`]: ThinVec::as_ptr
    /// [`as_non_null`]: ThinVec::as_non_null
    #[inline]
    pub const fn as_mut_ptr(&mut self) -> *mut T {
        self.ptr().as_ptr()
    }

    /// Returns a non-null pointer to the vector's first element.
    ///
    /// The caller must ensure that the vector outlives the pointer this
    /// function returns, or else it will end up dangling. Modification of the
    /// vector (e.g. pushing elements) may cause the buffer to be reallocated,
    /// which would also make any pointers to it invalid.
    #[inline]
    pub const fn as_non_null(&mut self) -> NonNull<T> {
        self.ptr()
    }

    /// Extracts a slice containing the entire vector.
    ///
    /// Equivalent to `&s[..]`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::ThinVec;
    /// let buffer = ThinVec::from_slice_copy(&[1, 2, 3]);
    /// assert_eq!(buffer.as_slice(), &[1, 2, 3]);
    /// ```
    #[inline]
    #[must_use]
    pub const fn as_slice(&self) -> &[T] {
        unsafe { self.as_slice_extended() }
    }

    /// Extracts a slice containing the entire vector.
    ///
    /// This is a more flexible but more dangerous version of [`as_slice`]. It
    /// allows the caller to specify the lifetime of the slice.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the thin vector outlives the slice, and that
    /// no modification of the thin vector occurs that would invalidate the
    /// slice (modification, reallocation, etc.).
    ///
    /// [`as_slice`]: Self::as_slice
    #[inline]
    #[must_use]
    pub const unsafe fn as_slice_extended<'a>(&self) -> &'a [T] {
        let ptr = self.ptr().as_ptr();
        unsafe { slice::from_raw_parts(ptr, self.len()) }
    }

    /// Returns a mutable slice of the vector.
    ///
    /// Equivalent to `&mut s[..]`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::ThinVec;
    /// let mut buffer = ThinVec::from_slice_copy(&[1, 2, 3]);
    /// buffer.as_mut_slice()[1] = 5;
    /// assert_eq!(buffer.as_slice(), &[1, 5, 3]);
    /// ```
    #[inline]
    #[must_use]
    pub const fn as_mut_slice(&mut self) -> &mut [T] {
        unsafe { slice::from_raw_parts_mut(self.as_mut_ptr(), self.len()) }
    }

    /// Gets the current layout.
    const fn current_layout(&self) -> Layout {
        // SAFETY: layout checked at creation
        let (layout, _) = unsafe { ThinHeader::<T, P>::layout(self.capacity()).unwrap_unchecked() };
        layout
    }

    /// Forces the length of the vector to `new_len`.
    ///
    /// This is a low-level operation that does not maintain any of the usual
    /// invariants of the type. Normally changing the length of a vector is done
    /// using one of the safe operations instead.
    ///
    /// # Panics
    ///
    /// When `debug_assertions` is on, panics if `new_len` is greater than the
    /// vector's capacity.
    ///
    /// # Safety
    ///
    /// - `new_len` must be less than or equal to the capacity of the vector.
    /// - The elements at `old_len..new_len` must be initialized.
    pub unsafe fn set_len(&mut self, new_len: usize) {
        if let Some(header) = self.0.as_mut() {
            debug_assert!(new_len <= header.cap, "new length out of bounds");

            // SAFETY: `header` is guaranteed to be valid as long as the vector is valid
            header.len = new_len;
        } else {
            debug_assert!(new_len == 0, "new length out of bounds");
        }
    }

    /// Shortens the vector, keeping only the first `len` elements and dropping
    /// the rest.
    ///
    /// If `len` is greater than or equal to the vector's current length, it
    /// does nothing.
    ///
    /// Note that this method has no effect on the allocated capacity of the
    /// vector.
    pub fn truncate(&mut self, len: usize) {
        truncate_impl!(self, len);
    }

    /// Removes the last element from the vector and returns it, or `None` if it
    /// is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::ThinVec;
    /// let mut vec = ThinVec::new();
    /// vec.push(1);
    /// vec.push(2);
    /// assert_eq!(vec.pop(), Some(2));
    /// assert_eq!(vec.pop(), Some(1));
    /// assert_eq!(vec.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        pop_impl!(self)
    }

    /// Removes and returns the last element from a vector if the predicate
    /// returns `true`, or [`None`] if the predicate returns `false` or if the
    /// vector is empty.
    ///
    /// The predicate is not called if the vector is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::ThinVec;
    /// let mut vec = ThinVec::new();
    /// vec.push(1);
    /// vec.push(2);
    /// assert_eq!(vec.pop_if(|x| *x % 2 == 0), Some(2));
    /// assert_eq!(vec.pop_if(|x| *x % 2 == 0), None);
    /// ```
    pub fn pop_if(&mut self, func: impl FnOnce(&mut T) -> bool) -> Option<T> {
        pop_if_impl!(self, func)
    }

    /// Removes and returns the element at position `index` within the vector,
    /// shifting all elements after it to the left.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::thin_vec;
    /// let mut v = thin_vec!['a', 'b', 'c'];
    /// assert_eq!(v.remove(1), 'b');
    /// assert_eq!(v, ['a', 'c']);
    /// ```
    ///
    /// # Time complexity
    ///
    /// Takes *O*([`len`] - `index`) time. All items after the removed element
    /// must be shifted to the left. In the worst case, all elements are shifted
    /// when the removed element is at the start of the vector.
    ///
    /// If you don't need to preserve the order of the elements, consider using
    /// [`swap_remove`] instead.
    ///
    /// [`len`]: Self::len
    /// [`swap_remove`]: Self::swap_remove
    #[inline]
    #[track_caller]
    pub fn remove(&mut self, index: usize) -> T {
        let len = self.len();
        assert!(index < len, "index out of bounds");

        // SAFETY: index is checked above
        unsafe { self.remove_unchecked(index) }
    }

    /// Removes and returns the element at position `index` within the vector,
    /// shifting all elements after it to the left, without doing any bounds checking.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `index` is less than the current length of the vector.
    pub unsafe fn remove_unchecked(&mut self, index: usize) -> T {
        remove_unchecked_impl!(self, index)
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
    /// # use hipstr::thin_vec;
    /// let mut v = thin_vec!["foo", "bar", "baz", "qux"];
    ///
    /// assert_eq!(v.swap_remove(1), "bar");
    /// assert_eq!(v, ["foo", "qux", "baz"]);
    ///
    /// assert_eq!(v.swap_remove(0), "foo");
    /// assert_eq!(v, ["baz", "qux"]);
    /// ```
    #[track_caller]
    pub fn swap_remove(&mut self, index: usize) -> T {
        swap_remove_impl!(self, index)
    }

    /// Clears the vector, removing all values.
    ///
    /// Note that this method has no effect on the allocated capacity
    /// of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::thin_vec;
    /// let mut v = thin_vec![1, 2, 3];
    /// v.clear();
    /// assert!(v.is_empty());
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        self.truncate(0);
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
    /// # use hipstr::vecs::ThinVec;
    /// // Allocate vector big enough for 10 elements.
    /// let mut v = ThinVec::with_capacity(10);
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
    /// assert_eq!(&v, &[0, 1, 2]);
    /// ```
    #[must_use]
    pub const fn spare_capacity_mut(&mut self) -> &mut [MaybeUninit<T>] {
        spare_capacity_mut_impl!(self)
    }

    /// Creates a draining iterator that removes the specified range in the vector
    /// and yields the removed items.
    ///
    /// When the iterator is dropped, all elements in the range are removed from
    /// the vector, even if the iterator was not fully consumed. If the iterator
    /// is leaked, the vector may still be truncated, but the exact behavior is
    /// unspecified.
    ///
    /// # Panics
    ///
    /// Panics if the range is invalid.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::thin_vec;
    /// let mut v = thin_vec![1, 2, 3, 4, 5];
    /// {
    ///     let mut iter = v.drain(1..4);
    ///     assert_eq!(iter.next(), Some(2));
    ///     assert_eq!(iter.next(), Some(3));
    ///     assert_eq!(iter.next(), Some(4));
    ///     assert_eq!(iter.next(), None);
    /// }
    /// assert_eq!(v, [1, 5]);
    /// ```
    pub fn drain(&mut self, range: impl RangeBounds<usize>) -> Drain<'_, Self> {
        unwrap_display(Drain::new(self, range))
    }

    /// Attempts to create a draining iterator that removes the specified range in the vector
    /// and yields the removed items.
    ///
    /// When the iterator is dropped, all elements in the range are removed from
    /// the vector, even if the iterator was not fully consumed. If the iterator
    /// is leaked, the vector may still be truncated, but the exact behavior is
    /// unspecified.
    ///
    /// # Errors
    ///
    /// Returns a [`RangeError`] if the specified range is invalid.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::thin_vec;
    /// # use hipstr::common::RangeError;
    /// let mut v = thin_vec![1, 2, 3, 4, 5];
    /// {
    ///     let mut iter = v.try_drain(1..4).unwrap();
    ///     assert_eq!(iter.next(), Some(2));
    ///     assert_eq!(iter.next(), Some(3));
    ///     assert_eq!(iter.next(), Some(4));
    ///     assert_eq!(iter.next(), None);
    /// }
    /// assert_eq!(v, [1, 5]);
    ///
    /// // Example of an invalid range
    /// let result = v.try_drain(6..8);
    /// assert_eq!(result.unwrap_err(), RangeError::EndOutOfBounds { end: 8, len: 2 });
    /// ```
    pub fn try_drain(
        &mut self,
        range: impl RangeBounds<usize>,
    ) -> Result<Drain<'_, Self>, RangeError> {
        Drain::new(self, range)
    }

    /// Extends the vector by duplicating a range of elements within itself.
    ///
    /// This method is useful for duplicating a range of elements within the
    /// vector. The range is specified using the `RangeBounds` trait, which
    /// allows for flexible range specifications (e.g., `0..5`, `..5`, `5..`).
    ///
    /// # Panics
    ///
    /// Panics if the specified range is invalid.
    ///
    /// See [`try_extend_from_within`] for a no-panic alternative.
    ///
    /// [`try_extend_from_within`]: Self::try_extend_from_within
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::thin_vec;
    /// let mut v = thin_vec![1, 2, 3];
    /// v.extend_from_within(1..3);
    /// assert_eq!(v.as_slice(), [1, 2, 3, 2, 3]);
    /// ```
    pub fn extend_from_within(&mut self, range: impl RangeBounds<usize>)
    where
        T: Clone,
    {
        unwrap_display(self.try_extend_from_within(range));
    }

    /// Attempts to extend the vector from a range of elements within itself.
    ///
    /// This method is useful for duplicating a range of elements within the
    /// vector. The range is specified using the `RangeBounds` trait, which
    /// allows for flexible range specifications (e.g., `0..5`, `..5`, `5..`).
    ///
    /// # Errors
    ///
    /// Returns a [`RangeError`] if the specified range is invalid.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::thin_vec;
    /// # use hipstr::common::RangeError;
    /// let mut v = thin_vec![1, 2, 3];
    /// v.try_extend_from_within(1..3).unwrap();
    /// assert_eq!(v.as_slice(), [1, 2, 3, 2, 3]);
    ///
    /// // out of bounds range
    /// let err = v.try_extend_from_within(6..8).unwrap_err();
    /// assert_eq!(err, RangeError::EndOutOfBounds { end: 8, len: 5 });
    /// ```
    pub fn try_extend_from_within(
        &mut self,
        range: impl RangeBounds<usize>,
    ) -> Result<(), common::RangeError>
    where
        T: Clone,
    {
        let len = self.len();
        let Range { start, end } = common::range(range, len)?;
        let ptr = self.ptr();
        unsafe {
            for (i, j) in (start..end).zip(len..) {
                ptr.add(j).write(ptr.add(i).as_ref().clone());
                self.set_len(j + 1);
            }
        }
        Ok(())
    }

    /// Clones with a fresh prefix.
    pub(crate) fn fresh_clone<Q: ConstDefault>(&self) -> ThinVec<T, Q>
    where
        T: Clone,
    {
        let len = self.len();
        let mut this = ThinVec::with_capacity(len);
        this.extend_from_slice(self.as_slice());
        this
    }

    /// Copies with a fresh prefix.
    pub(crate) fn fresh_copy<Q: ConstDefault>(&self) -> ThinVec<T, Q>
    where
        T: Copy,
    {
        let len = self.len();
        let mut this = ThinVec::with_capacity(len);
        this.extend_from_slice_copy(self.as_slice());
        this
    }

    /// Moves the items to a new vector with a fresh prefix.
    pub(crate) fn fresh_move<Q: ConstDefault>(mut self) -> ThinVec<T, Q> {
        if can_reuse::<T, P, Q>() {
            let this = ManuallyDrop::new(self);
            let Some(mut header) = this.0.get() else {
                return ThinVec::new();
            };

            // drop the old prefix if needed
            if mem::needs_drop::<P>() {
                // SAFETY: the prefix is valid by the type invariant
                unsafe {
                    ptr::drop_in_place(&raw mut header.as_mut().prefix);
                }
            }

            let new_header: NonNull<ThinHeader<T, Q>> = header.cast();

            // write the new prefix without dropping the already-drop, maybe invalid, prefix
            // SAFETY: new_header is a valid pointer (even if the prefix is inconsistant)
            unsafe {
                let prefix_ptr = &raw mut (*new_header.as_ptr()).prefix;
                prefix_ptr.write(Q::DEFAULT);
            }

            ThinVec(ThinRepr::new(new_header))
        } else {
            let len = self.len();
            let mut this = ThinVec::with_capacity(len);
            unsafe {
                this.ptr().copy_from_nonoverlapping(self.ptr(), len);
                this.set_len(len);
                self.set_len(0);
            }
            this
        }
    }

    /// Creates a new thin vector from a slice of elements by copying the
    /// elements.
    pub fn from_slice_copy(slice: &[T]) -> Self
    where
        T: Copy,
    {
        let len = slice.len();
        let mut this = Self::with_capacity(len);

        unsafe {
            maybe_uninit_write_copy_of_slice(&mut this.spare_capacity_mut()[..len], slice);
            this.set_len(len);
        };

        this
    }

    /// Creates a new thin vector from a slice of elements by cloning the
    /// elements.
    pub(crate) fn from_slice_clone(slice: &[T]) -> Self
    where
        T: Clone,
    {
        from_slice_clone_impl!(slice)
    }

    /// Creates a new thin vector from a copy-on-write slice of elements,
    /// possibly cloning elements if borrowed.
    pub(crate) fn from_cow(cow: Cow<'_, [T]>) -> Self
    where
        T: Clone,
    {
        match cow {
            Cow::Borrowed(slice) => Self::from_slice_clone(slice),
            Cow::Owned(vec) => Self::from_vector(vec),
        }
    }

    /// Creates a new thin vector from an array of elements by copying the
    /// elements.
    #[inline]
    pub(crate) fn from_array<const N: usize>(array: [T; N]) -> Self {
        from_array_impl!(array)
    }

    #[inline]
    pub(crate) fn from_boxed_slice(boxed: Box<[T]>) -> Self {
        Self::from_vector(boxed.into_vec())
    }

    /// Creates a new thin vector from a vector.
    #[inline]
    pub(crate) fn from_vector(mut vec: impl Mutate<Item = T>) -> Self {
        let mut vec = vec.mutate();
        let vec = vec.borrow_mut();

        let len = vec.len();
        let mut this = Self::with_capacity(len);
        unsafe {
            this.ptr().copy_from_nonoverlapping(vec.as_non_null(), len);
            vec.set_len(0);
            this.set_len(len);
        }
        this
    }

    pub(crate) fn from_iter(iterable: impl IntoIterator<Item = T>) -> Self {
        let iter = iterable.into_iter();
        let min = iter.size_hint().0;
        let mut this = Self::with_capacity(min);

        for (i, value) in iter.enumerate() {
            if i >= min {
                this.reserve(1);
            }
            // SAFETY: the capacity is updated if necessary above
            unsafe {
                this.ptr().add(i).write(value);
                this.set_len(i + 1);
            }
        }
        this
    }

    /// Creates a new thin vector with the given capacity. The vector will be
    /// able to hold at least `capacity` elements without reallocating.
    ///
    /// # Panics
    ///
    /// Panics if the capacity overflows.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::ThinVec;
    /// let vec: ThinVec<i32> = ThinVec::with_capacity(10);
    /// assert!(vec.capacity() >= 10);
    /// ```
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self(Self::make_repr(capacity))
    }

    fn make_repr(capacity: usize) -> ThinRepr<T, P> {
        if capacity == 0 {
            return ThinRepr::NULL;
        }

        let capacity = capacity.max(Self::MINIMAL_CAPACITY);
        let (layout, capacity) =
            ThinHeader::<T, P>::layout(capacity).expect("invalid layout: buffer too large");
        let ptr = unsafe { alloc(layout) };
        let ptr = check_alloc(ptr, layout);
        let ptr = ptr.cast();
        let mut header = ThinHeader::DEFAULT;
        header.cap = capacity;
        unsafe {
            ptr.write(header);
        }
        ThinRepr::new(ptr)
    }

    /// Deallocates the vector's buffer and drops the prefix if needed.
    ///
    /// Do nothing for the vector's contents.
    ///
    /// # Safety
    ///
    /// Actually safe, but will not drop the contents.
    fn dealloc(&mut self) {
        if let Some(header) = self.0.get() {
            let layout = self.current_layout();
            if mem::needs_drop::<P>() {
                let prefix = unsafe { &raw mut (*header.as_ptr()).prefix };
                // SAFETY: the prefix is valid by the type invariant
                unsafe {
                    ptr::drop_in_place(prefix);
                }
            }

            // SAFETY: header is valid and the layout is correct
            unsafe {
                dealloc(header.cast().as_ptr(), layout);
            }
        }
        self.0 = ThinRepr::NULL;
    }

    /// Splits the collection into two at the given index.
    ///
    /// Returns a newly allocated vector containing the elements in the range
    /// `[at, len)`. After the call, the original vector will be left containing
    /// the elements `[0, at)` with its previous capacity unchanged.
    ///
    /// - If you want to take ownership of the entire contents and capacity of
    ///   the vector, see [`mem::take`] or [`mem::replace`].
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
    /// # use hipstr::thin_vec;
    /// let mut v = thin_vec!['a', 'b', 'c'];
    /// let w = v.split_off(1);
    /// assert_eq!(v.as_slice(), ['a']);
    /// assert_eq!(w.as_slice(), ['b', 'c']);
    /// ```
    ///
    /// [`truncate`]: Self::truncate
    /// [`drain`]: Self::drain
    #[must_use = "use .truncate() if you don't need the returned vector"]
    pub fn split_off(&mut self, at: usize) -> Self {
        split_off_impl!(self, at)
    }

    /// Sets the capacity of the vector to `new_cap`.
    ///
    /// # Safety
    ///
    /// This is a low-level operation that maintains few of the invariants of
    /// the type.
    ///
    /// `new_cap` must be less than or equal to the current length of the
    /// vector.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows.
    pub(crate) unsafe fn set_capacity(&mut self, new_cap: usize) {
        debug_assert!(new_cap >= self.len(), "set_capacity loses data");

        // allocate new if empty
        let Some(original_ptr) = self.0.get() else {
            self.0 = Self::make_repr(new_cap);
            return;
        };

        // reset to empty if new_cap is 0
        if new_cap == 0 {
            self.dealloc();
            return;
        }

        // computes the layouts
        let layout = self.current_layout();
        let (new_layout, eff_cap) =
            ThinHeader::<T, P>::layout(new_cap).expect("invalid layout: buffer too large");

        // realloc only if needed
        if layout != new_layout {
            // SAFETY: pointer and layout are valid by the type invariant
            let ptr = unsafe { realloc(original_ptr.as_ptr().cast(), layout, new_layout.size()) };
            let ptr = check_alloc(ptr, new_layout);
            let mut ptr = ptr.cast();
            let header: &mut ThinHeader<_, _> = unsafe { ptr.as_mut() };
            header.cap = eff_cap;

            self.0 = ThinRepr::new(ptr);
        }
    }

    /// Reserves the minimum capacity for at least `additional` more elements to
    /// be inserted in the given `Thin<T, P>`. Unlike [`reserve`], this will not
    /// intentionally over-allocate to potentially avoid frequent reallocations.
    ///
    /// Prefer [`reserve`] if future insertions are expected.
    ///
    /// [`reserve`]: Self::reserve
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows.
    pub fn reserve_exact(&mut self, additional: usize) {
        if additional > self.capacity() - self.len() {
            let required = self
                .len()
                .checked_add(additional)
                .expect("capacity overflow");
            unsafe {
                self.set_capacity(required);
            }
        }
    }

    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the given `Thin<T, P>`. The collection may reserve more space to
    /// avoid frequent reallocations.
    ///
    /// Prefer [`reserve_exact`] if the exact amount of elements to be added is
    /// known.
    ///
    /// [`reserve_exact`]: Self::reserve_exact
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows.
    pub fn reserve(&mut self, additional: usize) {
        if additional > self.capacity() - self.len() {
            let required = self
                .len()
                .checked_add(additional)
                .expect("capacity overflow");
            let new_cap = cmp::max(required, self.capacity() * 2);
            unsafe {
                self.set_capacity(new_cap);
            }
        }
    }

    /// Appends an element to the back of the vector.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::ThinVec;
    /// let mut vec = ThinVec::new();
    /// vec.push(1);
    /// vec.push(2);
    /// vec.push(3);
    /// assert_eq!(vec.as_slice(), [1, 2, 3]);
    /// ```
    #[track_caller]
    pub fn push(&mut self, value: T) {
        let len = self.len();
        self.reserve(1);

        // SAFETY: the capacity has been checked/updated beforehand
        unsafe {
            self.ptr().add(len).write(value);
            self.set_len(len + 1);
        }
    }

    /// Appends an element to the back of the vector if there is enough capacity.
    ///
    /// # Errors
    ///
    /// Returns the element back if there is not enough capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::ThinVec;
    /// let mut vec = ThinVec::with_capacity(2);
    /// let cap = vec.capacity(); // actual capacity may be larger
    /// for i in 0..cap {
    ///     vec.push_within_capacity(1).unwrap();
    /// }
    /// assert!(vec.push_within_capacity(cap).is_err());
    /// ```
    pub fn push_within_capacity(&mut self, value: T) -> Result<(), T> {
        push_within_capacity!(self, value)
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
    /// use hipstr::thin_vec;
    /// let mut v = thin_vec!['a', 'c', 'd'];
    /// v.insert(1, 'b');
    /// assert_eq!(v, ['a', 'b', 'c', 'd']);
    /// v.insert(4, 'e');
    /// assert_eq!(v, ['a', 'b', 'c', 'd', 'e']);
    /// ```
    ///
    /// # Time complexity
    ///
    /// Takes *O*([`len`]) time. All items after the insertion index must be
    /// shifted to the right. In the worst case, all elements are shifted when
    /// the insertion index is 0.
    ///
    /// [`len`]: Self::len
    #[track_caller]
    pub fn insert(&mut self, index: usize, value: T) {
        insert_impl!(self, index, value);
    }

    /// Moves all the elements of `other` into `self`, leaving `other` empty.
    ///
    /// # Panics
    ///
    /// Panics if the new buffer would be too large.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::thin_vec;
    /// let mut v = thin_vec![1, 2, 3];
    /// let mut w = thin_vec![4, 5, 6];
    /// v.append(&mut w);
    /// assert_eq!(v, [1, 2, 3, 4, 5, 6]);
    /// assert_eq!(w, []);
    /// ```
    pub fn append(&mut self, other: &mut impl Mutate<Item = T>) {
        let mut other = other.mutate();
        let other = other.borrow_mut();

        append_impl!(self, other);
    }

    fn extend_iter(&mut self, iterable: impl IntoIterator<Item = T>) {
        let iter = iterable.into_iter();
        let len = self.len();
        let min = iter.size_hint().0;
        self.reserve(min);

        for (i, value) in iter.enumerate() {
            if i >= min {
                self.reserve(1);
            }
            unsafe {
                self.ptr().add(len + i).write(value);
                self.set_len(len + i + 1);
            }
        }
    }

    /// Appends a slice of elements to the thin vector.
    ///
    /// If `T` implements `Copy`, see [`extend_from_slice_copy`] for a more efficient version.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::ThinVec;
    /// let mut vec = ThinVec::new();
    /// vec.extend_from_slice(&[1, 2, 3]);
    /// assert_eq!(vec.as_slice(), &[1, 2, 3]);
    /// vec.extend_from_slice(&[4, 5]);
    /// assert_eq!(vec.as_slice(), &[1, 2, 3, 4, 5]);
    /// ```
    ///
    /// [`extend_from_slice_copy`]: Self::extend_from_slice_copy
    #[doc(alias = "push_slice")]
    pub fn extend_from_slice(&mut self, slice: &[T])
    where
        T: Clone,
    {
        extend_from_slice_impl!(self, slice);
    }

    /// Appends a slice of elements to the thin vector.
    ///
    /// This is a more efficient version of [`extend_from_slice`] for types that implement `Copy`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::ThinVec;
    /// let mut vec = ThinVec::new();
    /// vec.extend_from_slice_copy(&[1, 2, 3]);
    /// assert_eq!(vec.as_slice(), &[1, 2, 3]);
    /// vec.extend_from_slice_copy(&[4, 5]);
    /// assert_eq!(vec.as_slice(), &[1, 2, 3, 4, 5]);
    /// ```
    ///
    /// [`extend_from_slice`]: Self::extend_from_slice
    #[doc(alias = "push_slice_copy")]
    #[inline]
    pub fn extend_from_slice_copy(&mut self, slice: &[T])
    where
        T: Copy,
    {
        let slice_len = slice.len();
        self.reserve(slice_len);

        unsafe {
            maybe_uninit_write_copy_of_slice(&mut self.spare_capacity_mut()[..slice_len], slice);
            self.set_len(self.len() + slice_len);
        }
    }

    /// Appends an array of elements to the thin vector.
    ///
    /// Items for the array are *moved* into the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::ThinVec;
    /// let mut vec = ThinVec::new();
    /// vec.extend_from_array([1, 2, 3]);
    /// assert_eq!(vec.as_slice(), &[1, 2, 3]);
    /// vec.extend_from_array([4, 5]);
    /// assert_eq!(vec.as_slice(), &[1, 2, 3, 4, 5]);
    /// ```
    #[doc(alias = "push_array")]
    pub fn extend_from_array<const N: usize>(&mut self, array: [T; N]) {
        extend_from_array_impl!(self, array);
    }

    /// Shrinks the vector's capacity to at least the given capacity.
    ///
    /// The capacity will remain at least as large as both the length and the
    /// supplied value.
    ///
    /// If the current capacity is less that the provided value, this is a
    /// no-op.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::ThinVec;
    /// let mut vec = ThinVec::with_capacity(10);
    /// vec.extend([1, 2, 3]);
    /// assert!(vec.capacity() >= 10);
    /// vec.shrink_to(5);
    /// assert!(vec.capacity() < 10);
    /// vec.shrink_to(10);
    /// assert!(vec.capacity() < 10);
    /// ```
    pub fn shrink_to(&mut self, min_cap: usize) {
        let len = self.len();
        let cap = self.capacity();
        if min_cap >= cap {
            return;
        }
        let new_cap = min_cap.max(len);
        unsafe {
            self.set_capacity(new_cap);
        }
    }

    /// Shrinks the capacity of the vector as much as possible.
    ///
    /// The resulting vector might still have some excess capacity, just as is
    /// the case for [`with_capacity`].
    ///
    /// [`with_capacity`]: Self::with_capacity
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::ThinVec;
    /// let mut vec = ThinVec::with_capacity(10);
    /// vec.extend([1, 2, 3]);
    /// assert!(vec.capacity() >= 10);
    /// vec.shrink_to_fit();
    /// assert!(vec.capacity() < 10);
    /// ```
    pub fn shrink_to_fit(&mut self) {
        let len = self.len();
        let cap = self.capacity();
        if len == cap {
            return;
        }
        unsafe {
            self.set_capacity(len);
        }
    }

    /// Resizes the vector to the specified length, filling in new elements
    /// with the specified value.
    ///
    /// If `new_len` is less than the current length, the vector is truncated.
    /// If `new_len` is greater than the current length, the vector is extended
    /// by cloning the specified value.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::thin_vec;
    /// let mut v = thin_vec![1, 2, 3];
    /// v.resize(5, 0);
    /// assert_eq!(v.as_slice(), [1, 2, 3, 0, 0]);
    /// v.resize(2, 0);
    /// assert_eq!(v.as_slice(), [1, 2]);
    /// ```
    pub fn resize(&mut self, new_len: usize, value: T)
    where
        T: Clone,
    {
        resize_impl!(
            self,
            new_len,
            iter::repeat_n(value, new_len.saturating_sub(self.len()))
        );
    }

    /// Resizes the vector to the specified length, filling in new elements
    /// by calling the provided function.
    ///
    /// If `new_len` is less than the current length, the vector is truncated.
    /// If `new_len` is greater than the current length, the vector is extended
    /// by calling the provided function repeatedly to generate new elements.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::thin_vec;
    /// let mut v = thin_vec![1, 2, 3];
    /// let mut i = 0;
    /// v.resize_with(6, || { i += 1; i });
    /// assert_eq!(v.as_slice(), [1, 2, 3, 1, 2, 3]);
    /// v.resize_with(2, || 0);
    /// assert_eq!(v.as_slice(), [1, 2]);
    /// ```
    pub fn resize_with(&mut self, new_len: usize, f: impl FnMut() -> T)
    where
        T: Clone,
    {
        resize_impl!(self, new_len, iter::repeat_with(f));
    }
}

/// Computes a reasonable minimal capacity for an allocated thin vector
/// depending on the prefix type and the element type.
pub(crate) const fn minimal_capacity<T, P>() -> usize {
    let header = size_of::<ThinHeader<T, P>>();
    let base = (header + 1).next_power_of_two() - header;
    let t = size_of::<T>();
    if t == 0 {
        usize::MAX
    } else if 16 * t <= base {
        base / t
    } else if 4 * t <= base {
        8
    } else {
        1
    }
}

/// Checks if two prefix types `P` and `Q` are compatible to reuse a thin vec
/// allocation when moving from the first prefix `P` type to the other `Q`.
pub(crate) const fn can_reuse<T, P, Q>() -> bool {
    const {
        size_of::<P>() == size_of::<Q>()
            && align_of::<P>() >= align_of::<Q>()
            && offset_of!(ThinHeader<T, P>, prefix) == offset_of!(ThinHeader<T, Q>, prefix)
    }
}

// impl<T, P: ConstDefault> ops::Deref for ThinVec<T, P> {
//     type Target = [T];

//     #[inline]
//     fn deref(&self) -> &Self::Target {
//         self.as_slice()
//     }
// }

// impl<T, P: ConstDefault> ops::DerefMut for ThinVec<T, P> {
//     #[inline]
//     fn deref_mut(&mut self) -> &mut Self::Target {
//         self.as_mut_slice()
//     }
// }

impl<T, C: ConstDefault> Drop for ThinVec<T, C> {
    fn drop(&mut self) {
        // SAFETY: type invariant
        unsafe {
            drop_raw_slice(self.as_mut_ptr(), self.len());
        }
        self.dealloc();
    }
}

impl<T: Clone, P: ConstDefault> Clone for ThinVec<T, P> {
    fn clone(&self) -> Self {
        self.fresh_clone()
    }
}

macros::trait_impls! {
    [T, P: ConstDefault] {
        Extend {
            T => ThinVec<T, P>;
        }
    }
    [T, P] where [T: Clone, P: ConstDefault] {
        From {
            Cow<'_, [T]> => ThinVec<T, P> = ThinVec::from_cow;
        }
    }
    [T, P, const N: usize] where [ T:Clone, P: ConstDefault] {
    }

    [T, P: ConstDefault, L: super::inline::InlineLength]
    {
        From {
            super::inline::InlineVec<T, L> => ThinVec<T, P> = Self::from_vector;
        }
    }

    [T, U, P: ConstDefault] where [T: PartialEq<U>] {
        PartialEq {
            ThinVec<T, P>, ThinVec<U, P>;

            [T], ThinVec<U, P>;
            &[T], ThinVec<U, P>;
            &mut [T], ThinVec<U, P>;
            Vec<T>, ThinVec<U, P>;

            ThinVec<T, P>, [U];
            ThinVec<T, P>, &[U];
            ThinVec<T, P>, &mut[U];
            ThinVec<T, P>, Vec<U>;
        }
    }
    [T, U, P: ConstDefault, const N: usize] where [T: PartialEq<U>] {
        PartialEq {
            [T; N], ThinVec<U, P>;
            ThinVec<T, P>, [U; N];

            &[T; N], ThinVec<U, P>;
            ThinVec<T, P>, &[U; N];
        }
    }

    [T, P: ConstDefault] where [T: PartialOrd] {
        PartialOrd {
            ThinVec<T, P>;

            Vec<T>, ThinVec<T, P>;
            ThinVec<T, P>, Vec<T>;

            [T], ThinVec<T, P>;
            ThinVec<T, P>, [T];

            &[T], ThinVec<T, P>;
            ThinVec<T, P>, &[T];

            &mut [T], ThinVec<T, P>;
            ThinVec<T, P>, &mut [T];
        }
    }

    [T, P: ConstDefault, const N: usize] where [T: PartialOrd] {
        PartialOrd {
            [T; N], ThinVec<T, P>;
            ThinVec<T, P>, [T; N];

            &[T; N], ThinVec<T, P>;
            ThinVec<T, P>, &[T; N];
        }
    }
}

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
            $crate::vecs::thin::SmartThinVec::<_, $t>::from(
                $crate::thin_vec![ $( $rest )* ]
            )
        }
    };

    [ $($rest:tt)* ] => {
        $crate::smart_thin_vec![$crate::Arc : $($rest)*]
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
    Vector(T),
    ConstDefault(Self::EMPTY),
    // Delegated traits: debug and hash
    DelegateDebug(Self::as_slice where T: core::fmt::Debug),
    DelegateHash(Self::as_slice where T: core::hash::Hash),
    // AsRef, Deref and Borrow
    AsRef(ThinVec<T, C>, Self::as_thin_vec),
    AsRef([T], Self::as_slice),
    Deref(ThinVec<T ,C>, Self::as_thin_vec),
    Borrow(ThinVec<T, C>, Self::as_thin_vec),
    Borrow([T], Self::as_slice),
    // Iterators
    // TODO IntoIterator?
    FromIterator(T, Self::from_iter),
    // From conversions
    From(Vec<T>, Self::from_vector),
    From(Box<[T]>, Self::from_boxed_slice),
    From(ThinVec<T, P>, Self::from_thin_vec, (P: ConstDefault)),
    From([T; N], Self::from_array, (const N: usize)),
    From(&[T], Self::from_slice_clone, () where (T: Clone)),
    From(&mut [T], Self::from_slice_clone, () where (T: Clone)),
    From(&[T; N], Self::from_slice_clone, (const N: usize) where (T: Clone)),
    From(&mut [T;N], Self::from_slice_clone, (const N: usize) where (T: Clone)),
)]
pub struct SmartThinVec<T, C: Backend>(pub(crate) ThinRepr<T, C>);

impl<T, B: Backend> SmartThinVec<T, B> {
    const EMPTY: Self = {
        let tv = ThinVec::new();
        unsafe { Self::from_thin_vec_unchecked(tv) }
    };

    /// Returns the number of elements in the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::vecs::thin::SmartThinVec;
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
    /// # use hipstr::vecs::thin::SmartThinVec;
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
    /// # use hipstr::vecs::thin::SmartThinVec;
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
    /// # use hipstr::vecs::thin::SmartThinVec;
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

    #[must_use]
    #[inline]
    pub const fn as_slice(&self) -> &[T] {
        self.as_thin_vec().as_slice()
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
    /// # use hipstr::vecs::SmartThinVec;
    /// let v = SmartThinVec::<u8>::new();
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
    /// # use hipstr::vecs::thin::SmartThinVec;
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
    /// # use hipstr::{smart_thin_vec, thin_vec};
    /// # use hipstr::vecs::thin::ThinVec;
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
    pub(crate) fn from_vector(vector: impl Mutate<Item = T>) -> Self {
        let thin_vec = ThinVec::from_vector(vector);
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
        Self::from_vector(slice.into_vec())
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

    #[inline]
    #[must_use]
    pub(crate) fn from_slice_copy(slice: &[T]) -> Self
    where
        T: Copy,
    {
        let thin_vec = ThinVec::from_slice_copy(slice);
        unsafe { Self::from_thin_vec_unchecked(thin_vec) }
    }

    #[inline]
    #[must_use]
    pub(crate) fn from_iter(iterable: impl IntoIterator<Item = T>) -> Self {
        let thin_vec = ThinVec::from_iter(iterable);
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
                let vec: ThinVec<T, B> = ThinVec(self.0);
                drop(vec);
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

trait_impls! {
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
