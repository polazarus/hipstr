//! Thin vector implementation.

use alloc::alloc::{alloc, dealloc, realloc, Layout};
use alloc::borrow::Cow;
use alloc::boxed::Box;
use alloc::vec::Vec;
use core::borrow::BorrowMut;
use core::hint::unreachable_unchecked;
use core::mem::{offset_of, ManuallyDrop, MaybeUninit};
use core::ops::{Range, RangeBounds};
use core::ptr::NonNull;
use core::{cmp, mem, ptr, slice};

use const_default::ConstDefault;
use rules_derive::rules_derive;

use super::reprs::ThinRepr;
use crate::common::derives::{
    AsRef, ConstDefault, DelegateDebug, DelegateHash, Deref, From, FromIterator, IntoIterator,
    MutVector,
};
use crate::common::drain::Drain;
use crate::common::into_iter::IntoIter;
use crate::common::methods::{
    append_impl, extend_from_array_impl, extend_from_slice_impl, from_array_impl,
    from_slice_clone_impl, pop_if_impl, pop_impl, remove_unchecked_impl, resize_impl,
    spare_capacity_mut_impl, swap_remove_impl, truncate_impl,
};
use crate::common::traits::{MutVector, Mutate, Vector};
use crate::common::{
    check_alloc, drop_raw_slice, maybe_uninit_write_copy_of_slice, panic_display, RangeError,
    ZeroUsize,
};
use crate::vecs::reprs::ThinHeader;
use crate::{common, macros};

#[cfg(test)]
mod tests;

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
        let mut vec = $crate::vecs::ThinVec::with_capacity(thin_vec!(@count $( ($e) )+));
        $(
            vec.push($e);
        )+
        vec
    }};

    (@count) => {
        0
    };
    (@count $( $a:tt $b:tt )*) => {
        thin_vec!(@count $( $a )* ) << 1
    };
    (@count $_odd:tt $( $a:tt $_b:tt )*) => {
        (thin_vec!(@count $( $a )* ) << 1) | 1
    };
}

/// A thin vector, that is, a contiguous growable array type with heap-allocated
/// metadata (prefix, capacity, length) and contents.
///
/// Whereas [`Vec`] is three-word wide, this vector is one-word wide. It
/// consists in a single pointer to a heap-allocated area containing both the
/// capacity, the length, and the actual data.
///
/// `ThinVec` contains an arbitrary additional data `P`.
///
/// [`Vec`]: alloc::vec::Vec
#[repr(transparent)]
#[rules_derive(
    MutVector(T),
    ConstDefault(Self(ThinRepr::NULL)),
    DelegateDebug(Self::as_slice where T: core::fmt::Debug),
    DelegateHash(Self::as_slice where T: core::hash::Hash),
    AsRef([T], Self::as_slice, Self::as_mut_slice),
    Deref([T], Self::as_slice, Self::as_mut_slice),
    IntoIterator(T, IntoIter<Self>, IntoIter::new),
    FromIterator(T, Self::from_iter),
)]
pub struct ThinVec<T, P: ConstDefault = Reserved>(pub(super) ThinRepr<T, P>);

impl<T, P: ConstDefault> ThinVec<T, P> {
    const MINIMAL_CAPACITY: usize = {
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
    };

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
    /// use hipstr::vecs::ThinVec;
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
        let (layout, _, _) =
            unsafe { ThinHeader::<T, P>::layout(self.capacity()).unwrap_unchecked() };
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
            debug_assert!(new_len <= header.cap, "length out of bounds");

            // SAFETY: `header` is guaranteed to be valid as long as the vector is valid
            header.len = new_len;
        } else if new_len > 0 {
            debug_assert!(false, "length out of bounds");
            // SAFETY: precondition says new_len <= capacity (here 0)
            unsafe { unreachable_unchecked() }
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
        Drain::new(self, range).unwrap_or_else(panic_display)
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
        self.try_extend_from_within(range)
            .unwrap_or_else(common::panic_display);
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

            // SAFETY: write the new prefix without dropping the already-drop, maybe invalid, prefix
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
        let len = boxed.len();
        let mut this = Self::with_capacity(len);

        // SAFETY:
        // - `boxed` is a valid pointer to a slice of `T` and length `len`
        // - `this` has a capacity >= `len`
        unsafe {
            // move the box's content to `this`
            this.ptr()
                .as_ptr()
                .copy_from_nonoverlapping(boxed.as_ptr(), len);

            // update the length
            this.set_len(len);
        }

        // drop the box without dropping the moved content
        // SAFETY: ManuallyDrop is a transparent wrapper
        let _: Box<[ManuallyDrop<T>]> = unsafe { mem::transmute(boxed) };

        this
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
        let (layout, _offset, capacity) =
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
        let len = self.len();
        assert!(at <= len, "index out of bounds");

        let other_len = len - at;
        let mut other = Self::with_capacity(other_len);

        // SAFETY: `at` is checked above
        unsafe {
            let src = self.ptr().add(at);
            let dst = other.ptr();
            dst.copy_from_nonoverlapping(src, other_len);
            self.set_len(at);
            other.set_len(other_len);
        }

        other
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
        let (new_layout, _, eff_cap) =
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
    pub fn push(&mut self, value: T) {
        let len = self.len();
        self.reserve(1);

        // SAFETY: the capacity has been checked/updated beforehand
        unsafe {
            self.ptr().add(len).write(value);
            self.set_len(len + 1);
        }
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
    pub fn insert(&mut self, index: usize, element: T) {
        let len = self.len();
        assert!(index <= len, "index out of bounds");

        self.reserve(1);

        // SAFETY: index is checked above
        unsafe {
            let ptr = self.ptr().add(index);
            if index < len {
                ptr.add(1).copy_from(ptr, len - index);
            }
            ptr.write(element);
            self.set_len(len + 1);
        }
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
        resize_impl!(self, new_len, value.clone());
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
    pub fn resize_with(&mut self, new_len: usize, mut f: impl FnMut() -> T)
    where
        T: Clone,
    {
        resize_impl!(self, new_len, f());
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
        From {
            Box<[T]> => ThinVec<T, P> = Self::from_boxed_slice;
            Vec<T> => ThinVec<T, P> = Self::from_vector;
        }
    }
    [T, P] where [T: Clone, P: ConstDefault] {
        From {
            &[T] => ThinVec<T, P> = ThinVec::from_slice_clone;
            &mut [T] => ThinVec<T, P> = ThinVec::from_slice_clone;
            Cow<'_, [T]> => ThinVec<T, P> = ThinVec::from_cow;
        }
    }
    [T, P, const N: usize] where [ T:Clone, P: ConstDefault] {
        From {
            &[T; N] => ThinVec<T, P> = ThinVec::from_slice_clone;
            &mut [T; N] => ThinVec<T, P> = ThinVec::from_slice_clone;
        }
    }

    [T, P, const N: usize] where [P: ConstDefault] {
        From {
            [T; N] => ThinVec<T, P> = ThinVec::from_array;
        }
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
