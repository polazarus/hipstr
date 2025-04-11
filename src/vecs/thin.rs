//! Thin vector implementation.
#![allow(unused)]

use alloc::alloc::{alloc, dealloc, handle_alloc_error, realloc, Layout};
use alloc::vec::Vec;
use core::marker::PhantomData;
use core::mem::MaybeUninit;
use core::ops::{Bound, Range, RangeBounds};
use core::ptr::NonNull;
use core::{cmp, fmt, mem, ops, panic, ptr, slice};

use crate::common::{panic_display, RangeError};
use crate::{common, macros};

#[repr(usize)]
#[derive(Default, Clone, Copy, Debug)]
pub enum Reserved {
    #[default]
    Reserved = 0,
}

/// A guard that drops the initialized elements of a slice.
struct SliceGuard<T> {
    ptr: NonNull<T>,
    initialized: usize,
}

impl<T> Drop for SliceGuard<T> {
    fn drop(&mut self) {
        if mem::needs_drop::<T>() {
            unsafe {
                let slice = slice::from_raw_parts_mut(self.ptr.as_ptr(), self.initialized);
                ptr::drop_in_place(slice);
            }
        }
    }
}

/// A macro to create a [`ThinVec`] with the given elements.
///
/// # Examples
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
        $crate::vecs::ThinVec::new();
    };
    [ $e:expr ; $l:expr ] => {{
        let len = $l;
        let mut vec = $crate::vecs::ThinVec::with_capacity(len);
        vec.extend_with(len, $e);
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

/// A shared thin vector's header.
#[derive(Clone, Copy, Debug)]
#[repr(C)]
pub(super) struct Header<T, P> {
    prefix: P,
    cap: usize,
    len: usize,
    phantom: PhantomData<T>,
}

/// A thin vector, that is, a contiguous growable array type with heap-allocated
/// metadata (prefix, capacity, length) and contents.
///
/// Whereas [`Vec`] is three-word wide, this vector is one-word wide. It
/// consists in a single pointer to a heap-allocated area containing both the
/// capacity, the length, and the actual data.
///
/// `PrefixThinVec` contains an arbitrary additional data before the capacity,
/// `P`.
///
/// [`Vec`]: alloc::vec::Vec
#[repr(transparent)]
pub struct ThinVec<T, P = Reserved>(pub(super) NonNull<Header<T, P>>);

impl<T, P> ThinVec<T, P>
where
    P: Default,
{
    /// Creates a new thin vector from a slice of elements by copying the
    /// elements.
    pub fn from_slice_copy(slice: &[T]) -> Self
    where
        T: Copy,
    {
        let len = slice.len();
        let mut this = Self::with_capacity(len);

        unsafe {
            this.ptr()
                .as_ptr()
                .copy_from_nonoverlapping(slice.as_ptr(), len);
            this.header_mut().len = len;
        };

        this
    }

    pub(crate) fn from_slice_clone(slice: &[T]) -> Self
    where
        T: Clone,
    {
        let len = slice.len();
        let mut this = Self::with_capacity(len);

        unsafe {
            let ptr = this.ptr();
            let mut guard = SliceGuard {
                ptr,
                initialized: 0,
            };

            for i in 0..len {
                ptr.add(i).write(slice[i].clone());
                guard.initialized = i + 1;
            }

            this.header_mut().len = len;
            mem::forget(guard);
        };

        this
    }

    #[inline]
    pub(crate) fn from_array<const N: usize>(array: [T; N]) -> Self {
        let mut this = Self::with_capacity(N);
        unsafe {
            let uninit_array: &mut MaybeUninit<[T; N]> = this.ptr().cast().as_mut();
            uninit_array.write(array);
            this.set_len(N);
            this
        }
    }

    /// Creates a new thin vector with the given prefix.
    #[inline]
    pub fn new() -> Self {
        Self::with_capacity(Self::MINIMAL_CAPACITY)
    }

    /// Creates a new thin vector with the given capacity and prefix. The vector
    /// will be able to hold at least `capacity` elements without reallocating.
    ///
    /// # Panics
    ///
    /// Panics if the capacity overflows.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::PrefixedThinVec;
    /// let vec: PrefixedThinVec<i32, i32> = PrefixedThinVec::with_capacity(0xDEAD_BEEF, 10);
    /// assert!(vec.capacity() >= 10);
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        let capacity = capacity.max(Self::MINIMAL_CAPACITY);
        let layout = Self::layout(capacity).expect("invalid layout: buffer too large");
        let ptr = unsafe { alloc(layout.0) };
        let Some(ptr) = NonNull::new(ptr) else {
            handle_alloc_error(layout.0);
        };
        let mut ptr = ptr.cast();
        let header: &mut Header<_, _> = unsafe { ptr.as_mut() };
        header.prefix = P::default();
        header.cap = capacity;
        header.len = 0;
        Self(ptr)
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
    pub fn split_off(&mut self, at: usize) -> Self
    where
        P: Default,
    {
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
}

impl<T, P> ThinVec<T, P> {
    const MINIMAL_CAPACITY: usize = match size_of::<T>() {
        0 => usize::MAX,
        64.. => 1,
        32.. => 3,   // 32*3 data + 32 header => 128
        n => 32 / n, // max 32 data + 32 header => 64
    };
    const DATA_OFFSET: usize = Self::layout(0).unwrap().1;

    #[inline]
    const fn header(&self) -> &Header<T, P> {
        unsafe { self.0.as_ref() }
    }

    #[inline]
    const unsafe fn header_mut(&mut self) -> &mut Header<T, P> {
        unsafe { self.0.as_mut() }
    }

    /// Returns the capacity of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::ThinVec;
    /// let vec: ThinVec<i32> = ThinVec::with_capacity(10);
    /// assert_eq!(vec.capacity(), 10);
    /// ```
    #[inline]
    #[must_use]
    pub const fn capacity(&self) -> usize {
        self.header().cap
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
        self.header().len
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
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the current prefix associated with this thin vector.
    pub fn prefix(&self) -> &P {
        &self.header().prefix
    }

    #[inline]
    const fn ptr(&self) -> NonNull<T> {
        unsafe { self.0.byte_add(Self::DATA_OFFSET).cast() }
    }

    /// Returns a raw pointer to the vector's first element.
    ///
    /// The caller must ensure that the vector outlives the pointer this
    /// function returns, or else it will end up dangling. Modification of the
    /// vector (e.g. pushing elements) may cause the buffer to be reallocated,
    /// which would also make any pointers to it invalid.
    ///
    /// The caller must also ensure that the memory the pointer (non-transitively) points to
    /// is never written to (except inside an `UnsafeCell`) using this pointer or any pointer
    /// derived from it. If you need to mutate the contents of the slice, use [`as_mut_ptr`].
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
    /// [`as_mut_ptr`]: Vec::as_mut_ptr
    /// [`as_ptr`]: Vec::as_ptr
    /// [`as_non_null`]: Vec::as_non_null
    #[inline]
    pub const fn as_mut_ptr(&mut self) -> *mut T {
        self.ptr().as_ptr()
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
        unsafe { self.as_mut_slice_extended() }
    }

    #[inline]
    #[must_use]
    pub const unsafe fn as_mut_slice_extended<'a>(&mut self) -> &'a mut [T] {
        let ptr = self.ptr().as_ptr();
        unsafe { slice::from_raw_parts_mut(ptr, self.len()) }
    }

    const fn layout(payload: usize) -> Option<(Layout, usize)> {
        let layout = Layout::new::<Header<T, P>>();
        let Ok(arr) = Layout::array::<T>(payload) else {
            return None;
        };
        let Ok((l, o)) = layout.extend(arr) else {
            return None;
        };
        Some((l, o))
    }

    fn current_layout(&self) -> Layout {
        // SAFETY: layout checked at creation
        let (layout, _) = unsafe { Self::layout(self.capacity()).unwrap_unchecked() };
        layout
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
        debug_assert!(new_cap >= self.len());

        let old_cap = self.capacity();

        // SAFETY: layout checked at creation
        let layout = self.current_layout();
        let (new_layout, _) = Self::layout(new_cap).expect("invalid layout: buffer too large");

        let ptr = unsafe { realloc(self.0.cast().as_ptr(), layout, new_layout.size()) };

        let Some(ptr) = NonNull::new(ptr) else {
            handle_alloc_error(layout);
        };

        let mut ptr = ptr.cast();
        let header: &mut Header<_, _> = unsafe { ptr.as_mut() };
        header.cap = new_cap;
        self.0 = ptr;
    }

    /// Forces the length of the vector to `new_len`.
    ///
    /// This is a low-level operation that does not maintain any of the usual
    /// invariants of the type. Normally changing the length of a vector is done
    /// using one of the safe operations instead.
    ///
    /// # Safety
    ///
    /// - `new_len` must be less than or equal to the capacity of the vector.
    /// - The elements at `old_len..new_len` must be initialized.
    pub unsafe fn set_len(&mut self, new_len: usize) {
        debug_assert!(new_len <= self.capacity());
        unsafe {
            self.header_mut().len = new_len;
        }
    }

    /// Reserves the minimum capacity for at least `additional` more elements to
    /// be inserted in the given `Thin<T, P>`. Unlike [`reserve`], this will not
    /// intentionally over-allocate to potentially avoid frequent reallocations.
    ///
    /// Prefer [`reserve`] if future insertions are expected.
    ///
    /// [`reserve`]: Self::reserve
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
    /// Prefer [`reserve_exact`] if the exact amount of elements to be added is known.
    ///
    /// [`reserve_exact`]: Self::reserve_exact
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

    /// Shortens the vector, keeping only the first `len` elements and dropping
    /// the rest.
    ///
    /// If `len` is greater than or equal to the vector's current length, it
    /// does nothing.
    ///
    /// Note that this method has no effect on the allocated capacity of the
    /// vector.
    pub fn truncate(&mut self, len: usize) {
        if len > self.len() {
            return;
        }
        // get a raw pointer to the elements to drop
        let ptr = &raw mut self.as_mut_slice()[len..];

        // SAFETY:
        // * `ptr` is a pointer to the elements to drop
        // * `len` of the vector is shrunk before calling `drop_in_place`
        //    so that no value can be dropped twice if the call to
        //    `drop_in_place` panics
        unsafe {
            self.set_len(len);
            ptr::drop_in_place(ptr);
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
        let len = self.len();
        if len == 0 {
            return None;
        }

        // SAFETY: the length is checked above
        unsafe {
            let value = self.ptr().add(len - 1).read();
            self.header_mut().len = len - 1;
            Some(value)
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
    pub fn remove(&mut self, index: usize) -> T {
        let len = self.len();
        assert!(index < len, "index out of bounds");

        // SAFETY: index is checked above
        unsafe {
            let ptr = self.ptr().add(index);
            let value = ptr.read();
            ptr.copy_from(ptr.add(1), len - index - 1);
            self.set_len(len - 1);
            value
        }
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
        let len = self.len();
        assert!(index < len, "index out of bounds");

        // SAFETY: index is checked above
        unsafe {
            let last = self.ptr().add(len - 1);
            let current = self.ptr().add(index);

            // read the value
            let value = current.read();

            // NOTE replace even if index == len - 1
            current.copy_from(last, 1);
            self.set_len(len - 1);

            value
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
    pub fn append<Q>(&mut self, other: &mut ThinVec<T, Q>) {
        unsafe {
            self.append_raw(other.ptr(), other.len());
            other.set_len(0);
        }
    }

    /// Moves all the elements of some `other` [`Vec`] into `self`, leaving `other` empty.
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
    /// let mut w = vec![4, 5, 6];
    /// v.append_vec(&mut w);
    /// assert_eq!(v, [1, 2, 3, 4, 5, 6]);
    /// assert_eq!(w, []);
    /// ```
    pub fn append_vec(&mut self, other: &mut Vec<T>) {
        unsafe {
            self.reserve(other.len());
            let src = NonNull::new_unchecked(other.as_mut_ptr());
            self.append_raw(src, other.len());
            other.set_len(0);
        }
    }

    unsafe fn append_raw(&mut self, ptr: NonNull<T>, len: usize) {
        self.reserve(len);
        let old_len = self.len();
        unsafe {
            let dst = self.ptr().add(old_len);
            dst.copy_from(ptr, len);
            self.set_len(old_len + len);
        }
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
        let slice: *mut [T] = self.as_mut_slice();

        // SAFETY:
        // - `slice` is a valid slice
        // - the slice cannot not accessed after the call to `drop_in_place`
        //   even if an element's drop panics because the length is set to 0
        //   before the call to `drop_in_place`
        unsafe {
            self.set_len(0);
            ptr::drop_in_place(slice);
        }
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
    pub fn spare_capacity_mut(&mut self) -> &mut [MaybeUninit<T>] {
        let len = self.len();
        let cap = self.capacity();

        // SAFETY: the slice is within the bounds of the buffer
        unsafe {
            let ptr = self.ptr().add(len).cast().as_ptr();
            slice::from_raw_parts_mut(ptr, cap - len)
        }
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
    pub fn drain(&mut self, range: impl RangeBounds<usize>) -> Drain<'_, T, P> {
        self.try_drain(range).unwrap_or_else(panic_display)
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
    /// assert_eq!(result.unwrap_err(), RangeError::EndOutOfBounds { end: 8, len: 5 });
    /// ```
    pub fn try_drain(
        &mut self,
        range: impl RangeBounds<usize>,
    ) -> Result<Drain<'_, T, P>, RangeError> {
        let len = self.len();
        let range = common::range(range, len)?;
        let Range { start, end } = range;

        // SAFETY: start < len
        //
        // if drain is leaked, the length is at least memory safe but will leak
        // the tail
        unsafe {
            self.set_len(start);
        }

        Ok(Drain {
            vec: self,
            range: start..end,
            tail_start: end,
            tail_len: len - end,
        })
    }

    pub fn resize(&mut self, new_len: usize, value: T)
    where
        T: Clone,
    {
        let len = self.len();
        if new_len > len {
            self.extend_with(new_len - len, value);
        } else {
            self.truncate(new_len);
        }
    }

    pub fn extend_from_within<R>(&mut self, range: impl RangeBounds<usize>)
    where
        T: Clone,
    {
        self.try_extend_from_within(range)
            .unwrap_or_else(common::panic_display)
    }

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
                self.ptr().add(j).write(self.ptr().add(i).as_ref().clone());
                self.set_len(j + 1);
            }
        }
        Ok(())
    }

    pub fn extend_with(&mut self, n: usize, value: T)
    where
        T: Clone,
    {
        let len = self.len();
        self.reserve(n);
        unsafe {
            for i in 1..n {
                self.ptr().add(len + i).write(value.clone());
                self.set_len(len + i + 1);
            }
            if n > 0 {
                self.ptr().add(len).write(value);
                self.set_len(len + 1);
            }
        }
    }

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
}

impl<T, P> ops::Deref for ThinVec<T, P> {
    type Target = [T];

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<T, P> ops::DerefMut for ThinVec<T, P> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut_slice()
    }
}

impl<T, C> Drop for ThinVec<T, C> {
    fn drop(&mut self) {
        unsafe {
            if mem::needs_drop::<T>() {
                ptr::drop_in_place(self.as_mut_slice());
            }
            let layout = self.current_layout();
            unsafe { dealloc(self.0.cast().as_ptr(), layout) };
        }
    }
}

macros::trait_impls! {
    [T, P] where [T: Clone, P: Default] {
        From {
            &[T] => ThinVec<T, P> = ThinVec::from_slice_clone;
        }
    }

    [T, P, const N: usize] where [P: Default] {
        From {
            [T; N] => ThinVec<T, P> = ThinVec::from_array;
        }
    }

    [T, P] where [T: core::fmt::Debug] {
        Debug {
            ThinVec<T, P>;
        }
    }

    [T, P] where [T: PartialEq] {
        PartialEq {
            ThinVec<T, P>;
        }
    }
    [T, U, P] where [T: PartialEq<U>] {
        PartialEq {
            [T], ThinVec<U, P>;
            ThinVec<T, P>, [U];

            &[T], ThinVec<U, P>;
            ThinVec<T, P>, &[U];

            Vec<T>, ThinVec<U, P>;
            ThinVec<T, P>, Vec<U>;
        }
    }
    [T, U, P, const N: usize] where [T: PartialEq<U>] {
        PartialEq {
            [T; N], ThinVec<U, P>;
            ThinVec<T, P>, [U; N];
        }
    }

    [T, P] where [T: PartialOrd] {
        PartialOrd {
            ThinVec<T, P>;
        }
    }

    [T, P] where [T: PartialOrd] {
        PartialOrd {
            Vec<T>, ThinVec<T, P>;
            ThinVec<T, P>, Vec<T>;

            &[T], ThinVec<T, P>;
            ThinVec<T, P>, &[T];
        }
    }

    [T, P, const N: usize] where [T: PartialOrd] {
        PartialOrd {
            [T; N], ThinVec<T, P>;
            ThinVec<T, P>, [T; N];
        }
    }
}

/// A draining iterator for thin vectors.
///
/// This `struct` is created by [`PrefixedThinVec::drain`].
/// See its documentation for more.
///
/// # Example
///
/// ```
/// use hipstr::thin_vec;
/// use hipstr::vecs::thin::Drain;
/// let mut v = thin_vec![0, 1, 2];
/// let iter: Drain<_> = v.drain(..);
/// ```
pub struct Drain<'a, T, P> {
    vec: &'a mut ThinVec<T, P>,
    range: Range<usize>,
    tail_start: usize,
    tail_len: usize,
}

impl<'a, T, P> Drain<'a, T, P> {
    /// Returns the remaining items of this iterator as a slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::thin_vec;
    /// let mut v = thin_vec!['a', 'b', 'c'];
    /// let mut drain = v.drain(..);
    /// assert_eq!(drain.as_slice(), &['a', 'b', 'c']);
    /// let _ = drain.next().unwrap();
    /// assert_eq!(drain.as_slice(), &['b', 'c']);
    /// ```
    #[must_use]
    pub fn as_slice(&self) -> &[T] {
        unsafe {
            slice::from_raw_parts(
                self.vec.ptr().add(self.range.start).as_ptr(),
                self.range.len(),
            )
        }
    }
}

impl<'a, T, P> Iterator for Drain<'a, T, P> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        let index = self.range.next()?;
        let value = unsafe { self.vec.ptr().add(index).read() };
        Some(value)
    }
}

impl<T: fmt::Debug, P> fmt::Debug for Drain<'_, T, P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Drain").field(&self.as_slice()).finish()
    }
}

impl<'a, T, P> Drop for Drain<'a, T, P> {
    fn drop(&mut self) {
        let ptr = self.vec.ptr();

        if mem::needs_drop::<T>() {
            unsafe {
                let slice = slice::from_raw_parts_mut(
                    self.vec.ptr().add(self.range.start).as_ptr(),
                    self.range.len(),
                );
                ptr::drop_in_place(slice);
            }
        }

        let start = self.vec.len();
        // SAFETY: type invariant
        unsafe {
            ptr.add(start)
                .copy_from(ptr.add(self.tail_start), self.tail_len);
            self.vec.set_len(start + self.tail_len);
        }
    }
}

#[cfg(test)]
mod unshared_tests {
    use alloc::boxed::Box;

    use crate::vecs::ThinVec;
    use crate::Arc;

    #[test]
    fn new() {
        let v = ThinVec::<()>::with_capacity(0);
        assert_eq!(v.capacity(), usize::MAX);
        assert_eq!(v.len(), 0);

        let v = ThinVec::<i32>::with_capacity(10);
        assert!(v.capacity() >= 10);
        assert_eq!(v.len(), 0);

        let v = ThinVec::<i32>::new();
        assert_eq!(v.len(), 0);
    }

    #[test]
    fn from_array() {
        let array: [_; 10] = core::array::from_fn(|i| Box::new(i));
        let _ = ThinVec::from_array(array);
    }

    #[test]
    fn push_drop() {
        struct S<'a>(&'a mut i32);
        impl Drop for S<'_> {
            fn drop(&mut self) {
                *self.0 += 1;
            }
        }
        let mut a = 1;
        let mut b = 2;
        let mut c = 3;

        {
            let mut v = ThinVec::new();
            v.push(S(&mut a));
            v.push(S(&mut b));
            v.push(S(&mut c));
            assert_eq!(v.len(), 3);
        }

        assert_eq!(a, 2);
        assert_eq!(b, 3);
        assert_eq!(c, 4);
    }

    #[test]
    fn push() {
        let mut v = ThinVec::new();
        v.push(1);
        v.push(2);
        v.push(3);
        assert_eq!(v.as_slice(), [1, 2, 3]);
        assert_eq!(v.pop(), Some(3));
        assert_eq!(v.pop(), Some(2));
        assert_eq!(v.pop(), Some(1));
        assert_eq!(v.pop(), None);
    }

    #[test]
    fn from_slice_copy() {
        let array: [_; 10] = core::array::from_fn(|i| i);
        let v = ThinVec::from_slice_copy(&array);
        assert_eq!(v.as_slice(), array);
    }

    #[test]
    fn from_slice_clone() {
        let array: [_; 10] = core::array::from_fn(|i| i);
        let v = ThinVec::from_slice_clone(&array);
        assert_eq!(v.as_slice(), array);

        let array: [_; 10] = core::array::from_fn(|i| Box::new(i));
        let v = ThinVec::from_slice_clone(&array);
        assert_eq!(v.as_slice(), array);
    }

    #[test]
    #[cfg(feature = "std")]
    fn from_slice_clone_panic() {
        static CLONE_COUNT: std::sync::Mutex<usize> = std::sync::Mutex::new(0);
        static DROP_COUNT: std::sync::Mutex<usize> = std::sync::Mutex::new(0);

        struct S(bool);
        impl Drop for S {
            fn drop(&mut self) {
                // witness the drop
                *DROP_COUNT.lock().unwrap() += 1;
            }
        }
        impl Clone for S {
            fn clone(&self) -> Self {
                *CLONE_COUNT.lock().unwrap() += 1;
                if self.0 {
                    panic!();
                }
                Self(self.0)
            }
        }

        *CLONE_COUNT.lock().unwrap() = 0;
        *DROP_COUNT.lock().unwrap() = 0;

        let array: [_; 4] = [false, false, true, false].map(S);
        let r = std::panic::catch_unwind(|| {
            let _ = ThinVec::from(array.as_slice());
        })
        .unwrap_err();

        assert_eq!(*CLONE_COUNT.lock().unwrap(), 3);
        assert_eq!(*DROP_COUNT.lock().unwrap(), 2);
    }

    #[test]
    #[should_panic]
    fn with_capacity_overflow() {
        let _ = ThinVec::<u8>::with_capacity(isize::MAX as usize);
    }

    #[test]
    #[should_panic]
    fn reserve_overflow() {
        let mut v = ThinVec::<u8>::new();
        v.reserve(isize::MAX as usize);
    }

    #[test]
    #[should_panic]
    fn reserve_exact_overflow() {
        let mut v = ThinVec::<u8>::new();
        v.reserve_exact(isize::MAX as usize);
    }

    #[test]
    fn truncate() {
        let mut v = thin_vec![1, 2, 3];
        v.truncate(4);
        assert_eq!(v.as_slice(), &[1, 2, 3]);
        v.truncate(1);
        assert_eq!(v.as_slice(), &[1]);
        v.truncate(0);
        assert!(v.is_empty());
    }

    #[test]
    fn insert() {
        let mut v = thin_vec!['a', 'c', 'd'];
        v.insert(1, 'b');
        assert_eq!(v, ['a', 'b', 'c', 'd']);
        v.insert(4, 'e');
        assert_eq!(v, ['a', 'b', 'c', 'd', 'e']);
    }

    #[test]
    #[should_panic]
    fn insert_out_of_bound() {
        let mut v = thin_vec!['a', 'b', 'c'];
        v.insert(4, 'e');
    }

    #[test]
    fn drain() {
        let mut v = thin_vec![1, 2, 3, 4, 5];
        {
            let mut d = v.drain(1..4);
            assert_eq!(d.as_slice(), &[2, 3, 4]);
            assert_eq!(d.next(), Some(2));
            assert_eq!(d.next(), Some(3));
            assert_eq!(d.next(), Some(4));
            assert_eq!(d.next(), None);
        }
        assert_eq!(v.as_slice(), &[1, 5]);
    }

    #[test]
    fn drain_dst() {
        let mut v = thin_vec![(), (), ()];
        assert_eq!(v.drain(..).count(), 3);
        assert_eq!(v.len(), 0);

        let mut v = thin_vec![(), (), ()];
        assert_eq!(v.drain(1..2).count(), 1);
        assert_eq!(v.len(), 2);
    }

    #[test]
    fn drain_drop() {
        struct S<'a>(&'a mut i32);
        impl Drop for S<'_> {
            fn drop(&mut self) {
                *self.0 += 1;
            }
        }
        let mut a = 1;
        let mut b = 2;
        let mut c = 3;

        {
            let mut v = thin_vec![S(&mut a), S(&mut b), S(&mut c)];
            let mut d = v.drain(..);
            let _ = d.next();
        }

        assert_eq!(a, 2);
        assert_eq!(b, 3);
        assert_eq!(c, 4);
    }

    #[test]
    fn drain_dst_forget() {
        let mut v = thin_vec![(), (), ()];
        core::mem::forget(v.drain(..));
        assert_eq!(v.len(), 0);

        let mut v = thin_vec![(), (), ()];
        core::mem::forget(v.drain(1..2));
        assert_eq!(v.len(), 1);
    }

    #[test]
    fn split_off() {
        let mut v = thin_vec![1, 2, 3, 4, 5];
        let w = v.split_off(2);
        assert_eq!(v.as_slice(), &[1, 2]);
        assert_eq!(w.as_slice(), &[3, 4, 5]);

        let mut v = thin_vec![1, 2, 3];
        let w = v.split_off(0);
        assert!(v.is_empty());
        assert_eq!(w.as_slice(), &[1, 2, 3]);

        let mut v = thin_vec![1, 2, 3];
        let w = v.split_off(3);
        assert_eq!(v.as_slice(), &[1, 2, 3]);
        assert!(w.is_empty());
    }

    #[test]
    #[should_panic(expected = "index out of bounds")]
    fn split_off_bad_index() {
        let mut v = thin_vec![1, 2, 3];
        v.split_off(4);
    }
}
