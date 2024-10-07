//! Bytes.
//!
//! This module provides the [`HipByt`] type as well as the associated helper and error types.

use core::borrow::Borrow;
use core::error::Error;
use core::hash::Hash;
use core::mem::MaybeUninit;
use core::ops::{Bound, Deref, DerefMut, Range, RangeBounds};
use core::ptr;

use super::raw::Raw;
use crate::alloc::fmt;
use crate::alloc::vec::Vec;
use crate::raw::try_range_of;
use crate::{Backend, ThreadSafe};

mod cmp;
mod convert;

#[cfg(feature = "serde")]
pub mod serde;

#[cfg(feature = "bstr")]
mod bstr;

#[cfg(test)]
mod tests;

#[cfg(feature = "bstr")]
type Owned = ::bstr::BString;

#[cfg(not(feature = "bstr"))]
type Owned = Vec<u8>;

#[cfg(feature = "bstr")]
type Slice = ::bstr::BStr;

#[cfg(not(feature = "bstr"))]
type Slice = [u8];

/// Smart bytes, i.e. cheaply clonable and sliceable byte string.
///
/// # Examples
///
/// You can create a `HipStr` from a [byte slice (&`[u8]`)][slice], an owned byte string
/// ([`Vec<u8>`], [`Box<[u8]>`][Box]), or a clone-on-write smart pointer
/// ([`Cow<[u8]>`][std::borrow::Cow]) with [`From`]:
///
/// ```
/// # use hipstr::HipByt;
/// let hello = HipByt::from(b"Hello".as_slice());
/// ```
///
/// When possible, `HipStr::from` takes ownership of the underlying buffer:
///
/// ```
/// # use hipstr::HipByt;
/// let vec = Vec::from(b"World".as_slice());
/// let world = HipByt::from(vec);
/// ```
///
/// To borrow a string slice, you can also use the no-copy constructor [`HipByt::borrowed`]:
///
/// ```
/// # use hipstr::HipByt;
/// let hello = HipByt::borrowed(b"Hello, world!");
/// ```
///
/// # Representations
///
/// `HipByt` has three possible internal representations:
///
/// * borrow
/// * inline string
/// * shared heap allocated string
#[repr(transparent)]
pub struct HipByt<'borrow, B = ThreadSafe>(pub(crate) Raw<'borrow, B>)
where
    B: Backend;

impl<'borrow, B> HipByt<'borrow, B>
where
    B: Backend,
{
    /// Creates an empty `HipByt`.
    ///
    /// Function provided for [`Vec::new`] replacement.
    ///
    /// # ⚠️ Warning!
    ///
    /// The used representation of the empty string is unspecified.
    /// It may be *borrowed* or *inlined* but will never be allocated.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let s = HipByt::new();
    /// ```
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self(Raw::empty())
    }

    /// Creates a new `HipByt` with the given capacity.
    ///
    /// The underlying representation is not **normalized**.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let mut s = HipByt::with_capacity(42);
    /// let p = s.as_ptr();
    /// for _ in 0..42 {
    ///     s.push(b'*');
    /// }
    /// assert_eq!(s, [b'*'; 42]);
    /// assert_eq!(s.as_ptr(), p);
    /// ```
    #[inline]
    #[must_use]
    pub fn with_capacity(cap: usize) -> Self {
        Self(Raw::with_capacity(cap))
    }

    /// Creates a new `HipByt` from a byte slice.
    /// No heap allocation is performed.
    /// **The slice is not copied.**
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let b = HipByt::borrowed(b"hello\0");
    /// assert_eq!(b.len(), 6);
    /// ```
    #[must_use]
    pub const fn borrowed(bytes: &'borrow [u8]) -> Self {
        Self(Raw::borrowed(bytes))
    }

    /// Returns `true` if this `HipByt` uses the inline representation, `false` otherwise.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let s = HipByt::borrowed(b"hello");
    /// assert!(!s.is_inline());
    ///
    /// let s = HipByt::from(b"hello");
    /// assert!(s.is_inline());
    ///
    /// let s = HipByt::from(b"hello".repeat(10));
    /// assert!(!s.is_inline());
    /// ```
    #[inline]
    #[must_use]
    pub const fn is_inline(&self) -> bool {
        self.0.is_inline()
    }

    /// Returns `true` if this `HipByt` is a slice borrow, `false` otherwise.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let s = HipByt::borrowed(b"hello");
    /// assert!(s.is_borrowed());
    ///
    /// let s = HipByt::from(b"hello");
    /// assert!(!s.is_borrowed());
    ///
    /// let s = HipByt::from(b"hello".repeat(10));
    /// assert!(!s.is_borrowed());
    /// ```
    #[inline]
    #[must_use]
    pub const fn is_borrowed(&self) -> bool {
        self.0.is_borrowed()
    }

    /// Returns `true` if this `HipByt` is a shared heap-allocated byte sequence, `false` otherwise.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let s = HipByt::borrowed(b"hello");
    /// assert!(!s.is_allocated());
    ///
    /// let s = HipByt::from(b"hello");
    /// assert!(!s.is_allocated());
    ///
    /// let s = HipByt::from(b"hello".repeat(10));
    /// assert!(s.is_allocated());
    /// ```
    #[inline]
    #[must_use]
    pub const fn is_allocated(&self) -> bool {
        self.0.is_allocated()
    }

    /// Converts `self` into a borrowed slice if this `HipByt` is backed by a borrow.
    ///
    /// # Errors
    ///
    /// Returns `Err(self)` if this `HipByt` is not a borrow.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// static SEQ: &[u8] = &[1 ,2, 3];
    /// let s = HipByt::borrowed(SEQ);
    /// let c = s.into_borrowed();
    /// assert_eq!(c, Ok(SEQ));
    /// assert!(std::ptr::eq(SEQ, c.unwrap()));
    /// ```
    #[inline]
    pub fn into_borrowed(self) -> Result<&'borrow [u8], Self> {
        self.0.into_borrowed().map_err(Self)
    }

    /// Returns the length of this `HipByt`.
    ///
    /// # Example
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let a = HipByt::borrowed(b"\xDE\xAD\xBE\xEF");
    /// assert_eq!(a.len(), 4);
    /// ```
    #[inline]
    #[must_use]
    pub const fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns `true` if this `HipByt` has a length of zero, and `false` otherwise.
    ///
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let a = HipByt::new();
    /// assert!(a.is_empty());
    ///
    /// let b = HipByt::borrowed(b"ab");
    /// assert!(!b.is_empty());
    /// ```
    #[inline]
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.0.len() == 0
    }

    /// Extracts a slice of the entire `HipByt`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let s = HipByt::from(b"foobar");
    ///
    /// assert_eq!(b"foobar", s.as_slice());
    /// ```
    #[inline]
    #[must_use]
    pub const fn as_slice(&self) -> &[u8] {
        self.0.as_slice()
    }

    /// Extracts a mutable slice of the entire `HipByt` if possible.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let mut s = HipByt::from(b"foo");
    /// let slice = s.as_mut_slice().unwrap();
    /// slice.copy_from_slice(b"bar");
    /// assert_eq!(b"bar", slice);
    /// ```
    #[inline]
    #[must_use]
    pub fn as_mut_slice(&mut self) -> Option<&mut [u8]> {
        self.0.as_mut_slice()
    }

    /// Extracts a mutable slice of the entire `HipByt` changing the
    /// representation (and thus _potentially reallocating_) if the current
    /// representation cannot be mutated.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let mut s = HipByt::borrowed(b"foo");
    /// let slice = s.to_mut_slice(); // change the representation to inline
    /// slice.copy_from_slice(b"bar");
    /// assert_eq!(b"bar", slice);
    /// ```
    #[inline]
    #[doc(alias = "make_mut")]
    pub fn to_mut_slice(&mut self) -> &mut [u8] {
        self.0.make_unique();
        // SAFETY: `make_unique` above ensures that it is uniquely owned
        unsafe { self.0.as_mut_slice_unchecked() }
    }

    /// Extracts a slice as its own `HipByt`.
    ///
    /// # Panics
    ///
    /// Panics if the range is invalid: out of bounds or not at char boundaries.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let a = HipByt::from(b"abc");
    /// assert_eq!(a.slice(0..2), HipByt::from(b"ab"));
    /// ```
    #[must_use]
    #[track_caller]
    pub fn slice(&self, range: impl RangeBounds<usize>) -> Self {
        match self.try_slice(range) {
            Ok(result) => result,
            Err(err) => panic!("{}", err),
        }
    }

    /// Returns a `HipByt` of a range of bytes in this `HipByt`, if the range is
    /// valid.
    ///
    /// # Errors
    ///
    /// This function will return an error if the range is invalid.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let a = HipByt::from(b"abc");
    /// assert_eq!(a.try_slice(0..2), Ok(HipByt::from(b"ab")));
    /// assert!(a.try_slice(0..4).is_err());
    /// ```
    pub fn try_slice(&self, range: impl RangeBounds<usize>) -> Result<Self, SliceError<B>> {
        let range = simplify_range(range, self.len())
            .map_err(|(start, end, kind)| SliceError::new(kind, start, end, self))?;
        let slice = unsafe { self.0.slice_unchecked(range) };
        Ok(Self(slice))
    }

    /// Extracts a slice as its own `HipByt`.
    ///
    /// # Safety
    ///
    /// `range` must be a equivalent to some `a..b` with `a <= b <= len`.
    ///
    /// Panics in debug mode. UB in release mode.
    #[must_use]
    pub unsafe fn slice_unchecked(&self, range: impl RangeBounds<usize>) -> Self {
        let start = match range.start_bound() {
            Bound::Excluded(&n) => n + 1,
            Bound::Included(&n) => n,
            Bound::Unbounded => 0,
        };
        let end = match range.end_bound() {
            Bound::Excluded(&n) => n,
            Bound::Included(&n) => n + 1,
            Bound::Unbounded => self.len(),
        };
        Self(unsafe { self.0.slice_unchecked(start..end) })
    }

    /// Extracts a slice as its own `HipByt` based on the given subslice `&[u8]`.
    ///
    /// # Panics
    ///
    /// Panics if `slice` is not part of `self`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let a = HipByt::from(b"abc");
    /// let sl = &a[0..2];
    /// assert_eq!(a.slice_ref(sl), HipByt::from(b"ab"));
    /// ```
    #[must_use]
    #[track_caller]
    pub fn slice_ref(&self, slice: &[u8]) -> Self {
        let Some(result) = self.try_slice_ref(slice) else {
            panic!("slice {slice:p} is not a part of {self:p}")
        };
        result
    }

    /// Extracts a slice as its own `HipByt` based on the given subslice `&[u8]`.
    ///
    /// # Safety
    ///
    /// The slice MUST be a part of this `HipByt`
    #[must_use]
    pub unsafe fn slice_ref_unchecked(&self, slice: &[u8]) -> Self {
        Self(unsafe { self.0.slice_ref_unchecked(slice) })
    }

    /// Returns a slice as it own `HipByt` based on the given subslice `&[u8]`.
    ///
    /// # Errors
    ///
    /// Returns `None` if `slice` is not a part of `self`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let a = HipByt::from(b"abc");
    /// let sl = &a[0..2];
    /// assert_eq!(a.try_slice_ref(sl), Some(HipByt::from(b"ab")));
    /// assert!(a.try_slice_ref(b"z").is_none());
    /// ```
    #[must_use]
    pub fn try_slice_ref(&self, range: &[u8]) -> Option<Self> {
        let slice = range;
        let range = try_range_of(self.0.as_slice(), slice)?;
        let raw = unsafe { self.0.slice_unchecked(range) };
        Some(Self(raw))
    }

    /// Returns the maximal length for inline byte sequence.
    #[inline]
    #[must_use]
    pub const fn inline_capacity() -> usize {
        Raw::<B>::inline_capacity()
    }

    /// Returns the total number of bytes the backend can hold.
    ///
    /// # Example
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let mut vec: Vec<u8> = Vec::with_capacity(42);
    /// vec.extend(0..30);
    /// let bytes = HipByt::from(vec);
    /// assert_eq!(bytes.len(), 30);
    /// assert_eq!(bytes.capacity(), 42);
    ///
    /// let start = bytes.slice(0..29);
    /// assert_eq!(bytes.capacity(), 42); // same backend, same capacity
    /// ```
    #[inline]
    #[must_use]
    pub fn capacity(&self) -> usize {
        self.0.capacity()
    }

    /// Converts `self` into a [`Vec`] without clone or allocation if possible.
    ///
    /// # Errors
    ///
    /// Returns `Err(self)` if it is impossible to take ownership of the vector
    /// backing this `HipByt`.
    #[inline]
    pub fn into_vec(self) -> Result<Vec<u8>, Self> {
        self.0.into_vec().map_err(Self)
    }

    /// Returns a mutable handle to the underlying [`Vec`].
    ///
    /// This operation may reallocate a new vector if either:
    ///
    /// - the representation is not an allocated buffer (inline array or static borrow),
    /// - the underlying buffer is shared.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hipstr::HipByt;
    /// let mut s = HipByt::borrowed(b"abc");
    /// {
    ///     let mut r = s.mutate();
    ///     r.extend_from_slice(b"def");
    ///     assert_eq!(r.as_slice(), b"abcdef");
    /// }
    /// assert_eq!(s, b"abcdef");
    /// ```
    #[inline]
    #[must_use]
    pub fn mutate(&mut self) -> RefMut<'_, 'borrow, B> {
        let owned = self.0.take_vec();

        #[cfg(feature = "bstr")]
        let owned = owned.into();

        RefMut {
            result: self,
            owned,
        }
    }

    /// Shortens this `HipByt` to the specified length.
    ///
    /// If the new length is greater than the current length, this has no effect.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let mut a = HipByt::from(b"abc");
    /// a.truncate(1);
    /// assert_eq!(a, b"a");
    /// ```
    #[inline]
    pub fn truncate(&mut self, new_len: usize) {
        self.0.truncate(new_len);
    }

    /// Truncates this `HipByt`, removing all contents.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let mut s = HipByt::from(b"foo");
    ///
    /// s.clear();
    ///
    /// assert!(s.is_empty());
    /// assert_eq!(0, s.len());
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        self.0.truncate(0);
    }

    /// Removes the last element from this `HipByt` and returns it, or [`None`]
    /// if it is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipByt;
    ///
    /// let mut h = HipByt::from(&[1, 2, 3]);
    /// assert_eq!(h.pop(), Some(3));
    /// assert_eq!(h, [1, 2]);
    /// ```
    pub fn pop(&mut self) -> Option<u8> {
        let len = self.len();
        if len == 0 {
            None
        } else {
            let result = unsafe { *self.as_slice().get_unchecked(len - 1) };
            self.truncate(len - 1);
            Some(result)
        }
    }

    /// Appends all bytes of the slice to this `HipByt`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let mut bytes = HipByt::from(b"abc");
    /// bytes.push_slice(b"123");
    /// assert_eq!(bytes, b"abc123");
    /// ```
    #[inline]
    #[doc(alias = "extend_from_slice")]
    pub fn push_slice(&mut self, addition: &[u8]) {
        self.0.push_slice(addition);
    }

    /// Appends a byte to this `HipByt`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let mut bytes = HipByt::from(b"abc");
    /// bytes.push(b'1');
    /// bytes.push(b'2');
    /// bytes.push(b'3');
    /// assert_eq!(bytes, b"abc123");
    /// ```
    #[inline]
    pub fn push(&mut self, value: u8) {
        self.0.push_slice(&[value]);
    }

    /// Makes the data owned, copying it if the data is actually borrowed.
    ///
    /// Returns a new `HipByt` consuming this one.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let v = vec![42; 42];
    /// let h = HipByt::borrowed(&v[..]);
    /// // drop(v); // err, v is borrowed
    /// let h = h.into_owned();
    /// drop(v); // ok
    /// assert_eq!(h, [42; 42]);
    /// ```
    #[must_use]
    pub fn into_owned(self) -> HipByt<'static, B> {
        HipByt(self.0.into_owned())
    }

    /// Shrinks the capacity of the vector as much as possible.
    ///
    /// The capacity will remain at least as large as the actual length of the
    /// vector.
    ///
    /// No-op if the representation is not allocated.
    ///
    /// # Representation stability
    ///
    /// The allocated representation may change to *inline* if the required
    /// capacity is smaller thant the inline capacity.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hipstr::HipByt;
    /// let mut s = HipByt::with_capacity(100);
    /// s.push_slice(b"abc");
    /// s.shrink_to_fit();
    /// assert_eq!(s.capacity(), HipByt::inline_capacity());
    /// ```
    pub fn shrink_to_fit(&mut self) {
        self.0.shrink_to(self.len());
    }

    /// Shrinks the capacity of the vector with a lower bound.
    ///
    /// The capacity will remain at least as large as the given bound and the
    /// actual length of the vector.
    ///
    /// No-op if the representation is not allocated.
    ///
    /// # Representation stability
    ///
    /// The representation may change to inline if the required capacity is
    /// smaller than the inline capacity.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hipstr::HipByt;
    /// let mut s = HipByt::with_capacity(100);
    /// s.shrink_to(4);
    /// assert_eq!(s.capacity(), HipByt::inline_capacity());
    /// ```
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.0.shrink_to(min_capacity);
    }

    pub(crate) fn take_vec(&mut self) -> Vec<u8> {
        self.0.take_vec()
    }

    #[cfg(test)]
    #[inline]
    pub(crate) const fn is_normalized(&self) -> bool {
        self.0.is_normalized()
    }

    /// Returns a new `HipByt` containing a copy of this slice where each byte
    /// is mapped to its ASCII lower case equivalent.
    ///
    /// ASCII letters 'A' to 'Z' are mapped to 'a' to 'z',
    /// but non-ASCII letters are unchanged.
    ///
    /// To lowercase the value in-place, use [`make_ascii_lowercase`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hipstr::HipByt;
    /// let h = HipByt::from(b"!abc\0OK\x80");
    /// let h2 = h.to_ascii_lowercase();
    /// assert_eq!(h2, b"!abc\0ok\x80");
    /// ```
    ///
    /// [`make_ascii_lowercase`]: Self::make_ascii_lowercase
    #[inline]
    #[must_use]
    pub fn to_ascii_lowercase(&self) -> Self {
        let mut other = self.clone();
        other.to_mut_slice().make_ascii_lowercase();
        other
    }

    /// Converts this slice to its ASCII lower case equivalent in-place.
    ///
    /// ASCII letters 'A' to 'Z' are mapped to 'a' to 'z',
    /// but non-ASCII letters are unchanged.
    ///
    /// To return a new lowercased value without modifying the existing one, use
    /// [`to_ascii_lowercase`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hipstr::HipByt;
    /// let mut h = HipByt::from(b"!abc\0OK\x80");
    /// h.make_ascii_lowercase();
    /// assert_eq!(h, b"!abc\0ok\x80");
    /// ```
    ///
    /// [`to_ascii_lowercase`]: Self::to_ascii_lowercase
    #[inline]
    pub fn make_ascii_lowercase(&mut self) {
        self.to_mut_slice().make_ascii_lowercase();
    }

    /// Returns a new `HipByt` containing a copy of this slice where each byte
    /// is mapped to its ASCII lower case equivalent.
    ///
    /// ASCII letters 'A' to 'Z' are mapped to 'a' to 'z',
    /// but non-ASCII letters are unchanged.
    ///
    /// To lowercase the value in-place, use [`make_ascii_lowercase`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hipstr::HipByt;
    /// let h = HipByt::from(b"!abc\0OK\x80");
    /// let h2: HipByt = h.to_ascii_uppercase();
    /// assert_eq!(h2, b"!ABC\0OK\x80");
    /// ```
    ///
    /// [`make_ascii_lowercase`]: Self::make_ascii_lowercase
    #[inline]
    #[must_use]
    pub fn to_ascii_uppercase(&self) -> Self {
        let mut other = self.clone();
        other.to_mut_slice().make_ascii_uppercase();
        other
    }

    /// Converts this slice to its ASCII upper case equivalent in-place.
    ///
    /// ASCII letters 'a' to 'z' are mapped to 'A' to 'Z',
    /// but non-ASCII letters are unchanged.
    ///
    /// To return a new uppercased value without modifying the existing one, use
    /// [`to_ascii_uppercase`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hipstr::HipByt;
    /// let mut h = HipByt::from(b"!abc\0OK\x80");
    /// h.make_ascii_uppercase();
    /// assert_eq!(h, b"!ABC\0OK\x80");
    /// ```
    ///
    /// [`to_ascii_uppercase`]: Self::to_ascii_uppercase
    #[inline]
    pub fn make_ascii_uppercase(&mut self) {
        self.to_mut_slice().make_ascii_uppercase();
    }

    /// Creates a new `HipByt` by copying this one `n` times.
    ///
    /// This function **will not allocate** if the new length is less than or
    /// equal to the maximum inline capacity.
    ///
    /// # Panics
    ///
    /// This function will panic if the capacity would overflow.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// assert_eq!(HipByt::from(&[1, 2]).repeat(3), HipByt::from(&[1, 2, 1, 2, 1, 2]));
    /// ```
    ///
    /// A panic upon overflow:
    ///
    /// ```should_panic
    /// // this will panic at runtime
    /// # use hipstr::HipByt;
    /// HipByt::from(b"0123456789abcdef").repeat(usize::MAX);
    /// ```
    #[inline]
    #[must_use]
    pub fn repeat(&self, n: usize) -> Self {
        Self(self.0.repeat(n))
    }

    /// Returns the remaining spare capacity of the vector as a slice of
    /// `MaybeUninit<T>`.
    ///
    /// The returned slice can be used to fill the vector with data (e.g. by
    /// reading from a file) before marking the data as initialized using the
    /// [`set_len`] method.
    ///
    /// [`set_len`]: HipByt::set_len
    pub fn spare_capacity_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        self.0.spare_capacity_mut()
    }

    /// Forces the length of the vector to `new_len`.
    ///
    /// # Safety
    ///
    /// * If inline, `new_len` should be must be less than or equal to `INLINE_CAPACITY`.
    /// * If borrowed, `new_len` must be less than or equal to the current length.
    /// * If allocated and `new_len` is greater than the current length, the vector should not be shared.
    /// * The elements at `old_len..new_len` must be initialized.
    pub unsafe fn set_len(&mut self, new_len: usize) {
        // SAFETY: precondition
        unsafe { self.0.set_len(new_len) }
    }

    /// Concatenates some byte slices into a single `HipByt`.
    ///
    /// The related constructor [`HipByt::concat`] is more general but may be
    /// less efficient due to the absence of specialization in Rust.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hipstr::HipByt;
    /// let c = HipByt::concat_slices(&[b"hello", b" world", b"!"]);
    /// assert_eq!(c, b"hello world!");
    /// ```
    #[must_use]
    pub fn concat_slices(slices: &[&[u8]]) -> Self {
        let new_len = slices.iter().map(|e| e.len()).sum();

        if new_len == 0 {
            return Self::new();
        }

        let mut raw = Raw::with_capacity(new_len);
        let dst = raw.spare_capacity_mut();
        let dst_ptr = dst.as_mut_ptr().cast();
        let final_ptr = slices.iter().fold(dst_ptr, |dst_ptr, slice| {
            let len = slice.len();
            unsafe {
                ptr::copy_nonoverlapping(slice.as_ptr(), dst_ptr, len);
                dst_ptr.add(len)
            }
        });

        debug_assert_eq!(
            {
                #[expect(clippy::cast_sign_loss)]
                let diff_u = unsafe { final_ptr.offset_from(dst_ptr) } as usize;
                diff_u
            },
            new_len
        );

        unsafe { raw.set_len(new_len) };

        // check end pointer
        debug_assert_eq!(final_ptr.cast_const(), raw.as_slice().as_ptr_range().end);

        Self(raw)
    }

    /// Concatenates some byte slices (or things than can be seen as byte slice) into a new `HipByt`.
    ///
    /// # Panics
    ///
    /// During the concatenation, the iterator is ran twice: once to get the
    /// expected new length, and again to do the actual copy.
    /// If the returned slices are not the same and the new length is greater
    /// than the expected length, the function panics (before actually
    /// overflowing).
    ///
    /// This behavior differs from [`std::slice::Concat`] that reallocates when
    /// needed.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hipstr::HipByt;
    /// let c  = HipByt::concat(&[b"hello".as_slice(), b" world", b"!"]);
    /// assert_eq!(c, b"hello world!");
    ///
    /// let c2 = HipByt::concat([b"hello".to_vec(), b" world".to_vec(), b"!".to_vec()]);
    /// assert_eq!(c2, b"hello world!");
    ///
    /// let c3 = HipByt::concat(vec![b"hello".as_slice(), b" world", b"!"].iter());
    /// assert_eq!(c3, b"hello world!");
    /// ```
    #[must_use]
    pub fn concat<E, I>(slices: I) -> Self
    where
        E: AsRef<[u8]>,
        I: IntoIterator<Item = E>,
        I::IntoIter: Clone,
    {
        let slices = slices.into_iter();
        let new_len = slices.clone().map(|e| e.as_ref().len()).sum();
        if new_len == 0 {
            return Self::new();
        }

        let mut raw = Raw::with_capacity(new_len);
        let dst = raw.spare_capacity_mut();
        let dst_ptr: *mut u8 = dst.as_mut_ptr().cast();

        // compute the final pointer
        let final_ptr = unsafe { dst_ptr.add(new_len) };

        let _ = slices.fold(dst_ptr, |dst_ptr, slice| {
            let slice = slice.as_ref();
            let len = slice.len();
            let end_ptr = unsafe { dst_ptr.add(len) };
            assert!(end_ptr <= final_ptr, "slices changed during concat");
            unsafe {
                ptr::copy_nonoverlapping(slice.as_ptr(), dst_ptr, len);
                end_ptr
            }
        });

        unsafe { raw.set_len(new_len) };
        debug_assert_eq!(final_ptr.cast_const(), raw.as_slice().as_ptr_range().end);

        Self(raw)
    }

    /// Joins some byte slices with the given separator into a new `HipByt`, i.e.
    /// concatenates some byte slices, with a separator byte inserted between
    /// each pair of byte slices.
    ///
    /// The related constructor [`HipByt::join`] is more general but may be less
    /// efficient due to the absence of specialization in Rust.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let slices: &[&[u8]] = &[b"hello", b"world", b"rust"];
    /// let sep = b", ";
    /// let joined = HipByt::join_slices(slices, sep);
    /// assert_eq!(joined, b"hello, world, rust");
    /// ```
    #[must_use]
    pub fn join_slices(slices: &[&[u8]], sep: impl AsRef<[u8]>) -> Self {
        let slices_len = slices.len();
        if slices_len == 0 {
            return Self::new();
        }

        let sep = sep.as_ref();
        let sep_len = sep.len();

        // computes the final length
        let slices_sum: usize = slices.iter().copied().map(<[_]>::len).sum();
        let new_len = (slices_len - 1) * sep_len + slices_sum;
        if new_len == 0 {
            return Self::new();
        }

        let mut raw = Raw::with_capacity(new_len);
        let dst = raw.spare_capacity_mut();
        let dst_ptr: *mut u8 = dst.as_mut_ptr().cast();

        // compute the final pointer
        let final_ptr = unsafe { dst_ptr.add(new_len) };

        let mut iter = slices.iter().copied();

        // get first slice
        // SAFETY: segments > 0 is checked above
        let slice = unsafe { iter.next().unwrap_unchecked() };
        let len = slice.len();
        // SAFETY: dst_ptr + len cannot overflow
        let end_ptr = unsafe { dst_ptr.add(len) };
        debug_assert!(end_ptr <= final_ptr, "slices changed during concat");
        unsafe {
            ptr::copy_nonoverlapping(slice.as_ptr(), dst_ptr, len);
        }

        // remainder
        let _ = iter.fold(end_ptr, |mut dst_ptr, slice| {
            let end_ptr = unsafe { dst_ptr.add(sep_len) };
            debug_assert!(end_ptr <= final_ptr, "slices changed during concat");
            unsafe {
                ptr::copy_nonoverlapping(sep.as_ptr(), dst_ptr, sep_len);
            }
            dst_ptr = end_ptr;

            let len = slice.len();
            let end_ptr = unsafe { dst_ptr.add(len) };
            debug_assert!(end_ptr <= final_ptr, "slices changed during concat");
            unsafe {
                ptr::copy_nonoverlapping(slice.as_ptr(), dst_ptr, len);
            }

            end_ptr
        });

        unsafe { raw.set_len(new_len) };
        debug_assert_eq!(final_ptr.cast_const(), raw.as_slice().as_ptr_range().end);

        Self(raw)
    }

    /// Joins some byte slices (or things than can be seen as byte slice) with
    /// the given separator into a new `HipByt`.
    ///
    ///
    /// # Panics
    ///
    /// During the concatenation the iterator is ran twice: once to get the
    /// expected new length, and again to do the actual copy.
    /// If the returned strings are not the same and the new length is greater
    /// than the expected length, the function panics (before actually
    /// overflowing).
    ///
    /// This behavior differs from [`std::slice::Join`] that reallocates if needed.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hipstr::HipByt;
    /// let slices: &[&[u8]] = &[b"hello", b"world", b"rust"];
    /// let sep = b", ";
    /// let joined = HipByt::join(slices, sep);
    /// assert_eq!(joined, b"hello, world, rust");
    ///
    /// let joined = HipByt::join([b"hello".to_vec(), b"world".to_vec(), b"rust".to_vec()], sep.to_vec());
    /// assert_eq!(joined, b"hello, world, rust");
    ///
    /// let joined = HipByt::join(slices.to_vec().iter(), sep);
    /// assert_eq!(joined, b"hello, world, rust");
    /// ```
    #[must_use]
    pub fn join<E, I>(slices: I, sep: impl AsRef<[u8]>) -> Self
    where
        E: AsRef<[u8]>,
        I: IntoIterator<Item = E>,
        I::IntoIter: Clone,
    {
        let mut iter = slices.into_iter();

        // computes the final length
        let (segments, segments_len) = iter.clone().fold((0, 0), |(count, length), e| {
            (count + 1, length + e.as_ref().len())
        });
        if segments == 0 {
            return Self::new();
        }
        let sep = sep.as_ref();
        let sep_len = sep.len();
        let new_len = (segments - 1) * sep_len + segments_len;

        let mut raw = Raw::with_capacity(new_len);
        let dst = raw.spare_capacity_mut();
        let dst_ptr: *mut u8 = dst.as_mut_ptr().cast();

        // computes the final pointer
        // SAFETY: `new_len` is the length of raw
        let final_ptr = unsafe { dst_ptr.add(new_len) };

        if let Some(first) = iter.next() {
            let first = first.as_ref();
            let len = first.len();

            let end_ptr = unsafe { dst_ptr.add(first.len()) };
            assert!(end_ptr <= final_ptr, "slices changed during concat");
            unsafe {
                ptr::copy_nonoverlapping(first.as_ptr(), dst_ptr, len);
            }

            let _ = iter.fold(end_ptr, |mut dst_ptr, slice| {
                let end_ptr = unsafe { dst_ptr.add(sep_len) };
                assert!(end_ptr <= final_ptr, "slices changed during concat");
                unsafe {
                    ptr::copy_nonoverlapping(sep.as_ptr(), dst_ptr, sep_len);
                }
                dst_ptr = end_ptr;

                let slice = slice.as_ref();
                let len = slice.len();
                let end_ptr = unsafe { dst_ptr.add(len) };
                assert!(end_ptr <= final_ptr, "slices changed during concat");
                unsafe {
                    ptr::copy_nonoverlapping(slice.as_ptr(), dst_ptr, len);
                }
                end_ptr
            });
        }

        unsafe { raw.set_len(new_len) };
        debug_assert_eq!(final_ptr.cast_const(), raw.as_slice().as_ptr_range().end);

        Self(raw)
    }
}

impl<B> HipByt<'static, B>
where
    B: Backend,
{
    /// Creates a new `HipByt` from a static slice without copying the slice.
    ///
    /// Handy shortcut to make a `HipByt<'static, _>` out of a `&'static [u8]`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let b = HipByt::from_static(b"hello\0");
    /// assert_eq!(b.len(), 6);
    /// ```
    #[inline]
    #[must_use]
    pub const fn from_static(bytes: &'static [u8]) -> Self {
        Self::borrowed(bytes)
    }
}

impl<B> Clone for HipByt<'_, B>
where
    B: Backend,
{
    #[inline]
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<B> Default for HipByt<'_, B>
where
    B: Backend,
{
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<B> Deref for HipByt<'_, B>
where
    B: Backend,
{
    type Target = Slice;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

impl<B> Borrow<[u8]> for HipByt<'_, B>
where
    B: Backend,
{
    #[inline]
    fn borrow(&self) -> &[u8] {
        self.as_slice()
    }
}

impl<B> Hash for HipByt<'_, B>
where
    B: Backend,
{
    #[inline]
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.as_slice().hash(state);
    }
}

// Formatting

impl<B> fmt::Debug for HipByt<'_, B>
where
    B: Backend,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_slice().fmt(f)
    }
}

/// Slice error kinds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SliceErrorKind {
    /// Start index should be less or equal to the end index
    StartGreaterThanEnd,

    /// Start index out of bounds
    StartOutOfBounds,

    /// End index out of bounds
    EndOutOfBounds,
}

/// Normalizes any [`RangeBounds`] to a [`Range`].
pub(crate) fn simplify_range(
    range: impl RangeBounds<usize>,
    len: usize,
) -> Result<Range<usize>, (usize, usize, SliceErrorKind)> {
    simplify_range_mono(
        range.start_bound().cloned(),
        range.end_bound().cloned(),
        len,
    )
}

const fn simplify_range_mono(
    start: Bound<usize>,
    end: Bound<usize>,
    len: usize,
) -> Result<Range<usize>, (usize, usize, SliceErrorKind)> {
    let start = match start {
        Bound::Included(start) => start,
        Bound::Excluded(start) => start + 1,
        Bound::Unbounded => 0,
    };
    let end = match end {
        Bound::Included(end) => end + 1,
        Bound::Excluded(end) => end,
        Bound::Unbounded => len,
    };
    if start > len {
        Err((start, end, SliceErrorKind::StartOutOfBounds))
    } else if end > len {
        Err((start, end, SliceErrorKind::EndOutOfBounds))
    } else if start > end {
        Err((start, end, SliceErrorKind::StartGreaterThanEnd))
    } else {
        Ok(Range { start, end })
    }
}

/// A possible error value when slicing a [`HipByt`].
///
/// This type is the error type for [`HipByt::try_slice`].
pub struct SliceError<'a, 'borrow, B>
where
    B: Backend,
{
    kind: SliceErrorKind,
    start: usize,
    end: usize,
    bytes: &'a HipByt<'borrow, B>,
}

impl<B> Clone for SliceError<'_, '_, B>
where
    B: Backend,
{
    fn clone(&self) -> Self {
        *self
    }
}

impl<B> Copy for SliceError<'_, '_, B> where B: Backend {}

impl<B> Eq for SliceError<'_, '_, B> where B: Backend {}

impl<B> PartialEq for SliceError<'_, '_, B>
where
    B: Backend,
{
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
            && self.start == other.start
            && self.end == other.end
            && self.bytes == other.bytes
    }
}

impl<'a, B> SliceError<'_, 'a, B>
where
    B: Backend,
{
    const fn new(kind: SliceErrorKind, start: usize, end: usize, bytes: &'a HipByt<B>) -> Self {
        Self {
            kind,
            start,
            end,
            bytes,
        }
    }

    /// Returns the kind of error.
    #[inline]
    #[must_use]
    pub const fn kind(&self) -> SliceErrorKind {
        self.kind
    }

    /// Returns the start of the requested range.
    #[inline]
    #[must_use]
    pub const fn start(&self) -> usize {
        self.start
    }

    /// Returns the end of the requested range.
    #[inline]
    #[must_use]
    pub const fn end(&self) -> usize {
        self.end
    }

    /// Returns the _normalized_ requested range.
    #[inline]
    #[must_use]
    pub const fn range(&self) -> Range<usize> {
        self.start..self.end
    }

    /// Returns a reference to the source `HipByt` to slice.
    #[inline]
    #[must_use]
    pub const fn source(&self) -> &HipByt<B> {
        self.bytes
    }
}

impl<B> fmt::Debug for SliceError<'_, '_, B>
where
    B: Backend,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SliceError")
            .field("kind", &self.kind)
            .field("start", &self.start)
            .field("end", &self.end)
            .field("bytes", &self.bytes)
            .finish()
    }
}

impl<B> fmt::Display for SliceError<'_, '_, B>
where
    B: Backend,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            SliceErrorKind::StartGreaterThanEnd => {
                write!(f, "range starts at {} but ends at {}", self.start, self.end)
            }
            SliceErrorKind::StartOutOfBounds => write!(
                f,
                "range start index {} out of bounds for slice of length {}",
                self.start,
                self.bytes.len()
            ),
            SliceErrorKind::EndOutOfBounds => {
                write!(
                    f,
                    "range end index {} out of bounds for slice of length {}",
                    self.end,
                    self.bytes.len()
                )
            }
        }
    }
}

impl<B> Error for SliceError<'_, '_, B> where B: Backend {}

/// A wrapper type for a mutably borrowed vector out of a [`HipByt`].
pub struct RefMut<'a, 'borrow, B>
where
    B: Backend,
{
    result: &'a mut HipByt<'borrow, B>,
    owned: Owned,
}

impl<B> Drop for RefMut<'_, '_, B>
where
    B: Backend,
{
    fn drop(&mut self) {
        let owned = core::mem::take(&mut self.owned);
        *self.result = HipByt::from(owned);
    }
}

impl<B> Deref for RefMut<'_, '_, B>
where
    B: Backend,
{
    type Target = Owned;

    fn deref(&self) -> &Self::Target {
        &self.owned
    }
}

impl<B> DerefMut for RefMut<'_, '_, B>
where
    B: Backend,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.owned
    }
}
