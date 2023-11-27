//! Bytes.
//!
//! This module provides the [`HipByt`] type as well as the associated helper and error types.

use core::borrow::Borrow;
use core::hash::Hash;
use core::ops::{Bound, Deref, DerefMut, Range, RangeBounds};

use super::raw::Raw;
use crate::alloc::fmt;
use crate::alloc::vec::Vec;
use crate::raw::try_range_of;
use crate::{Backend, ThreadSafe};

mod cmp;
mod convert;

#[cfg(feature = "serde")]
pub mod serde;

#[cfg(test)]
mod tests;

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

    /// Creates a new `HipByt` from a borrowed slice without copying the slice.
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
    pub fn to_mut_slice(&mut self) -> &mut [u8] {
        self.0.make_unique();
        unsafe { self.0.as_mut_slice().unwrap_unchecked() }
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
    /// The range must be a range `a..b` with `a <= b <= len`.
    /// Panics in debug mode. UB in release mode.
    #[must_use]
    pub(crate) unsafe fn slice_unchecked(&self, range: Range<usize>) -> Self {
        Self(unsafe { self.0.slice_unchecked(range) })
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
        RefMut {
            result: self,
            owned,
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
    /// ```
    /// # use hipstr::HipByt;
    /// let v = vec![42; 42];
    /// let h = HipByt::borrowed(&v[..]);
    /// // drop(v); // err, v is borrowed
    /// let h = h.into_owned();
    /// drop(v); // ok
    /// assert_eq!(h, [42; 42]);
    /// ```
    pub fn into_owned(self) -> HipByt<'static, B> {
        HipByt(self.0.into_owned())
    }

    pub(crate) fn take_vec(&mut self) -> Vec<u8> {
        self.0.take_vec()
    }

    #[cfg(test)]
    #[inline]
    pub(crate) fn is_normalized(&self) -> bool {
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

impl<'borrow, B> Clone for HipByt<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<'borrow, B> Default for HipByt<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<'borrow, B> Deref for HipByt<'borrow, B>
where
    B: Backend,
{
    type Target = [u8];

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<'borrow, B> Borrow<[u8]> for HipByt<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn borrow(&self) -> &[u8] {
        self.as_slice()
    }
}

impl<'borrow, B> Hash for HipByt<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.as_slice().hash(state);
    }
}

// Formatting

impl<'borrow, B> fmt::Debug for HipByt<'borrow, B>
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

fn simplify_range_mono(
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
#[derive(PartialEq, Eq, Clone)]
pub struct SliceError<'a, 'borrow, B>
where
    B: Backend,
{
    kind: SliceErrorKind,
    start: usize,
    end: usize,
    bytes: &'a HipByt<'borrow, B>,
}

impl<'a, 'borrow, B> SliceError<'borrow, 'a, B>
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

impl<'a, 'borrow, B> fmt::Debug for SliceError<'a, 'borrow, B>
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

impl<'a, 'borrow, B> fmt::Display for SliceError<'a, 'borrow, B>
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

#[cfg(feature = "std")]
impl<'a, 'borrow, B> std::error::Error for SliceError<'a, 'borrow, B> where B: Backend {}

/// A wrapper type for a mutably borrowed vector out of a [`HipByt`].
pub struct RefMut<'a, 'borrow, B>
where
    B: Backend,
{
    result: &'a mut HipByt<'borrow, B>,
    owned: Vec<u8>,
}

impl<'a, 'borrow, B> Drop for RefMut<'a, 'borrow, B>
where
    B: Backend,
{
    fn drop(&mut self) {
        let owned = core::mem::take(&mut self.owned);
        *self.result = HipByt::from(owned);
    }
}

impl<'a, 'borrow, B> Deref for RefMut<'a, 'borrow, B>
where
    B: Backend,
{
    type Target = Vec<u8>;
    fn deref(&self) -> &Self::Target {
        &self.owned
    }
}

impl<'a, 'borrow, B> DerefMut for RefMut<'a, 'borrow, B>
where
    B: Backend,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.owned
    }
}
