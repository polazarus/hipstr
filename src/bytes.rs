//! Cheaply clonable, sliceable, and mostly immutable, byte string.

use std::borrow::Borrow;
use std::error::Error;
use std::fmt;
use std::hash::Hash;
use std::ops::{Bound, Deref, DerefMut, Range, RangeBounds};

use super::raw::Raw;
use crate::{Backend, ThreadSafe};

mod cmp;
mod convert;

#[cfg(feature = "serde")]
mod serde;

/// Smart bytes, i.e. cheaply clonable and sliceable byte string.
///
/// # Examples
///
/// You can create a `HipStr` from a [byte slice][slice], an owned byte string
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
/// For literals, you can also use the more efficient constructor [`HipByt::from_static`]:
///
/// ```
/// # use hipstr::HipByt;
/// let hello = HipByt::from_static(b"Hello, world!");
/// ```
///
/// # Representations
///
/// `HipByt` has three possible internal representations:
///
/// * static borrow
/// * inline string
/// * shared heap allocated string
#[repr(transparent)]
pub struct HipByt<B = ThreadSafe>(pub(crate) Raw<B>)
where
    B: Backend;

impl<B> HipByt<B>
where
    B: Backend,
{
    /// Creates an empty `HipByt`.
    ///
    /// Function provided for [`Vec::new`] replacement.
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

    /// Creates a new `HipByt` from a static slice without copying the slice.
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
    #[must_use]
    pub const fn from_static(bytes: &'static [u8]) -> Self {
        Self(Raw::from_static(bytes))
    }

    /// Returns `true` if this `HipByt` uses the inline representation, `false` otherwise.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let s = HipByt::from_static(b"hello");
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

    /// Returns `true` if this `HipByt` is a static slice borrow,.`false` otherwise.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let s = HipByt::from_static(b"hello");
    /// assert!(s.is_static());
    ///
    /// let s = HipByt::from(b"hello");
    /// assert!(!s.is_static());
    ///
    /// let s = HipByt::from(b"hello".repeat(10));
    /// assert!(!s.is_static());
    /// ```
    #[inline]
    #[must_use]
    pub const fn is_static(&self) -> bool {
        self.0.is_static()
    }

    /// Returns `true` if this `HipByt` is a shared heap-allocated byte sequence, `false` otherwise.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let s = HipByt::from_static(b"hello");
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

    /// Converts `self` into a static slice if this `HipByt` is backed by a static borrow.
    ///
    /// # Errors
    ///
    /// Returns `Err(self)` if this `HipByt` is not a static borrow.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// static SEQ: &[u8] = &[1 ,2, 3];
    /// let s = HipByt::from_static(SEQ);
    /// let c = s.into_static();
    /// assert_eq!(c, Ok(SEQ));
    /// assert!(std::ptr::eq(SEQ, c.unwrap()));
    /// ```
    #[inline]
    pub fn into_static(self) -> Result<&'static [u8], Self> {
        self.0.into_static().map_err(Self)
    }

    /// Returns the length of this `HipByt`.
    ///
    /// # Example
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let a = HipByt::from_static(b"\xDE\xAD\xBE\xEF");
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
    /// let b = HipByt::from_static(b"ab");
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
    /// let mut s = HipByt::from_static(b"foo");
    /// let slice = s.to_mut_slice(); // change the representation to inline
    /// slice.copy_from_slice(b"bar");
    /// assert_eq!(b"bar", slice);
    /// ```
    pub fn to_mut_slice(&mut self) -> &mut [u8] {
        self.0.to_mut_slice()
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
        Ok(Self(self.0.slice(range)))
    }

    #[must_use]
    pub(crate) fn slice_unchecked(&self, range: Range<usize>) -> Self {
        Self(self.0.slice(range))
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
    /// let mut vec: Vec<u8> = Vec::with_capacity(10);
    /// vec.extend_from_slice(&[1, 2, 3]);
    /// let bytes = HipByt::from(vec);
    /// assert_eq!(bytes.capacity(), 10);
    ///
    /// let half = bytes.slice(0..2);
    /// assert_eq!(bytes.capacity(), 10); // same backend, same capacity
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
    /// let mut s = HipByt::from_static(b"abc");
    /// {
    ///     let mut r = s.mutate();
    ///     r.extend_from_slice(b"def");
    ///     assert_eq!(r.as_slice(), b"abcdef");
    /// }
    /// assert_eq!(s, b"abcdef");
    /// ```
    #[inline]
    #[must_use]
    pub fn mutate(&mut self) -> RefMut<B> {
        let owned = self.0.take_vec();
        RefMut {
            result: self,
            owned,
        }
    }

    pub(crate) fn take_vec(&mut self) -> Vec<u8> {
        self.0.take_vec()
    }

    /// Transforms to the inline representation, returning a new inline `HipByt`
    /// and consuming this `HipByt`.
    ///
    /// # Errors
    ///
    /// Returns the original `HipByt` if it cannot be inlined, i.e.,
    /// if the length greater than [`HipByt::inline_capacity()`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hipstr::HipByt;
    /// let v = vec![42; 42];
    /// let mut b = HipByt::from(v);
    /// assert!(b.is_allocated());
    /// assert!(!b.is_inline());
    /// assert!(b.inline().is_err());
    ///
    /// let v = b"abc".to_vec();
    /// let b = HipByt::from(v);
    /// assert!(b.is_allocated());
    /// assert!(!b.is_inline());
    /// let b = b.inline().unwrap();
    /// assert!(b.is_inline());
    /// ```
    #[inline]
    pub fn inline(self) -> Result<Self, Self> {
        self.0.inline().map(Self).map_err(Self)
    }
}

impl<B> Clone for HipByt<B>
where
    B: Backend,
{
    #[inline]
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<B> Default for HipByt<B>
where
    B: Backend,
{
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<B> Deref for HipByt<B>
where
    B: Backend,
{
    type Target = [u8];

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<B> Borrow<[u8]> for HipByt<B>
where
    B: Backend,
{
    #[inline]
    fn borrow(&self) -> &[u8] {
        self.as_slice()
    }
}

impl<B> Hash for HipByt<B>
where
    B: Backend,
{
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_slice().hash(state);
    }
}

// Formatting

impl<B> fmt::Debug for HipByt<B>
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
    let start = match range.start_bound() {
        Bound::Included(&start) => start,
        Bound::Excluded(&start) => start + 1,
        Bound::Unbounded => 0,
    };
    let end = match range.end_bound() {
        Bound::Included(&end) => end + 1,
        Bound::Excluded(&end) => end,
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
pub struct SliceError<'a, B>
where
    B: Backend,
{
    kind: SliceErrorKind,
    start: usize,
    end: usize,
    bytes: &'a HipByt<B>,
}

impl<'a, B> SliceError<'a, B>
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

impl<'a, B> fmt::Debug for SliceError<'a, B>
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

impl<'a, B> fmt::Display for SliceError<'a, B>
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

impl<'a, B> Error for SliceError<'a, B> where B: Backend {}

/// A wrapper type for a mutably borrowed vector out of a [`HipByt`].
pub struct RefMut<'a, B>
where
    B: Backend,
{
    result: &'a mut HipByt<B>,
    owned: Vec<u8>,
}

impl<'a, B> Drop for RefMut<'a, B>
where
    B: Backend,
{
    fn drop(&mut self) {
        let owned = std::mem::take(&mut self.owned);
        *self.result = HipByt::from(owned);
    }
}

impl<'a, B> Deref for RefMut<'a, B>
where
    B: Backend,
{
    type Target = Vec<u8>;
    fn deref(&self) -> &Self::Target {
        &self.owned
    }
}

impl<'a, B> DerefMut for RefMut<'a, B>
where
    B: Backend,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.owned
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;
    use std::ops::Bound;

    // cspell:ignore fastrand
    use fastrand::Rng;

    use super::SliceErrorKind;
    use crate::HipByt;

    const INLINE_CAPACITY: usize = HipByt::inline_capacity();

    #[test]
    fn test_new_default() {
        let new = HipByt::new();
        assert_eq!(new, &[]);
        assert!(new.is_empty());

        let new = HipByt::default();
        assert_eq!(new, &[]);
        assert!(new.is_empty());
    }

    #[test]
    fn test_borrow_and_hash() {
        let mut set = HashSet::new();
        set.insert(HipByt::from(b"a"));
        set.insert(HipByt::from(b"b"));

        assert!(set.contains(b"a".as_slice()));
        assert!(!set.contains(b"c".as_slice()));
    }

    #[test]
    fn test_debug() {
        let slice = &[1, 2, 3];
        let bytes = HipByt::from(slice);
        assert_eq!(format!("{slice:?}"), format!("{bytes:?}"));
    }

    #[test]
    fn test_from_vec() {
        let v = vec![42; 10];
        let bytes = HipByt::from(v);
        assert!(!bytes.is_inline());
        assert!(!bytes.is_static());
        assert!(bytes.is_allocated());
        assert_eq!(bytes.len(), 10);
        assert_eq!(bytes.as_slice(), [42; 10]);
    }

    #[test]
    fn test_from_static() {
        static V: &[u8] = &[42; 1024];

        for size in [0, 1, INLINE_CAPACITY, INLINE_CAPACITY + 1, 256, 1024] {
            let bytes = HipByt::from_static(&V[..size]);
            assert!(!bytes.is_inline());
            assert!(bytes.is_static());
            assert!(!bytes.is_allocated());
            assert_eq!(bytes.len(), size);
            assert_eq!(bytes.as_ptr(), V.as_ptr());
        }
    }

    #[test]
    fn test_from_slice() {
        static V: &[u8] = &[42; 1024];

        for size in [0, 1, INLINE_CAPACITY, INLINE_CAPACITY + 1, 256, 1024] {
            let bytes = HipByt::from(&V[..size]);
            assert_eq!(size > 0 && size <= INLINE_CAPACITY, bytes.is_inline());
            assert_eq!(size > INLINE_CAPACITY, bytes.is_allocated());
            assert!(size == 0 || !bytes.is_static());
            assert_eq!(bytes.len(), size);
        }
    }

    #[test]
    fn test_as_slice() {
        // static
        {
            let a = HipByt::from_static(b"abc");
            assert!(a.is_static());
            assert!(!a.is_inline());
            assert!(!a.is_allocated());
            assert_eq!(a.as_slice(), b"abc");
        }
        // inline
        {
            let a = HipByt::from(b"abc".as_slice());
            assert!(!a.is_static());
            assert!(a.is_inline());
            assert!(!a.is_allocated());
            assert_eq!(a.as_slice(), b"abc");
        }
        // allocated
        {
            let a = HipByt::from(vec![42; 42]);
            assert!(!a.is_static());
            assert!(!a.is_inline());
            assert!(a.is_allocated());
            assert_eq!(a.as_slice(), [42; 42]);
        }
    }

    #[test]
    fn test_clone() {
        // static
        {
            let s: &'static [u8] = b"abc";
            let a = HipByt::from_static(s);
            assert!(a.is_static());
            let b = a.clone();
            drop(a);
            assert_eq!(b.as_slice(), s);
            assert_eq!(s.as_ptr(), b.as_ptr());
        }

        // inline
        {
            let a = HipByt::from(b"abc".as_slice());
            assert!(a.is_inline());
            let b = a.clone();
            drop(a);
            assert_eq!(b.as_slice(), b"abc");
        }

        // allocated
        {
            let v = vec![42; 42];
            let p = v.as_ptr();
            let a = HipByt::from(v);
            assert!(a.is_allocated());
            let b = a.clone();
            drop(a);
            assert_eq!(b.as_slice(), [42; 42]);
            assert_eq!(b.as_ptr(), p);
        }
    }

    #[test]
    fn test_clone_drop() {
        let v = vec![42; 42];
        let rand = Rng::with_seed(0);
        for n in [5, 10, 20, 100] {
            // println!("!n {n}");
            let mut vs = vec![HipByt::from(v.clone()); n];

            while !vs.is_empty() {
                // println!("len {}", vs.len());
                let drops = rand.usize(1..=vs.len());
                // println!("drops {drops}");

                for _ in 0..drops {
                    let _ = vs.pop();
                }
                if !vs.is_empty() {
                    let clones = rand.usize(..drops.min(vs.len()));
                    // println!("clones {clones}");
                    for _ in 0..clones {
                        vs.push(vs[0].clone())
                    }
                }
            }
        }
        // assert!(false);
    }

    #[test]
    fn test_into_static() {
        // static
        let a = HipByt::from_static(b"abc");
        assert_eq!(a.into_static(), Ok(b"abc".as_slice()));

        // inline
        let a = HipByt::from(b"abc".as_slice());
        let b = a.clone();
        assert_eq!(a.into_static(), Err(b));

        // heap
        let a = HipByt::from([42; 42].as_slice());
        let b = a.clone();
        assert_eq!(a.into_static(), Err(b));
    }

    #[test]
    fn test_as_mut_slice() {
        // static
        let mut a = HipByt::from_static(b"abc");
        assert_eq!(a.as_mut_slice(), None);

        // inline
        let mut a = HipByt::from([42; 3].as_slice());
        assert!(a.is_inline());
        assert_eq!(a.as_mut_slice(), Some([42; 3].as_mut_slice()));

        // heap
        let mut a = HipByt::from([42; 42].as_slice());
        {
            let sl = a.as_mut_slice();
            assert_eq!(sl, Some([42; 42].as_mut_slice()));
            sl.unwrap()[0] = 43;
        }
        let mut b = a.clone();
        assert_eq!(b[0], 43);
        assert_eq!(b.as_mut_slice(), None);
        let _ = a.as_slice();
    }

    #[test]
    fn test_to_mut_slice() {
        // static
        let mut a = HipByt::from_static(b"abc");
        assert!(a.is_static());
        assert_eq!(a.to_mut_slice(), b"abc".to_vec().as_mut_slice());
        assert!(a.is_inline());

        // inline
        let mut a = HipByt::from([42; 3].as_slice());
        assert!(a.is_inline());
        assert_eq!(a.to_mut_slice(), [42; 3].as_mut_slice());
        assert!(a.is_inline());

        // heap
        let mut a = HipByt::from([42; 42].as_slice());
        assert!(a.is_allocated());
        {
            let sl = a.to_mut_slice();
            assert_eq!(sl, [42; 42].as_mut_slice());
            sl[0] = 43;
        }
        let mut b = a.clone();
        assert_eq!(b[0], 43);
        let _ = b.to_mut_slice();
        assert!(b.is_allocated());
        assert_ne!(b.as_ptr(), a.as_ptr());
    }

    #[test]
    fn test_slice() {
        let v: Vec<_> = (0..(INLINE_CAPACITY as u8)).collect();
        let s = HipByt::from(&v[..]);
        let sl = s.slice(0..10);
        assert_eq!(&sl, &v[0..10]);
        let sl = s.slice(..);
        assert_eq!(&sl, &v[..]);

        let v: Vec<_> = (0..42).collect();
        let s = HipByt::from(&v[..]);

        let sl1 = s.slice(4..30);
        assert_eq!(&sl1, &v[4..30]);
        assert_eq!(sl1.as_ptr(), s[4..30].as_ptr());

        let p = s[9..12].as_ptr();
        drop(s);

        let sl2 = sl1.slice(5..8);
        drop(sl1);
        assert_eq!(&sl2, &v[9..12]);
        assert_eq!(sl2.as_ptr(), p);
    }

    #[test]
    #[should_panic]
    fn test_slice_panic_start() {
        let a = HipByt::from_static(b"abc");
        let _b = a.slice(4..);
    }

    #[test]
    #[should_panic]
    fn test_slice_panic_end() {
        let a = HipByt::from_static(b"abc");
        let _b = a.slice(..5);
    }

    #[test]
    #[should_panic]
    fn test_slice_panic_mixed() {
        let a = HipByt::from_static(b"abc");
        let _b = a.slice(3..2);
    }

    #[test]
    fn test_try_slice() {
        let a = HipByt::from_static(b"abcdef");

        let e = a.try_slice(7..).unwrap_err();
        assert_eq!(e.kind(), SliceErrorKind::StartOutOfBounds);
        assert_eq!(e.start(), 7);
        assert_eq!(e.end(), 6);
        assert_eq!(e.range(), 7..6);
        assert!(std::ptr::eq(e.source(), &a));
        assert_eq!(format!("{e:?}"), "SliceError { kind: StartOutOfBounds, start: 7, end: 6, bytes: [97, 98, 99, 100, 101, 102] }");
        assert_eq!(
            format!("{e}"),
            "range start index 7 out of bounds for slice of length 6"
        );

        let e = a.try_slice(..7).unwrap_err();
        assert_eq!(
            format!("{e}"),
            "range end index 7 out of bounds for slice of length 6"
        );
        assert_eq!(a.try_slice(0..=6).unwrap_err(), e);

        let e = a.try_slice(1..0).unwrap_err();
        assert_eq!(format!("{e}"), "range starts at 1 but ends at 0");

        assert!(a.try_slice(0..6).is_ok());
        assert!(a.try_slice(..=1).is_ok());

        assert!(a.try_slice(1..).is_ok());
        assert!(a.try_slice(1..0).is_err());
        assert!(a
            .try_slice((Bound::Excluded(0), Bound::Included(1)))
            .is_ok());
    }

    #[test]
    fn test_empty_vec() {
        // the vec is adopted even if it's empty
        let source = vec![];
        let p = source.as_ptr();
        let heap_zero = HipByt::from(source);
        assert!(heap_zero.is_allocated());
        assert_eq!(heap_zero.len(), 0);
        assert_eq!(heap_zero, b"");
        assert_eq!(heap_zero.as_ptr(), p);
    }

    #[test]
    fn test_empty_slice() {
        // should normalize slice to static
        let source1 = HipByt::from(vec![1, 2, 3]);
        let empty_slice1 = source1.slice(0..0);
        assert!(empty_slice1.is_static());

        let source2 = HipByt::from(&[1, 2, 3]);
        let empty_slice2 = source2.slice(0..0);
        assert!(empty_slice2.is_static());
    }

    #[test]
    fn test_into_vec() {
        {
            // static
            let a = HipByt::from_static(b"abc");
            assert!(a.into_vec().is_err());
        }

        {
            // inline
            let a = HipByt::from(b"abc");
            assert!(a.into_vec().is_err());
        }

        let v = vec![42; 10];
        {
            // allocated, unique
            let v = v.clone();
            let p = v.as_ptr();
            let a = HipByt::from(v);
            let v = a.into_vec().unwrap();
            assert_eq!(p, v.as_ptr());
            assert_eq!(10, v.len());
        }

        {
            // allocated, shared
            let a = HipByt::from(v.clone());
            let _b = a.clone();
            assert!(a.into_vec().is_err());
        }

        {
            // allocated, unique, sliced at start
            let v = v.clone();
            let p = v.as_ptr();
            let a = HipByt::from(v).slice(0..5);
            let v = a.into_vec().unwrap();
            assert_eq!(v.len(), 5);
            assert_eq!(v.as_ptr(), p);
        }

        {
            // allocated, unique, sliced at start
            let a = HipByt::from(v).slice(1..5);
            assert!(a.into_vec().is_err());
        }
    }

    #[test]
    fn test_capacity() {
        {
            // static
            let a = HipByt::from_static(b"abc");
            assert_eq!(a.capacity(), a.len());
        }

        {
            // inline
            let a = HipByt::from(b"abc");
            assert_eq!(a.capacity(), HipByt::inline_capacity());
        }

        {
            // allocated
            let mut v = Vec::with_capacity(42);
            v.extend_from_slice(b"abc");
            let a = HipByt::from(v);
            assert_eq!(a.capacity(), 42);

            let b = a.slice(1..);
            assert_eq!(b.capacity(), 42);
        }
    }

    #[test]
    fn test_mutate() {
        {
            // static
            let mut a = HipByt::from_static(b"abc");
            assert!(a.is_static(), "a should be static");
            a.mutate().extend_from_slice(b"def");
            assert!(a.is_allocated(), "a should be allocated at the end");
            assert_eq!(a, b"abcdef", "should be modified");
        }

        {
            // inline
            let mut a = HipByt::from(b"abc");
            assert!(a.is_inline(), "a should be inline at the start");
            a.mutate().extend_from_slice(b"def");
            assert!(a.is_allocated(), "a should be allocated at the end");
            assert_eq!(a, b"abcdef", "should be modified");
        }

        {
            // allocated, unique with enough capacity
            let mut v = Vec::with_capacity(6);
            v.extend_from_slice(b"abc");
            let p = v.as_ptr();
            let mut a = HipByt::from(v);
            assert!(a.is_allocated(), "should be allocated at the start");
            a.mutate().extend_from_slice(b"def");
            assert!(a.is_allocated(), "should be allocated at the end");
            assert_eq!(a, b"abcdef", "should be modified");
            assert_eq!(a.as_ptr(), p, "should have same backend vector");
        }

        {
            // allocated, shared
            let mut v = Vec::with_capacity(6);
            v.extend_from_slice(b"abc");
            let mut a = HipByt::from(v);
            assert!(a.is_allocated(), "a should be allocated at the start");
            let b = a.clone();
            a.mutate().extend_from_slice(b"def");
            assert!(a.is_allocated(), "a should be allocated at the end");
            assert_eq!(a, b"abcdef", "a should be modified");
            assert_eq!(b, b"abc", "b should not be modified");
            assert_ne!(a.as_ptr(), b.as_ptr(), "different backend vector");
        }
    }
}
