//! Cheaply clonable, sliceable, and mostly immutable, string.

use std::borrow::{Borrow, Cow};
use std::error::Error;
use std::fmt;
use std::hash::Hash;
use std::ops::{Deref, DerefMut, Range, RangeBounds};
use std::str::Utf8Error;
use std::string::FromUtf16Error;

use crate::bytes::{simplify_range, HipByt, SliceErrorKind as ByteSliceErrorKind};
use crate::Backend;

mod cmp;
mod convert;

#[cfg(feature = "serde")]
mod serde;

/// Smart string, i.e. cheaply clonable and sliceable string.
///
/// Internally used the same representations as [`HipByt`].
///
/// # Examples
///
/// You can create a `HipStr` from a [string slice][str], an owned string
/// ([`String`], [`Box<str>`][Box]), or a clone-on-write smart pointer
/// ([`Cow<str>`][std::borrow::Cow]) with [`From`]:
///
/// ```
/// # use hipstr::HipStr;
/// let hello = HipStr::from("Hello");
/// ```
///
/// When possible, `HipStr::from` takes ownership of the underlying string
/// buffer:
///
/// ```
/// # use hipstr::HipStr;
/// let world = HipStr::from(String::from("World")); // here there is only one heap-allocation
/// ```
///
/// For borrowing string slice, you can also use the no-copy [`HipStr::borrowed`]
/// (like [`Cow::Borrowed`](std::borrow::Cow)):
///
/// ```
/// # use hipstr::HipStr;
/// let hello = HipStr::borrowed("Hello, world!");
/// ```
///
/// # Representations
///
/// Like `HipByt`, `HipStr` has three possible internal representations:
///
/// * borrow
/// * inline string
/// * shared heap allocated string
#[repr(transparent)]
pub struct HipStr<'borrow, B>(HipByt<'borrow, B>)
where
    B: Backend;

impl<'borrow, B> HipStr<'borrow, B>
where
    B: Backend,
{
    /// Creates an empty `HipStr`.
    ///
    /// Function provided for [`String::new`] replacement.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let s = HipStr::new();
    /// ```
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self(HipByt::new())
    }

    /// Creates a new `HipStr` from a static string slice without copying the slice.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let s = HipStr::borrowed("hello");
    /// assert_eq!(s.len(), 5);
    /// ```
    #[must_use]
    pub const fn borrowed(value: &'borrow str) -> Self {
        Self(HipByt::borrowed(value.as_bytes()))
    }

    /// Returns `true` if this `HipStr` uses the inline representation, `false` otherwise.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let s = HipStr::borrowed("hello");
    /// assert!(!s.is_inline());
    ///
    /// let s = HipStr::from("hello");
    /// assert!(s.is_inline());
    ///
    /// let s = HipStr::from("hello".repeat(10));
    /// assert!(!s.is_inline());
    /// ```
    #[inline]
    #[must_use]
    pub const fn is_inline(&self) -> bool {
        self.0.is_inline()
    }

    /// Returns `true` if this `HipStr` is a static string borrow, `false` otherwise.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let s = HipStr::borrowed("hello");
    /// assert!(s.is_static());
    ///
    /// let s = HipStr::from("hello");
    /// assert!(!s.is_static());
    ///
    /// let s = HipStr::from("hello".repeat(10));
    /// assert!(!s.is_static());
    /// ```
    #[inline]
    #[must_use]
    pub const fn is_static(&self) -> bool {
        self.0.is_static()
    }

    /// Returns `true` if this `HipStr` is a shared heap-allocated string, `false` otherwise.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let s = HipStr::borrowed("hello");
    /// assert!(!s.is_allocated());
    ///
    /// let s = HipStr::from("hello");
    /// assert!(!s.is_allocated());
    ///
    /// let s = HipStr::from("hello".repeat(10));
    /// assert!(s.is_allocated());
    /// ```
    #[inline]
    #[must_use]
    pub const fn is_allocated(&self) -> bool {
        self.0.is_allocated()
    }

    /// Converts `self` into a static string slice if this `HipStr` is backed by a static borrow.
    ///
    /// # Errors
    ///
    /// Returns `Err(self)` if this `HipStr` is not a static borrow.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let borrowed = "hipstr";
    /// let s = HipStr::borrowed(borrowed);
    /// let c = s.into_borrowed();
    /// assert_eq!(c, Ok(borrowed));
    /// assert!(std::ptr::eq(borrowed, c.unwrap()));
    /// ```
    #[inline]
    pub fn into_borrowed(self) -> Result<&'borrow str, Self> {
        self.0
            .into_borrowed()
            .map(|slice|
                // SAFETY: type invariant
                unsafe { std::str::from_utf8_unchecked(slice) })
            .map_err(Self)
    }

    /// Returns the length of this `HipStr`, in bytes, not [`char`]s or
    /// graphemes. In other words, it might not be what a human considers the
    /// length of the string.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let a = HipStr::from("(c)");
    /// assert_eq!(a.len(), 3);
    ///
    /// let b = HipStr::from("®");
    /// assert_eq!(b.len(), 2);
    /// assert_eq!(b.chars().count(), 1);
    /// ```
    #[inline]
    #[must_use]
    pub const fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns `true` if this `HipStr` has a length of zero, and `false` otherwise.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let a = HipStr::new();
    /// assert!(a.is_empty());
    ///
    /// let b = HipStr::borrowed("ab");
    /// assert!(!b.is_empty());
    /// ```
    #[inline]
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Converts a `HipStr` into a `HipByt`.
    ///
    /// It consumes the `HipStr` without copying the content
    /// (if [shared][HipByt::is_allocated] or [static][HipByt::is_static]).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let s = HipStr::from("hello");
    /// let b = s.into_bytes();
    ///
    /// assert_eq!(&[104, 101, 108, 108, 111][..], &b[..]);
    /// ```
    #[allow(clippy::missing_const_for_fn)] // cannot const it for now, clippy bug
    #[must_use]
    pub fn into_bytes(self) -> HipByt<'borrow, B> {
        self.0
    }

    /// Extracts a string slice of the entire `HipStr`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let s = HipStr::from("foobar");
    ///
    /// assert_eq!("foobar", s.as_str());
    /// ```
    #[inline]
    #[must_use]
    pub const fn as_str(&self) -> &str {
        // SAFETY: type invariant
        unsafe { std::str::from_utf8_unchecked(self.0.as_slice()) }
    }

    /// Extracts a mutable string slice of the entire `HipStr` if possible.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let mut s = HipStr::from("foo");
    /// let slice = s.as_mut_str().unwrap();
    /// slice.make_ascii_uppercase();
    /// assert_eq!("FOO", slice);
    /// ```
    #[must_use]
    pub fn as_mut_str(&mut self) -> Option<&mut str> {
        self.0.as_mut_slice().map(|slice|
                // SAFETY: type invariant
                unsafe { std::str::from_utf8_unchecked_mut(slice) })
    }

    /// Extracts a mutable string slice of the entire `HipStr` changing the
    /// representation (and thus _potentially reallocating_) if the current
    /// representation cannot be mutated.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let mut s = HipStr::borrowed("foo");
    /// let slice = s.to_mut_str();
    /// slice.make_ascii_uppercase();
    /// assert_eq!("FOO", slice);
    /// ```
    #[must_use]
    pub fn to_mut_str(&mut self) -> &mut str {
        let slice = self.0.to_mut_slice();
        // SAFETY: type invariant
        unsafe { std::str::from_utf8_unchecked_mut(slice) }
    }

    /// Extracts a slice as its own `HipStr`.
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
    /// # use hipstr::HipStr;
    /// let a = HipStr::from("abc");
    /// assert_eq!(a.slice(0..2), HipStr::from("ab"));
    /// ```
    #[must_use]
    #[track_caller]
    pub fn slice(&self, range: impl RangeBounds<usize>) -> Self {
        match self.try_slice(range) {
            Ok(result) => result,
            Err(err) => panic!("{}", err),
        }
    }

    /// Returns a `HipStr` of a range of bytes in this `HipStr`, if the range is
    /// valid and at char boundaries.
    ///
    /// # Errors
    ///
    /// This function will return an error if the range is invalid or if the
    /// range is not at char boundaries.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let a = HipStr::from("Rust \u{1F980}");
    /// assert_eq!(a.try_slice(0..4), Ok(HipStr::from("Rust")));
    /// assert!(a.try_slice(5..6).is_err());
    /// ```
    pub fn try_slice(&self, range: impl RangeBounds<usize>) -> Result<Self, SliceError<B>> {
        let range = simplify_range(range, self.len())
            .map_err(|(start, end, kind)| SliceError::new(kind, start, end, self))?;
        if !self.is_char_boundary(range.start) {
            Err(SliceError {
                kind: SliceErrorKind::StartNotACharBoundary,
                start: range.start,
                end: range.end,
                string: self,
            })
        } else if !self.is_char_boundary(range.end) {
            Err(SliceError {
                kind: SliceErrorKind::EndNotACharBoundary,
                start: range.start,
                end: range.end,
                string: self,
            })
        } else {
            Ok(Self(self.0.slice_unchecked(range)))
        }
    }

    /// Decodes a UTF-16–encoded vector `v` into a `HipStr`.
    ///
    /// # Errors
    ///
    /// Returns an [`FromUtf16Error`] if `v` contains any invalid data.
    ///
    /// [`FromUtf16Error`]: std::string::FromUtf16Error
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// // 𝄞music
    /// let v = &[0xD834, 0xDD1E, 0x006d, 0x0075,
    ///           0x0073, 0x0069, 0x0063];
    /// assert_eq!(HipStr::from("𝄞music"),
    ///            HipStr::from_utf16(v).unwrap());
    ///
    /// // 𝄞mu<invalid>ic
    /// let v = &[0xD834, 0xDD1E, 0x006d, 0x0075,
    ///           0xD800, 0x0069, 0x0063];
    /// assert!(HipStr::from_utf16(v).is_err());
    /// ```
    #[inline]
    pub fn from_utf16(v: &[u16]) -> Result<Self, FromUtf16Error> {
        String::from_utf16(v).map(Into::into)
    }

    /// Decodes a UTF-16–encoded slice `v` into a `HipStr`, replacing
    /// invalid data with [the replacement character (`U+FFFD`)][U+FFFD].
    ///
    /// [U+FFFD]: core::char::REPLACEMENT_CHARACTER
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// // 𝄞mus<invalid>ic<invalid>
    /// let v = &[0xD834, 0xDD1E, 0x006d, 0x0075,
    ///           0x0073, 0xDD1E, 0x0069, 0x0063,
    ///           0xD834];
    ///
    /// assert_eq!(String::from("𝄞mus\u{FFFD}ic\u{FFFD}"),
    ///            String::from_utf16_lossy(v));
    /// ```
    #[inline]
    #[must_use]
    pub fn from_utf16_lossy(v: &[u16]) -> Self {
        String::from_utf16_lossy(v).into()
    }

    /// Converts a [`HipByt`] to a `HipStr` without checking that the
    /// string contains valid UTF-8.
    ///
    /// See the safe version, [`from_utf8`](HipStr::from_utf8), for more details.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it does not check that the bytes passed
    /// to it are valid UTF-8. If this constraint is violated, it may cause
    /// memory unsafety issues with future users of the `HipStr`, as the rest of
    /// the library assumes that `HipStr`s are valid UTF-8.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// // some bytes, in a vector
    /// let sparkle_heart = vec![240, 159, 146, 150];
    ///
    /// let sparkle_heart = unsafe {
    ///     String::from_utf8_unchecked(sparkle_heart)
    /// };
    ///
    /// assert_eq!("💖", sparkle_heart);
    /// ```
    #[inline]
    #[must_use]
    pub const unsafe fn from_utf8_unchecked(byt: HipByt<'borrow, B>) -> Self {
        Self(byt)
    }

    /// Converts a [`HipByt`] (a sequence of bytes) to a `HipStr`.
    ///
    /// Both [`HipByt`] and [`HipStr`] are made of bytes, so this function
    /// converts between the two without any coping allocated data. However, not
    /// all byte sequence are valid strings: `HipStr` (like `std`'s [`String`])
    /// requires that it is valid UTF-8. `from_utf8()` checks to ensure that
    /// the bytes are valid UTF-8, and then does the conversion.
    ///
    /// If you are sure that the byte slice is valid UTF-8, and you don't want
    /// to incur the overhead of the validity check, there is an unsafe version
    /// of this function, [`from_utf8_unchecked`], which has the same behavior
    /// but skips the check.
    ///
    /// The inverse of this method is [`into_bytes`].
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if the slice is not UTF-8 with a description as to why the
    /// provided bytes are not UTF-8. The vector you moved in is also included.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::{HipByt, HipStr};
    /// // some bytes, in a vector
    /// let sparkle_heart = HipByt::borrowed(&[240, 159, 146, 150]);
    ///
    /// // We know these bytes are valid, so we'll use `unwrap()`.
    /// let sparkle_heart = HipStr::from_utf8(sparkle_heart).unwrap();
    ///
    /// assert_eq!("💖", sparkle_heart);
    /// ```
    ///
    /// Incorrect bytes:
    ///
    /// ```
    /// # use hipstr::{HipByt, HipStr};
    /// // some invalid bytes, in a vector
    /// let sparkle_heart = HipByt::borrowed(&[0, 159, 146, 150]);
    ///
    /// assert!(HipStr::from_utf8(sparkle_heart).is_err());
    /// ```
    ///
    /// See the docs for [`FromUtf8Error`] for more details on what you can do
    /// with this error.
    ///
    /// [`from_utf8_unchecked`]: HipStr::from_utf8_unchecked
    /// [`into_bytes`]: HipStr::into_bytes
    #[inline]
    pub fn from_utf8(bytes: HipByt<'borrow, B>) -> Result<Self, FromUtf8Error<'borrow, B>> {
        match std::str::from_utf8(&bytes) {
            Ok(_) => {
                // SAFETY: checked above
                Ok(unsafe { Self::from_utf8_unchecked(bytes) })
            }
            Err(e) => Err(FromUtf8Error { bytes, error: e }),
        }
    }

    /// Converts a [`HipByt`] to a `HipStr`, including invalid characters.
    ///
    /// Strings are made of bytes ([`u8`]). However, not all byte sequences are
    /// valid strings: strings are required to be valid UTF-8. During this
    /// conversion, `from_utf8_lossy()` will replace any invalid UTF-8 sequences
    /// with [`U+FFFD REPLACEMENT CHARACTER`][U+FFFD], which looks like this: �
    ///
    /// [U+FFFD]: core::char::REPLACEMENT_CHARACTER
    ///
    /// If you are sure that the byte slice is valid UTF-8, and you don't want
    /// to incur the overhead of the conversion, there is an unsafe version
    /// of this function, [`from_utf8_unchecked`], which has the same behavior
    /// but skips the checks.
    ///
    /// [`from_utf8_unchecked`]: HipStr::from_utf8_unchecked
    ///
    /// If our byte sequence is invalid UTF-8, then we need to insert the
    /// replacement characters, which will change the size of the string, and
    /// hence, require to allocate a new string. But if it's already valid
    /// UTF-8, we don't need a new allocation and the output reuses the
    /// allocated data of the source.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::{HipByt, HipStr};
    /// // some bytes, in a vector
    /// let sparkle_heart = HipByt::from(vec![240, 159, 146, 150]);
    ///
    /// let sparkle_heart = HipStr::from_utf8_lossy(sparkle_heart);
    ///
    /// assert_eq!("💖", sparkle_heart);
    /// ```
    ///
    /// Incorrect bytes:
    ///
    /// ```
    /// # use hipstr::{HipByt, HipStr};
    /// // some invalid bytes
    /// let input = HipByt::borrowed(b"Hello \xF0\x90\x80World");
    /// let output = HipStr::from_utf8_lossy(input);
    ///
    /// assert_eq!("Hello �World", output);
    /// ```
    #[inline]
    #[must_use]
    pub fn from_utf8_lossy(bytes: HipByt<'borrow, B>) -> Self {
        match String::from_utf8_lossy(&bytes) {
            Cow::Borrowed(_) => Self(bytes),
            Cow::Owned(s) => Self::from(s),
        }
    }

    /// Returns the maximal length (in bytes) of inline string.
    #[inline]
    #[must_use]
    pub const fn inline_capacity() -> usize {
        HipByt::<B>::inline_capacity()
    }

    /// Returns the total number of bytes the backend can hold.
    ///
    /// # Example
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let mut s: String = String::with_capacity(10);
    /// s.push('a');
    /// let string = HipStr::from(s);
    /// assert_eq!(string.capacity(), 10);
    /// ```
    #[inline]
    pub fn capacity(&self) -> usize {
        self.0.capacity()
    }

    /// Converts `self` into a [`String`] without clone or allocation if possible.
    ///
    /// # Errors
    ///
    /// Returns `Err(self)` if it is impossible to take ownership of the string
    /// backing this `HipStr`.
    #[inline]
    pub fn into_string(self) -> Result<String, Self> {
        self.0
            .into_vec()
            .map(|v| unsafe { String::from_utf8_unchecked(v) })
            .map_err(Self)
    }

    /// Returns a mutable handle to the underlying [`String`].
    ///
    /// This operation may reallocate a new string if either:
    ///
    /// - the representation is not an allocated buffer (inline array or static borrow),
    /// - the underlying buffer is shared.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hipstr::HipStr;
    /// let mut s = HipStr::borrowed("abc");
    /// {
    ///     let mut r = s.mutate();
    ///     r.push_str("def");
    ///     assert_eq!(r.as_str(), "abcdef");
    /// }
    /// assert_eq!(s, "abcdef");
    /// ```
    #[inline]
    #[must_use]
    pub fn mutate(&mut self) -> RefMut<'_, 'borrow, B> {
        let owned = unsafe { String::from_utf8_unchecked(self.0.take_vec()) };
        RefMut {
            result: self,
            owned,
        }
    }

    /// Transforms to the inline representation, returning a new inline `HipStr`
    /// and consuming this `HipStr`.
    ///
    /// # Errors
    ///
    /// Returns the original `HipStr` if it cannot be inlined, i.e.,
    /// if the length greater than [`HipStr::inline_capacity()`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hipstr::HipStr;
    /// let s = "A".repeat(42);
    /// let mut h = HipStr::from(s);
    /// assert!(h.is_allocated());
    /// assert!(!h.is_inline());
    /// assert!(h.inline().is_err());
    ///
    /// let s = "abc".to_string();
    /// let h = HipStr::from(s);
    /// assert!(h.is_allocated());
    /// assert!(!h.is_inline());
    /// let h = h.inline().unwrap();
    /// assert!(h.is_inline());
    /// ```
    #[inline]
    pub fn inline(self) -> Result<Self, Self> {
        self.0.inline().map(Self).map_err(Self)
    }
}

// Manual implementation needed to remove trait bound on B::RawPointer.
impl<'borrow, B> Clone for HipStr<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

// Manual implementation needed to remove trait bound on B::RawPointer.
impl<'borrow, B> Default for HipStr<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<'borrow, B> Deref for HipStr<'borrow, B>
where
    B: Backend,
{
    type Target = str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl<'borrow, B> Borrow<str> for HipStr<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl<'borrow, B> Hash for HipStr<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_str().hash(state);
    }
}

// Formatting

impl<'borrow, B> fmt::Debug for HipStr<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.as_str(), f)
    }
}

impl<'borrow, B> fmt::Display for HipStr<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.as_str(), f)
    }
}

/// Slice error kinds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SliceErrorKind {
    /// Start index should be less or equal to the end index.
    StartGreaterThanEnd,

    /// Start index out of bounds.
    StartOutOfBounds,

    /// End index out of bounds.
    EndOutOfBounds,

    /// Start index is not at a char boundary.
    StartNotACharBoundary,

    /// End index is not at a char boundary.
    EndNotACharBoundary,
}

/// A possible error value when slicing a [`HipStr`].
///
/// This type is the error type for [`HipStr::try_slice`].
#[derive(PartialEq, Eq, Clone)]
pub struct SliceError<'a, 'borrow, B>
where
    B: Backend,
{
    kind: SliceErrorKind,
    start: usize,
    end: usize,
    string: &'a HipStr<'borrow, B>,
}

impl<'a, 'borrow, B> SliceError<'a, 'borrow, B>
where
    B: Backend,
{
    const fn new(
        kind: ByteSliceErrorKind,
        start: usize,
        end: usize,
        string: &'a HipStr<'borrow, B>,
    ) -> Self {
        let kind = match kind {
            ByteSliceErrorKind::StartGreaterThanEnd => SliceErrorKind::StartGreaterThanEnd,
            ByteSliceErrorKind::StartOutOfBounds => SliceErrorKind::StartOutOfBounds,
            ByteSliceErrorKind::EndOutOfBounds => SliceErrorKind::EndOutOfBounds,
        };
        Self {
            kind,
            start,
            end,
            string,
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
    pub const fn source(&self) -> &HipStr<'borrow, B> {
        self.string
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
            .field("string", &self.string)
            .finish()
    }
}

impl<'a, 'borrow, B> fmt::Display for SliceError<'a, 'borrow, B>
where
    B: Backend,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            SliceErrorKind::StartGreaterThanEnd => write!(
                f,
                "range starts at {} but ends at {} when slicing `{}`",
                self.start, self.end, self.string
            ),
            SliceErrorKind::StartOutOfBounds => write!(
                f,
                "range start index {} is out of bounds of `{}`",
                self.start, self.string
            ),
            SliceErrorKind::EndOutOfBounds => write!(
                f,
                "range end index {} is out of bounds of `{}`",
                self.end, self.string
            ),
            SliceErrorKind::StartNotACharBoundary => write!(
                f,
                "range start index {} is not a char boundary of `{}`",
                self.start, self.string
            ),
            SliceErrorKind::EndNotACharBoundary => write!(
                f,
                "range end index {} is not a char boundary of `{}`",
                self.end, self.string
            ),
        }
    }
}

impl<'a, 'borrow, B> Error for SliceError<'a, 'borrow, B> where B: Backend {}

/// A possible error value when converting a [`HipStr`] from a [`HipByt`].
///
/// This type is the error type for the [`from_utf8`] method on [`HipStr`]. It
/// is designed in such a way to carefully avoid reallocations: the
/// [`into_bytes`] method will give back the byte vector that was used in the
/// conversion attempt.
///
/// [`from_utf8`]: HipStr::from_utf8
/// [`into_bytes`]: FromUtf8Error::into_bytes
///
/// The [`Utf8Error`] type provided by [`std::str`] represents an error that may
/// occur when converting a slice of [`u8`]s to a [`&str`]. In this sense, it's
/// an analogue to `FromUtf8Error`, and you can get one from a `FromUtf8Error`
/// through the [`utf8_error`] method.
///
/// [`Utf8Error`]: std::str::Utf8Error
/// [`std::str`]: std::str
/// [`&str`]: prim@str "&str"
/// [`utf8_error`]: FromUtf8Error::utf8_error
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// // some invalid bytes, in a vector
/// let bytes = vec![0, 159];
///
/// let value = String::from_utf8(bytes);
///
/// assert!(value.is_err());
/// assert_eq!(vec![0, 159], value.unwrap_err().into_bytes());
/// ```
#[derive(PartialEq, Eq, Clone)]
pub struct FromUtf8Error<'borrow, B>
where
    B: Backend,
{
    pub(super) bytes: HipByt<'borrow, B>,
    pub(super) error: Utf8Error,
}

impl<'borrow, B> fmt::Debug for FromUtf8Error<'borrow, B>
where
    B: Backend,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("FromUtf8Error")
            .field("bytes", &self.bytes)
            .field("error", &self.error)
            .finish()
    }
}

impl<'borrow, B> FromUtf8Error<'borrow, B>
where
    B: Backend,
{
    /// Returns a slice of [`u8`]s bytes that were attempted to convert to a `HipStr`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::{HipStr, HipByt};
    /// // some invalid bytes, in a vector
    /// let bytes = HipByt::from(vec![0, 159]);
    ///
    /// let value = HipStr::from_utf8(bytes);
    ///
    /// assert_eq!(&[0, 159], value.unwrap_err().as_bytes());
    /// ```
    #[must_use]
    pub const fn as_bytes(&self) -> &[u8] {
        self.bytes.as_slice()
    }

    /// Returns the bytes that were attempted to convert to a `HipStr`.
    ///
    /// This method is carefully constructed to avoid allocation. It will
    /// consume the error, moving out the bytes, so that a copy of the bytes
    /// does not need to be made.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::{HipStr, HipByt};
    /// // some invalid bytes, in a vector
    /// let bytes = HipByt::from(vec![0, 159]);
    ///
    /// let value = HipStr::from_utf8(bytes.clone());
    ///
    /// assert_eq!(bytes, value.unwrap_err().into_bytes());
    /// ```
    #[allow(clippy::missing_const_for_fn)] // cannot const it for now, clippy bug
    #[must_use]
    pub fn into_bytes(self) -> HipByt<'borrow, B> {
        self.bytes
    }

    /// Fetch a `Utf8Error` to get more details about the conversion failure.
    ///
    /// The [`Utf8Error`] type provided by [`std::str`] represents an error that may
    /// occur when converting a slice of [`u8`]s to a [`&str`]. In this sense, it's
    /// an analogue to `FromUtf8Error`. See its documentation for more details
    /// on using it.
    ///
    /// [`std::str`]: core::str "std::str"
    /// [`&str`]: prim@str "&str"
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::{HipStr, HipByt};
    /// // some invalid bytes, in a vector
    /// let bytes = HipByt::from(vec![0, 159]);
    ///
    /// let error = HipStr::from_utf8(bytes).unwrap_err().utf8_error();
    ///
    /// // the first byte is invalid here
    /// assert_eq!(1, error.valid_up_to());
    /// ```
    #[must_use]
    pub const fn utf8_error(&self) -> Utf8Error {
        self.error
    }
}

impl<'borrow, B> fmt::Display for FromUtf8Error<'borrow, B>
where
    B: Backend,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.error, f)
    }
}

impl<'borrow, B> Error for FromUtf8Error<'borrow, B> where B: Backend {}

/// A wrapper type for a mutably borrowed [`String`] out of a [`HipStr`].
pub struct RefMut<'a, 'borrow, B>
where
    B: Backend,
{
    result: &'a mut HipStr<'borrow, B>,
    owned: String,
}

impl<'a, 'borrow, B> Drop for RefMut<'a, 'borrow, B>
where
    B: Backend,
{
    fn drop(&mut self) {
        let owned = std::mem::take(&mut self.owned);
        *self.result = HipStr::from(owned);
    }
}

impl<'a, 'borrow, B> Deref for RefMut<'a, 'borrow, B>
where
    B: Backend,
{
    type Target = String;
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

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use super::SliceErrorKind;
    use crate::{HipByt, HipStr};

    const INLINE_CAPACITY: usize = HipStr::inline_capacity();

    #[test]
    fn test_new_default() {
        let new = HipStr::new();
        assert_eq!(new, "");
        assert!(new.is_empty());

        let new = HipStr::default();
        assert_eq!(new, "");
        assert!(new.is_empty());
    }

    #[test]
    fn test_borrow_and_hash() {
        let mut set = HashSet::new();
        set.insert(HipStr::from("a"));
        set.insert(HipStr::from("b"));

        assert!(set.contains("a"));
        assert!(!set.contains("c"));
    }

    #[test]
    fn test_fmt() {
        let source = "Rust \u{1F980}";
        let a = HipStr::borrowed(source);
        assert_eq!(format!("{}", a), source);
        assert_eq!(format!("{:?}", a), format!("{:?}", source),);
    }

    #[test]
    fn test_from_string() {
        let s = "A".repeat(42);
        let hs = HipStr::from(s.clone());
        assert!(!hs.is_static());
        assert!(!hs.is_inline());
        assert!(hs.is_allocated());
        assert_eq!(hs.len(), 42);
        assert_eq!(hs.as_str(), s.as_str());
    }

    #[test]
    fn test_borrowed() {
        let s = "0123456789";
        let string = HipStr::borrowed(s);
        assert!(string.is_static());
        assert!(!string.is_inline());
        assert_eq!(string.len(), s.len());
        assert_eq!(string.as_str(), s);
        assert_eq!(string.as_ptr(), s.as_ptr());
    }

    #[test]
    fn test_from_slice() {
        static V: &[u8] = &[b'a'; 1024];
        let s = std::str::from_utf8(V).unwrap();

        for size in [0, 1, INLINE_CAPACITY, INLINE_CAPACITY + 1, 256, 1024] {
            let string = HipStr::from(&s[..size]);
            assert_eq!(size > 0 && size <= INLINE_CAPACITY, string.is_inline());
            assert!(size == 0 || !string.is_static());
            assert_eq!(string.len(), size);
        }
    }

    #[test]
    fn test_as_slice() {
        // static
        {
            let a = HipStr::borrowed("abc");
            assert!(a.is_static());
            assert!(!a.is_inline());
            assert!(!a.is_allocated());
            assert_eq!(a.as_str(), "abc");
        }
        // inline
        {
            let a = HipStr::from("abc");
            assert!(!a.is_static());
            assert!(a.is_inline());
            assert!(!a.is_allocated());
            assert_eq!(a.as_str(), "abc");
        }
        // allocated
        {
            let s = "A".repeat(42);
            let a = HipStr::from(s.as_str());
            assert!(!a.is_static());
            assert!(!a.is_inline());
            assert!(a.is_allocated());
            assert_eq!(a.as_str(), s.as_str());
        }
    }

    #[test]
    fn test_clone() {
        // static
        {
            let s: &'static str = "abc";
            let a = HipStr::borrowed(s);
            assert!(a.is_static());
            let b = a.clone();
            drop(a);
            assert_eq!(b.as_str(), "abc");
            assert_eq!(s.as_ptr(), b.as_ptr());
        }

        // inline
        {
            let a = HipStr::from("abc");
            assert!(a.is_inline());
            let b = a.clone();
            drop(a);
            assert_eq!(b.as_str(), "abc");
        }

        // allocated
        {
            let s = "a".repeat(42);
            let p = s.as_ptr();
            let a = HipStr::from(s);
            assert!(a.is_allocated());
            let b = a.clone();
            drop(a);
            assert_eq!(b.as_str(), "a".repeat(42).as_str());
            assert_eq!(b.as_ptr(), p);
        }
    }

    #[test]
    fn test_into_static() {
        // static
        let a = HipStr::borrowed("abc");
        assert_eq!(a.into_borrowed(), Ok("abc"));

        // inline
        let a = HipStr::from("abc");
        let b = a.clone();
        assert_eq!(a.into_borrowed(), Err(b));

        // heap
        let a = HipStr::from("a".repeat(42).as_str());
        let b = a.clone();
        assert_eq!(a.into_borrowed(), Err(b));
    }

    #[test]
    fn test_into_bytes() {
        let s = HipStr::from("A".repeat(42));
        let bytes = s.into_bytes();
        assert_eq!(bytes.len(), 42);
        assert_eq!(bytes.as_slice(), [b'A'; 42]);
    }

    #[test]
    fn test_as_mut_str() {
        // static
        let mut a = HipStr::borrowed("abc");
        assert_eq!(a.as_mut_str(), None);

        // inline
        let mut a = HipStr::from("abc");
        assert!(a.is_inline());
        assert_eq!(a.as_mut_str(), Some(String::from("abc").as_mut_str()));

        // heap
        let mut a = HipStr::from("a".repeat(42).as_str());
        {
            let sl = a.as_mut_str();
            assert_eq!(sl, Some("a".repeat(42).as_mut_str()));
            unsafe {
                sl.unwrap().as_bytes_mut()[0] = b'b';
            }
        }
        let mut b = a.clone();
        assert!(b.starts_with("b"));
        assert_eq!(b.as_mut_str(), None);
        let _ = a.as_str();
    }

    #[test]
    fn test_to_mut_str() {
        {
            // static
            let mut a = HipStr::borrowed("abc");
            assert!(a.is_static());
            assert_eq!(a.to_mut_str(), "abc".to_string().as_mut_str());
            assert!(a.is_inline());
        }

        {
            // inline
            let mut a = HipStr::from("abc");
            assert!(a.is_inline());
            assert_eq!(a.to_mut_str(), "abc".to_string().as_mut_str());
            assert!(a.is_inline());
        }

        {
            // heap
            let mut a = HipStr::from("a".repeat(42).as_str());
            assert!(a.is_allocated());
            {
                let sl = a.to_mut_str();
                assert_eq!(sl, "a".repeat(42).as_mut_str());
                sl.make_ascii_uppercase();
            }

            let mut b = a.clone();
            assert_eq!(b, "A".repeat(42));
            let _ = b.to_mut_str();
            assert_ne!(b.as_ptr(), a.as_ptr());
            assert!(b.is_allocated());
        }
    }

    #[test]
    fn test_slice() {
        let v = "a".repeat(INLINE_CAPACITY);
        let s = HipStr::from(&v[..]);
        let sl = s.slice(0..10);
        assert_eq!(&sl, &v[0..10]);

        let v = "a".repeat(42);
        let s = HipStr::from(&v[..]);

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
        let a = HipStr::borrowed("abc");
        let _b = a.slice(4..=4);
    }

    #[test]
    #[should_panic]
    fn test_slice_panic_end() {
        let a = HipStr::borrowed("abc");
        let _b = a.slice(0..5);
    }

    #[test]
    #[should_panic]
    fn test_slice_panic_mixed() {
        let a = HipStr::borrowed("abc");
        let _b = a.slice(3..2);
    }

    #[test]
    #[should_panic]
    fn test_slice_panic_start_char_boundary() {
        let a = HipStr::borrowed("\u{1F980}");
        let _b = a.slice(1..);
    }

    #[test]
    #[should_panic]
    fn test_slice_panic_end_char_boundary() {
        let a = HipStr::borrowed("\u{1F980}");
        let _b = a.slice(0..2);
    }

    #[test]
    fn test_try_slice() {
        let a = HipStr::borrowed("Rust \u{1F980}");

        let err = a.try_slice(10..).unwrap_err();
        assert_eq!(err.kind(), SliceErrorKind::StartOutOfBounds);
        assert_eq!(err.start(), 10);
        assert_eq!(err.end(), a.len());
        assert_eq!(err.range(), 10..a.len());
        assert!(std::ptr::eq(err.source(), &a));
        assert_eq!(
            format!("{err:?}"),
            "SliceError { kind: StartOutOfBounds, start: 10, end: 9, string: \"Rust \u{1F980}\" }"
        );
        assert_eq!(
            format!("{err}"),
            "range start index 10 is out of bounds of `Rust \u{1F980}`"
        );

        let err = a.try_slice(..10).unwrap_err();
        assert_eq!(
            format!("{err}"),
            "range end index 10 is out of bounds of `Rust \u{1F980}`"
        );

        let err = a.try_slice(4..2).unwrap_err();
        assert_eq!(
            format!("{err}"),
            "range starts at 4 but ends at 2 when slicing `Rust \u{1F980}`"
        );

        let err = a.try_slice(6..).unwrap_err();
        assert_eq!(
            format!("{err}"),
            "range start index 6 is not a char boundary of `Rust \u{1F980}`"
        );

        let err = a.try_slice(..6).unwrap_err();
        assert_eq!(
            format!("{err}"),
            "range end index 6 is not a char boundary of `Rust \u{1F980}`"
        );
    }

    #[test]
    fn test_from_utf8() {
        let bytes = HipByt::borrowed(b"abc\x80");
        let err = HipStr::from_utf8(bytes.clone()).unwrap_err();
        assert!(std::ptr::eq(err.as_bytes(), bytes.as_slice()));
        assert_eq!(err.utf8_error().valid_up_to(), 3);
        assert_eq!(format!("{err:?}"), "FromUtf8Error { bytes: [97, 98, 99, 128], error: Utf8Error { valid_up_to: 3, error_len: Some(1) } }");
        assert_eq!(
            format!("{err}"),
            "invalid utf-8 sequence of 1 bytes from index 3"
        );
        let bytes_clone = err.into_bytes();
        assert_eq!(bytes_clone.as_ptr(), bytes.as_ptr());
        assert_eq!(bytes_clone.len(), bytes.len());

        let bytes = HipByt::from(b"abc".repeat(10));
        let string = HipStr::from_utf8(bytes.clone()).unwrap();
        assert_eq!(bytes.as_ptr(), string.as_ptr());
    }

    #[test]
    fn test_from_utf8_lossy() {
        let bytes = HipByt::borrowed(b"abc\x80");
        let string = HipStr::from_utf8_lossy(bytes.clone());
        assert!(string.len() > bytes.len());

        let bytes = HipByt::from(b"abc".repeat(10));
        let string = HipStr::from_utf8_lossy(bytes.clone());
        assert_eq!(bytes.as_ptr(), string.as_ptr());
    }

    #[test]
    fn test_capacity() {
        let a = HipStr::borrowed("abc");
        assert_eq!(a.capacity(), a.len());

        let a = HipStr::from("abc");
        assert_eq!(a.capacity(), HipStr::inline_capacity());

        let mut v = String::with_capacity(42);
        v.push_str("abc");
        let a = HipStr::from(v);
        assert_eq!(a.capacity(), 42);
    }

    #[test]
    fn test_mutate() {
        {
            // static
            let mut a = HipStr::borrowed("abc");
            assert!(a.is_static(), "a should be static");
            a.mutate().push_str("def");
            assert!(a.is_allocated(), "a should be allocated at the end");
            assert_eq!(a, "abcdef", "should be modified");
        }

        {
            // inline
            let mut a = HipStr::from("abc");
            assert!(a.is_inline(), "a should be inline at the start");
            a.mutate().push_str("def");
            assert!(a.is_allocated(), "a should be allocated at the end");
            assert_eq!(a, "abcdef", "should be modified");
        }

        {
            // allocated, unique with enough capacity
            let mut v = String::with_capacity(6);
            v.push_str("abc");
            let p = v.as_ptr();
            let mut a = HipStr::from(v);
            assert!(a.is_allocated(), "should be allocated at the start");
            a.mutate().push_str("def");
            assert!(a.is_allocated(), "should be allocated at the end");
            assert_eq!(a, "abcdef", "should be modified");
            assert_eq!(a.as_ptr(), p, "should have same backend vector");
        }

        {
            // allocated, shared
            let mut v = String::with_capacity(6);
            v.push_str("abc");
            let mut a = HipStr::from(v);
            assert!(a.is_allocated(), "a should be allocated at the start");
            let b = a.clone();
            a.mutate().push_str("def");
            assert!(a.is_allocated(), "a should be allocated at the end");
            assert_eq!(a, "abcdef", "a should be modified");
            assert_eq!(b, "abc", "b should not be modified");
            assert_ne!(a.as_ptr(), b.as_ptr(), "different backend vector");
        }
    }
}
