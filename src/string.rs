//! String.
//!
//! This module provides the [`HipStr`] type as well as the associated helper and error types.

use core::borrow::Borrow;
use core::error::Error;
use core::hash::Hash;
use core::mem::transmute;
use core::ops::{Deref, DerefMut, Range, RangeBounds};
use core::str::{Lines, SplitAsciiWhitespace, SplitWhitespace, Utf8Error};

use self::pattern::{DoubleEndedPattern, IterWrapper, Pattern, ReversePattern};
use crate::alloc::borrow::Cow;
use crate::alloc::fmt;
use crate::alloc::string::{FromUtf16Error, String};
use crate::bytes::{simplify_range, HipByt, SliceErrorKind as ByteSliceErrorKind};
use crate::Backend;

mod cmp;
mod convert;
mod pattern;
#[cfg(feature = "serde")]
pub mod serde;
#[cfg(test)]
mod tests;

/// Smart string, i.e. cheaply clonable and sliceable string.
///
/// Internally used the same representations as [`HipByt`].
///
/// # Examples
///
/// You can create a `HipStr` from a [string slice (`&str`)][str], an owned string
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
    /// # use hipstr::HipStr;
    /// let s = HipStr::new();
    /// ```
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self(HipByt::new())
    }

    /// Creates a new `HipStr` with the given capacity.
    ///
    /// The returned `HipStr` will be able to hold at least `capacity` bytes
    /// without reallocating or changing representation.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let mut s = HipStr::with_capacity(42);
    /// for _ in 0..42 {
    ///     s.push('*');
    /// }
    /// assert_eq!(s, "*".repeat(42));
    /// ```
    #[inline]
    #[must_use]
    pub fn with_capacity(cap: usize) -> Self {
        Self(HipByt::with_capacity(cap))
    }

    /// Creates a new `HipStr` from a string slice.
    /// No heap allocation is performed.
    /// **The string is not copied.**
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
    /// assert!(s.is_borrowed());
    ///
    /// let s = HipStr::from("hello");
    /// assert!(!s.is_borrowed());
    ///
    /// let s = HipStr::from("hello".repeat(10));
    /// assert!(!s.is_borrowed());
    /// ```
    #[inline]
    #[must_use]
    pub const fn is_borrowed(&self) -> bool {
        self.0.is_borrowed()
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
                unsafe { core::str::from_utf8_unchecked(slice) })
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
    /// (if [shared][HipByt::is_allocated] or [static][HipByt::is_borrowed]).
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
        let slice = self.0.as_slice();
        // SAFETY: type invariant
        unsafe { core::str::from_utf8_unchecked(slice) }
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
    #[inline]
    #[must_use]
    pub fn as_mut_str(&mut self) -> Option<&mut str> {
        self.0.as_mut_slice().map(|slice|
                // SAFETY: type invariant
                unsafe { core::str::from_utf8_unchecked_mut(slice) })
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
    #[inline]
    #[must_use]
    pub fn to_mut_str(&mut self) -> &mut str {
        let slice = self.0.to_mut_slice();
        // SAFETY: type invariant
        unsafe { core::str::from_utf8_unchecked_mut(slice) }
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
            return Err(SliceError {
                kind: SliceErrorKind::StartNotACharBoundary,
                start: range.start,
                end: range.end,
                string: self,
            });
        }

        if !self.is_char_boundary(range.end) {
            return Err(SliceError {
                kind: SliceErrorKind::EndNotACharBoundary,
                start: range.start,
                end: range.end,
                string: self,
            });
        }

        // SAFETY: range and char boundaries checked above
        Ok(unsafe { self.slice_unchecked(range) })
    }

    /// Extracts a slice as its own `HipStr`.
    ///
    /// # Safety
    ///
    /// `range` must be a equivalent to some `a..b` with `a <= b <= len`.
    /// Also, both ends should be **character boundaries**.
    /// UB in release mode.
    ///
    /// # Panics
    ///
    /// Panics in debug mode if the safety condition is not ensured.
    #[must_use]
    pub unsafe fn slice_unchecked(&self, range: impl RangeBounds<usize>) -> Self {
        #[cfg(debug_assertions)]
        {
            let range =
                simplify_range((range.start_bound(), range.end_bound()), self.len()).unwrap();
            assert!(self.is_char_boundary(range.start));
            assert!(self.is_char_boundary(range.end));
        }
        Self(unsafe { self.0.slice_unchecked(range) })
    }

    /// Extracts a slice as its own `HipStr` based on the given subslice `&str`.
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
    /// # use hipstr::HipStr;
    /// let a = HipStr::from("abc");
    /// let sl = &a[0..2];
    /// assert_eq!(a.slice_ref(sl), HipStr::from("ab"));
    /// ```
    #[must_use]
    #[track_caller]
    pub fn slice_ref(&self, slice: &str) -> Self {
        let Some(result) = self.try_slice_ref(slice) else {
            panic!("slice {slice:p} is not a part of {self:p}")
        };
        result
    }

    /// Extracts a slice as its own `HipStr` based on the given subslice `&str`.
    ///
    /// # Safety
    ///
    /// The slice MUST be a part of this `HipStr`.
    #[must_use]
    pub unsafe fn slice_ref_unchecked(&self, slice: &str) -> Self {
        let slice = slice.as_bytes();
        unsafe { Self(self.0.slice_ref_unchecked(slice)) }
    }

    /// Returns a slice as it own `HipStr` based on the given subslice `&str`.
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
    /// # use hipstr::HipStr;
    /// let a = HipStr::from("abc");
    /// let sl = &a[0..2];
    /// assert_eq!(a.try_slice_ref(sl), Some(HipStr::from("ab")));
    /// assert!(a.try_slice_ref("z").is_none());
    /// ```
    pub fn try_slice_ref(&self, range: &str) -> Option<Self> {
        self.0.try_slice_ref(range.as_bytes()).map(Self)
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
    /// # use hipstr::HipStr;
    /// // 𝄞mus<invalid>ic<invalid>
    /// let v = &[0xD834, 0xDD1E, 0x006d, 0x0075,
    ///           0x0073, 0xDD1E, 0x0069, 0x0063,
    ///           0xD834];
    ///
    /// assert_eq!("𝄞mus\u{FFFD}ic\u{FFFD}",
    ///            HipStr::from_utf16_lossy(v));
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
        match core::str::from_utf8(&bytes) {
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
    /// let mut s: String = String::with_capacity(42);
    /// s.extend('a'..='z');
    /// let string = HipStr::from(s);
    /// assert_eq!(string.len(), 26);
    /// assert_eq!(string.capacity(), 42);
    ///
    /// let string2 = string.clone();
    /// assert_eq!(string.capacity(), 42);
    /// ```
    #[inline]
    #[must_use]
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
            // SAFETY: type invariant
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
        let vec = self.0.take_vec();
        // SAFETY: type invariant
        let owned = unsafe { String::from_utf8_unchecked(vec) };
        RefMut {
            result: self,
            owned,
        }
    }

    /// Shortens this string to the specified length.
    ///
    /// If `new_len` is greater than the string's current length, this has no
    /// effect.
    ///
    /// # Panics
    ///
    /// Panics if `new_len` is not a char boundary.
    ///
    /// # Examples
    /// ```
    /// # use hipstr::HipStr;
    /// let mut s = HipStr::from("abc");
    /// s.truncate(1);
    /// assert_eq!(s, "a");
    /// ```
    #[inline]
    pub fn truncate(&mut self, new_len: usize) {
        if new_len <= self.len() {
            assert!(self.is_char_boundary(new_len), "char boundary");
            self.0.truncate(new_len);
        }
    }

    /// Truncates this `HipStr`, removing all contents.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let mut s = HipStr::from("foo");
    ///
    /// s.clear();
    ///
    /// assert!(s.is_empty());
    /// assert_eq!(0, s.len());
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        self.0.clear();
    }

    /// Shrinks the capacity of the string as much as possible.
    ///
    /// The capacity will remain at least as large as the actual length of the
    /// string.
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
    /// # use hipstr::HipStr;
    /// let mut s = HipStr::with_capacity(100);
    /// s.push_str("abc");
    /// s.shrink_to_fit();
    /// assert_eq!(s.capacity(), HipStr::inline_capacity());
    /// ```
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.0.shrink_to_fit();
    }

    /// Shrinks the capacity of the string with a lower bound.
    ///
    /// The capacity will remain at least as large as the given lower bound and
    /// the actual length of the string.
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
    /// # use hipstr::HipStr;
    /// let mut s = HipStr::with_capacity(100);
    /// s.shrink_to(4);
    /// assert_eq!(s.capacity(), HipStr::inline_capacity());
    /// ```
    #[inline]
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.0.shrink_to(min_capacity);
    }

    /// Removes the last character from the string and returns it.
    ///
    /// Returns `None` if the string is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let mut s = HipStr::from("abc");
    /// assert_eq!(s.pop(), Some('c'));
    /// assert_eq!(s, "ab");
    /// ```
    #[inline]
    pub fn pop(&mut self) -> Option<char> {
        let (i, ch) = self.as_str().char_indices().next_back()?;
        self.truncate(i);
        Some(ch)
    }

    /// Appends a given string slice onto the end of this `HipStr`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let mut s = HipStr::from("cork");
    /// s.push_str("screw");
    /// assert_eq!(s, "corkscrew");
    /// ```
    #[inline]
    pub fn push_str(&mut self, addition: &str) {
        self.0.push_slice(addition.as_bytes());
    }

    /// Appends the given [`char`] to the end of this `HipStr`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let mut s = HipStr::from("abc");
    ///
    /// s.push('1');
    /// s.push('2');
    /// s.push('3');
    ///
    /// assert_eq!(s, "abc123");
    /// ```
    #[inline]
    pub fn push(&mut self, ch: char) {
        let mut data = [0; 4];
        let s = ch.encode_utf8(&mut data);
        self.0.push_slice(s.as_bytes());
    }

    /// Makes the string owned, copying the data if it is actually borrowed.
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let s: String = ('a'..'z').collect();
    /// let h = HipStr::borrowed(&s[..]);
    /// // drop(s); // err, s is borrowed
    /// let h = h.into_owned();
    /// drop(s); // ok
    /// assert_eq!(h, ('a'..'z').collect::<String>());
    /// ```
    #[must_use]
    pub fn into_owned(self) -> HipStr<'static, B> {
        HipStr(self.0.into_owned())
    }

    /// Returns a copy of this string where each character is mapped to its
    /// ASCII lower case equivalent.
    ///
    /// ASCII letters 'A' to 'Z' are mapped to 'a' to 'z',
    /// but non-ASCII letters are unchanged.
    ///
    /// To lowercase the value in-place, use [`make_ascii_lowercase`].
    ///
    /// To lowercase ASCII characters in addition to non-ASCII characters, use
    /// [`to_lowercase`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let s = HipStr::from("Grüße, Jürgen ❤");
    ///
    /// assert_eq!("grüße, jürgen ❤", s.to_ascii_lowercase());
    /// ```
    ///
    /// [`make_ascii_lowercase`]: Self::make_ascii_lowercase
    /// [`to_lowercase`]: Self::to_lowercase
    #[inline]
    #[must_use]
    pub fn to_ascii_lowercase(&self) -> Self {
        // SAFETY: changing ASCII letters only does not invalidate UTF-8.
        Self(self.0.to_ascii_lowercase())
    }

    /// Returns a copy of this string where each character is mapped to its
    /// ASCII upper case equivalent.
    ///
    /// ASCII letters 'a' to 'z' are mapped to 'A' to 'Z',
    /// but non-ASCII letters are unchanged.
    ///
    /// To uppercase the value in-place, use [`make_ascii_uppercase`].
    ///
    /// To uppercase ASCII characters in addition to non-ASCII characters, use
    /// [`to_uppercase`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let s = HipStr::from("Grüße, Jürgen ❤");
    ///
    /// assert_eq!("GRüßE, JüRGEN ❤", s.to_ascii_uppercase());
    /// ```
    ///
    /// [`make_ascii_uppercase`]: Self::make_ascii_uppercase
    /// [`to_uppercase`]: Self::to_uppercase
    #[inline]
    #[must_use]
    pub fn to_ascii_uppercase(&self) -> Self {
        // SAFETY: changing ASCII letters only does not invalidate UTF-8.
        Self(self.0.to_ascii_uppercase())
    }

    /// Converts this string to its ASCII upper case equivalent in-place.
    ///
    /// ASCII letters 'a' to 'z' are mapped to 'A' to 'Z',
    /// but non-ASCII letters are unchanged.
    ///
    /// To return a new uppercased value without modifying the existing one, use
    /// [`to_ascii_uppercase`].
    ///
    /// [`to_ascii_uppercase`]: Self::to_ascii_uppercase
    ///
    /// # Examples
    ///
    /// ```
    /// let mut s = String::from("Grüße, Jürgen ❤");
    ///
    /// s.make_ascii_uppercase();
    ///
    /// assert_eq!("GRüßE, JüRGEN ❤", s);
    /// ```
    #[inline]
    pub fn make_ascii_uppercase(&mut self) {
        // SAFETY: changing ASCII letters only does not invalidate UTF-8.
        self.0.make_ascii_uppercase();
    }

    /// Converts this string to its ASCII lower case equivalent in-place.
    ///
    /// ASCII letters 'A' to 'Z' are mapped to 'a' to 'z',
    /// but non-ASCII letters are unchanged.
    ///
    /// To return a new lowercased value without modifying the existing one, use
    /// [`to_ascii_lowercase`].
    ///
    /// [`to_ascii_lowercase`]: Self::to_ascii_lowercase
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let mut s = HipStr::from("GRÜßE, JÜRGEN ❤");
    ///
    /// s.make_ascii_lowercase();
    ///
    /// assert_eq!("grÜße, jÜrgen ❤", s);
    /// ```
    #[inline]
    pub fn make_ascii_lowercase(&mut self) {
        // SAFETY: changing ASCII letters only does not invalidate UTF-8.
        self.0.make_ascii_lowercase();
    }

    /// Returns the lowercase equivalent of this string, as a new `HipStr`.
    ///
    /// 'Lowercase' is defined according to the terms of the Unicode Derived Core Property
    /// `Lowercase`.
    ///
    /// Since some characters can expand into multiple characters when changing
    /// the case, this function returns a [`String`] instead of modifying the
    /// parameter in-place.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let s = HipStr::from("HELLO");
    ///
    /// assert_eq!("hello", s.to_lowercase());
    /// ```
    ///
    /// A tricky example, with sigma:
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let sigma = HipStr::from("Σ");
    ///
    /// assert_eq!("σ", sigma.to_lowercase());
    ///
    /// // but at the end of a word, it's ς, not σ:
    /// let odysseus = HipStr::from("ὈΔΥΣΣΕΎΣ");
    ///
    /// assert_eq!("ὀδυσσεύς", odysseus.to_lowercase());
    /// ```
    ///
    /// Languages without case are not changed:
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let new_year = HipStr::from("农历新年");
    ///
    /// assert_eq!(new_year, new_year.to_lowercase());
    /// ```
    #[inline]
    #[must_use]
    pub fn to_lowercase(&self) -> Self {
        Self::from(self.as_str().to_lowercase())
    }

    /// Returns the uppercase equivalent of this string, as a new `HipStr`.
    ///
    /// 'Uppercase' is defined according to the terms of the Unicode Derived Core Property
    /// `Uppercase`.
    ///
    /// Since some characters can expand into multiple characters when changing
    /// the case, this function returns a [`String`] instead of modifying the
    /// parameter in-place.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let s = HipStr::from("hello");
    ///
    /// assert_eq!("HELLO", s.to_uppercase());
    /// ```
    ///
    /// Scripts without case are not changed:
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let new_year = HipStr::from("农历新年");
    ///
    /// assert_eq!(new_year, new_year.to_uppercase());
    /// ```
    ///
    /// One character can become multiple:
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let s = HipStr::from("tschüß");
    ///
    /// assert_eq!("TSCHÜSS", s.to_uppercase());
    /// ```
    #[inline]
    #[must_use]
    pub fn to_uppercase(&self) -> Self {
        Self::from(self.as_str().to_uppercase())
    }

    /// Creates a new `HipStr` by repeating this one `n` times.
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
    /// # use hipstr::HipStr;
    /// assert_eq!(HipStr::from("abc").repeat(4), HipStr::from("abcabcabcabc"));
    /// ```
    ///
    /// A panic upon overflow:
    ///
    /// ```should_panic
    /// # use hipstr::HipStr;
    /// // this will panic at runtime
    /// let huge = HipStr::from("0123456789abcdef").repeat(usize::MAX);
    /// ```
    #[inline]
    #[must_use]
    pub fn repeat(&self, n: usize) -> Self {
        Self(self.0.repeat(n))
    }

    /// Returns a string with leading and trailing whitespace removed.
    ///
    /// 'Whitespace' is defined according to the terms of the Unicode Derived
    /// Core Property `White_Space`, which includes newlines.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let s = HipStr::from("\n Hello\tworld\t\n");
    ///
    /// assert_eq!("Hello\tworld", s.trim());
    /// ```
    #[inline]
    #[must_use]
    pub fn trim(&self) -> Self {
        let s = self.as_str().trim();
        unsafe { self.slice_ref_unchecked(s) }
    }

    /// Returns a string with leading whitespace removed.
    ///
    /// 'Whitespace' is defined according to the terms of the Unicode Derived
    /// Core Property `White_Space`, which includes newlines.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let s = HipStr::from("\n Hello\tworld\t\n");
    ///
    /// assert_eq!("Hello\tworld\t\n", s.trim_start());
    /// ```
    #[inline]
    #[must_use]
    pub fn trim_start(&self) -> Self {
        let s = self.as_str().trim_start();
        unsafe { self.slice_ref_unchecked(s) }
    }

    /// Returns a string with trailing whitespace removed.
    ///
    /// 'Whitespace' is defined according to the terms of the Unicode Derived
    /// Core Property `White_Space`, which includes newlines.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let s = HipStr::from("\n Hello\tworld\t\n");
    ///
    /// assert_eq!("\n Hello\tworld", s.trim_end());
    /// ```
    #[inline]
    #[must_use]
    pub fn trim_end(&self) -> Self {
        let s = self.as_str().trim_end();
        unsafe { self.slice_ref_unchecked(s) }
    }

    /// An iterator over substrings of this string, separated by
    /// characters matched by a pattern.
    ///
    /// Works like [`str::split`], but yields `HipStr`s rather than string slices.
    ///
    /// See [`str::split`], for examples and possible patterns.
    #[inline]
    pub fn split<P: Pattern>(&self, pattern: P) -> IterWrapper<'_, 'borrow, B, P::Split<'_>> {
        IterWrapper::new(self, pattern.split(self.as_str()))
    }

    /// An iterator over substrings of this string, separated by
    /// characters matched by a pattern. Differs from the iterator produced by
    /// `split` in that `split_inclusive` leaves the matched part as the
    /// terminator of the substring.
    ///
    /// Works like [`str::split_inclusive`], but yields `HipStr`s rather than string slices.
    ///
    /// See [`str::split_inclusive`], for examples and possible patterns.
    #[inline]
    pub fn split_inclusive<P: Pattern>(
        &self,
        pattern: P,
    ) -> IterWrapper<'_, 'borrow, B, P::SplitInclusive<'_>> {
        IterWrapper::new(self, pattern.split_inclusive(self.as_str()))
    }

    /// An iterator over substrings of this string, separated by
    /// characters matched by a pattern and yielded in reverse order.
    ///
    /// Works like [`str::rsplit`], but yields `HipStr`s rather than string slices.
    ///
    /// See [`str::rsplit`], for examples and possible patterns.
    #[inline]
    pub fn rsplit<P: ReversePattern>(
        &self,
        pattern: P,
    ) -> IterWrapper<'_, 'borrow, B, P::RSplit<'_>> {
        IterWrapper::new(self, pattern.rsplit(self.as_str()))
    }

    /// An iterator over substrings of this string, separated by
    /// characters matched by a pattern.
    ///
    /// Equivalent to [`split`](Self::split), except that the trailing substring
    /// is skipped if empty.
    ///
    /// This method can be used for string data that is _terminated_,
    /// rather than _separated_ by a pattern.
    ///
    /// Works like [`str::split_terminator`], but yields `HipStr`s rather than string slices.
    ///
    /// See [`str::split_terminator`], for examples and possible patterns.
    #[inline]
    pub fn split_terminator<P: Pattern>(
        &self,
        pattern: P,
    ) -> IterWrapper<'_, 'borrow, B, P::SplitTerminator<'_>> {
        IterWrapper::new(self, pattern.split_terminator(self.as_str()))
    }

    /// An iterator over substrings of this string, separated by
    /// characters matched by a pattern and yielded in reverse order.
    ///
    /// Equivalent to [`rsplit`](Self::rsplit), except that the trailing
    /// substring is skipped if empty.
    ///
    /// This method can be used for string data that is _terminated_,
    /// rather than _separated_ by a pattern.
    ///
    /// Works like [`str::rsplit_terminator`], but yields `HipStr`s rather than string slices.
    ///
    /// See [`str::rsplit_terminator`], for examples and possible patterns.
    #[inline]
    pub fn rsplit_terminator<P: ReversePattern>(
        &self,
        pattern: P,
    ) -> IterWrapper<'_, 'borrow, B, P::RSplitTerminator<'_>> {
        IterWrapper::new(self, pattern.rsplit_terminator(self.as_str()))
    }

    /// An iterator over substrings of this string, separated by a
    /// pattern, restricted to returning at most `n` items.
    ///
    /// If `n` substrings are returned, the last substring (the `n`th substring)
    /// will contain the remainder of the string.
    ///
    /// Works like [`str::splitn`], but yields `HipStr`s rather than string slices.
    ///
    /// See [`str::splitn`], for examples and possible patterns.
    #[inline]
    pub fn splitn<P: Pattern>(
        &self,
        n: usize,
        pattern: P,
    ) -> IterWrapper<'_, 'borrow, B, P::SplitN<'_>> {
        IterWrapper::new(self, pattern.splitn(n, self.as_str()))
    }

    /// An iterator over substrings of this string, separated by a
    /// pattern, starting from the end of the string, restricted to returning
    /// at most `n` items.
    ///
    /// If `n` substrings are returned, the last substring (the `n`th substring)
    /// will contain the remainder of the string.
    ///
    /// Works like [`str::rsplitn`], but yields `HipStr`s rather than string slices.
    ///
    /// See [`str::rsplitn`], for examples and possible patterns.
    #[inline]
    pub fn rsplitn<P: ReversePattern>(
        &self,
        n: usize,
        pattern: P,
    ) -> IterWrapper<'_, 'borrow, B, P::RSplitN<'_>> {
        IterWrapper::new(self, pattern.rsplitn(n, self.as_str()))
    }

    /// Splits the string on the first occurrence of the specified delimiter and
    /// returns prefix before delimiter and suffix after delimiter.
    ///
    /// Works like [`str::split_once`], but returns `HipStr`s rather than string slices.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// assert_eq!(HipStr::from("cfg").split_once('='), None);
    /// assert_eq!(HipStr::from("cfg=").split_once('='), Some(("cfg".into(), "".into())));
    /// assert_eq!(HipStr::from("cfg=foo").split_once('='), Some(("cfg".into(), "foo".into())));
    /// assert_eq!(HipStr::from("cfg=foo=bar").split_once('='), Some(("cfg".into(), "foo=bar".into())));
    /// ```
    #[inline]
    pub fn split_once<P: Pattern>(&self, pattern: P) -> Option<(Self, Self)> {
        pattern
            .split_once(self.as_str())
            .map(|(a, b)| unsafe { (self.slice_ref_unchecked(a), self.slice_ref_unchecked(b)) })
    }

    /// Splits the string on the last occurrence of the specified delimiter and
    /// returns prefix before delimiter and suffix after delimiter.
    ///
    /// Works like [`str::rsplit_once`], but returns `HipStr`s rather than string slices.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// assert_eq!(HipStr::from("cfg").split_once('='), None);
    /// assert_eq!(HipStr::from("cfg=foo").rsplit_once('='), Some(("cfg".into(), "foo".into())));
    /// assert_eq!(HipStr::from("cfg=foo=bar").rsplit_once('='), Some(("cfg=foo".into(), "bar".into())));
    /// ```
    #[inline]
    pub fn rsplit_once<P: ReversePattern>(&self, pattern: P) -> Option<(Self, Self)> {
        pattern
            .rsplit_once(self.as_str())
            .map(|(a, b)| unsafe { (self.slice_ref_unchecked(a), self.slice_ref_unchecked(b)) })
    }

    /// An iterator over the disjoint matches of a pattern within the given string
    /// slice.
    ///
    /// Works like [`str::matches`], but yields `HipStr` rather than string slices.
    ///
    /// See [`str::matches`], for examples and possible patterns.
    #[inline]
    pub fn matches<P: Pattern>(&self, pattern: P) -> IterWrapper<'_, 'borrow, B, P::Matches<'_>> {
        IterWrapper::new(self, pattern.matches(self.as_str()))
    }

    /// An iterator over the disjoint matches of a pattern within this string slice,
    /// yielded in reverse order.
    ///
    /// Works like [`str::rmatches`], but yields `HipStr` rather than string slices.
    ///
    /// See [`str::rmatches`], for examples and possible patterns.
    #[inline]
    pub fn rmatches<P: ReversePattern>(
        &self,
        pattern: P,
    ) -> IterWrapper<'_, 'borrow, B, P::RMatches<'_>> {
        IterWrapper::new(self, pattern.rmatches(self.as_str()))
    }

    /// An iterator over the disjoint matches of a pattern within this string
    /// slice as well as the index that the match starts at.
    ///
    /// Works like [`str::match_indices`], but yields `(usize, HipStr)` pairs
    /// rather than `(usize, &str)` pairs.
    ///
    /// See [`str::match_indices`] for examples.
    #[inline]
    pub fn match_indices<P: Pattern>(
        &self,
        pattern: P,
    ) -> IterWrapper<'_, 'borrow, B, P::MatchIndices<'_>> {
        IterWrapper::new(self, pattern.match_indices(self.as_str()))
    }

    /// An iterator over the disjoint matches of a pattern within `self`,
    /// yielded in reverse order along with the index of the match.
    ///
    /// Works like [`str::rmatch_indices`], but yields `(usize, HipStr)` pairs
    /// rather than `(usize, &str)` pairs.
    ///
    /// See [`str::rmatch_indices`] for examples.
    #[inline]
    pub fn rmatch_indices<P: ReversePattern>(
        &self,
        pattern: P,
    ) -> IterWrapper<'_, 'borrow, B, P::RMatchIndices<'_>> {
        IterWrapper::new(self, pattern.rmatch_indices(self.as_str()))
    }

    /// Returns a new `HipStr` with leading and trailing whitespace removed.
    ///
    /// Works like [`str::trim_matches`], but returns a `HipStr` rather than a string slice.
    ///
    /// See [`str::trim_matches`] for examples and possible patterns.
    #[inline]
    #[must_use]
    pub fn trim_matches(&self, p: impl DoubleEndedPattern) -> Self {
        let s = p.trim_matches(self.as_str());
        unsafe { self.slice_ref_unchecked(s) }
    }

    /// Returns a string slice with leading whitespace removed.
    ///
    /// Works like [`str::trim_start_matches`], but returns a `HipStr` rather than a string slice.
    ///
    /// See [`str::trim_start_matches`] for examples and possible patterns.
    #[inline]
    #[must_use]
    pub fn trim_start_matches(&self, p: impl Pattern) -> Self {
        let s = p.trim_start_matches(self.as_str());
        unsafe { self.slice_ref_unchecked(s) }
    }

    /// Returns a string slice with trailing whitespace removed.
    ///
    /// Works like [`str::trim_end_matches`], but returns a `HipStr` rather than a string slice.
    ///
    /// See [`str::trim_end_matches`] for examples and possible patterns.
    #[inline]
    #[must_use]
    pub fn trim_end_matches(&self, p: impl ReversePattern) -> Self {
        let s = p.trim_end_matches(self.as_str());
        unsafe { self.slice_ref_unchecked(s) }
    }

    /// Returns a string with the prefix removed.
    ///
    /// If the string starts with the pattern `prefix`, returns substring after the prefix, wrapped
    /// in `Some`.  Unlike `trim_start_matches`, this method removes the prefix exactly once.
    ///
    /// If the string does not start with `prefix`, returns `None`.
    ///
    /// Works like [`str::strip_prefix`], but returns a `HipStr` rather than a string slice.
    ///
    /// See [`str::strip_prefix`] for examples and possible patterns.
    #[inline]
    pub fn strip_prefix(&self, prefix: impl Pattern) -> Option<Self> {
        prefix
            .strip_prefix(self.as_str())
            .map(|s| unsafe { self.slice_ref_unchecked(s) })
    }

    /// Returns a string with the suffix removed.
    ///
    /// If the string ends with the pattern `suffix`, returns the substring before the suffix,
    /// wrapped in `Some`.  Unlike `trim_end_matches`, this method removes the suffix exactly once.
    ///
    /// If the string does not end with `suffix`, returns `None`.
    ///
    /// Works like [`str::strip_suffix`], but returns a `HipStr` rather than a
    /// string slice.
    ///
    /// See [`str::strip_suffix`] for examples and possible patterns.
    #[inline]
    pub fn strip_suffix(&self, suffix: impl ReversePattern) -> Option<Self> {
        suffix
            .strip_suffix(self.as_str())
            .map(|s| unsafe { self.slice_ref_unchecked(s) })
    }

    /// Splits a string by whitespace.
    ///
    /// Works like [`str::split_whitespace`], but yields `HipStr`s rather than
    /// string slices.
    ///
    /// See [`str::split_whitespace`] for examples.
    #[inline]
    pub fn split_whitespace(&self) -> IterWrapper<'_, 'borrow, B, SplitWhitespace<'_>> {
        IterWrapper::new(self, self.as_str().split_whitespace())
    }

    /// Splits a string by ASCII whitespace.
    ///
    /// Works like [`str::split_ascii_whitespace`], but yields `HipStr`s rather than
    /// string slices.
    ///
    /// See [`str::split_ascii_whitespace`] for examples.
    #[inline]
    pub fn split_ascii_whitespace(&self) -> IterWrapper<'_, 'borrow, B, SplitAsciiWhitespace<'_>> {
        IterWrapper::new(self, self.as_str().split_ascii_whitespace())
    }

    /// An iterator over the lines of a string.
    ///
    /// Works like [`str::split_ascii_whitespace`], but yields `HipStr`s rather than
    /// string slices.
    ///
    /// See [`str::split_ascii_whitespace`] for examples.
    #[inline]
    pub fn lines(&self) -> IterWrapper<'_, 'borrow, B, Lines> {
        IterWrapper::new(self, self.as_str().lines())
    }

    /// Concatenates some byte slices into a single `HipByt`.
    ///
    /// The related constructor [`HipStr::concat`] is more general but may be
    /// less efficient due to the absence of specialization in Rust.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hipstr::HipByt;
    /// let c = HipByt::concat_slices(&[b"hello", b" world", b"!"]);
    /// assert_eq!(c, b"hello world!");
    /// ```
    #[inline]
    #[must_use]
    pub fn concat_slices(slices: &[&str]) -> Self {
        #[expect(clippy::transmute_ptr_to_ptr)]
        let slices: &[&[u8]] = unsafe { transmute(slices) };

        Self(HipByt::concat_slices(slices))
    }

    /// Concatenates string slices (or things than can be seen as string slices)
    /// together into a new `HipStr`.
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
    /// # use hipstr::HipStr;
    /// let c  = HipStr::concat(&["hello", " world", "!"]);
    /// assert_eq!(c, "hello world!");
    ///
    /// let c2 = HipStr::concat(["hello".to_string(), " world".to_string(), "!".to_string()]);
    /// assert_eq!(c2, "hello world!");
    ///
    /// let c3 = HipStr::concat(vec!["hello", " world", "!"].iter());
    /// assert_eq!(c3, "hello world!");
    /// ```
    pub fn concat<E, I>(slices: I) -> Self
    where
        E: AsRef<str>,
        I: IntoIterator<Item = E>,
        I::IntoIter: Clone,
    {
        Self(HipByt::concat(slices.into_iter().map(AsBytes)))
    }

    /// Joins some string slices with the given separator string slice into a
    /// new `HipByt`, that is, concatenates the strings inserting the
    /// separator between each pair of adjacent strings.
    ///
    /// The related constructor [`HipStr::join`] is more general but may be less
    /// efficient due to the absence of specialization in Rust.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hipstr::HipStr;
    /// let s = HipStr::join_slices(&["hello", "world", "rust"], ", ");
    /// assert_eq!(s, "hello, world, rust");
    /// ```
    #[inline]
    #[must_use]
    pub fn join_slices(slices: &[&str], sep: &str) -> Self {
        #[expect(clippy::transmute_ptr_to_ptr)]
        let slices: &[&[u8]] = unsafe { transmute(slices) };

        Self(HipByt::join_slices(slices, sep.as_bytes()))
    }

    /// Joins strings together with the given separator string into a new `HipStr`,
    /// that is, concatenates the strings inserting the separator between each pair of
    /// adjacent strings.
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
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let slices = &["hello", "world", "rust"];
    /// let sep = ", ";
    /// let joined = HipStr::join(slices, sep);
    /// assert_eq!(joined, "hello, world, rust");
    ///
    /// let joined = HipStr::join(["hello".to_string(), "world".to_string(), "rust".to_string()].iter(), sep.to_string());
    /// assert_eq!(joined, "hello, world, rust");
    ///
    /// let joined = HipStr::join(slices.to_vec().iter(), sep);
    /// assert_eq!(joined, "hello, world, rust");
    /// ```
    pub fn join<E, I>(slices: I, sep: impl AsRef<str>) -> Self
    where
        E: AsRef<str>,
        I: IntoIterator<Item = E>,
        I::IntoIter: Clone,
    {
        let iter = slices.into_iter().map(AsBytes);
        Self(HipByt::join(iter, sep.as_ref().as_bytes()))
    }
}

impl<B> HipStr<'static, B>
where
    B: Backend,
{
    /// Creates a new `HipStr` from a static string slice without copying the slice.
    ///
    /// Handy shortcut to make a `HipStr<'static, _>` out of a `&'static str`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let s = HipStr::from_static("hello");
    /// assert_eq!(s.len(), 5);
    /// ```
    #[inline]
    #[must_use]
    pub const fn from_static(value: &'static str) -> Self {
        Self::borrowed(value)
    }
}

// Manual implementation needed to remove trait bound on B::RawPointer.
impl<B> Clone for HipStr<'_, B>
where
    B: Backend,
{
    #[inline]
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

// Manual implementation needed to remove trait bound on B::RawPointer.
impl<B> Default for HipStr<'_, B>
where
    B: Backend,
{
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<B> Deref for HipStr<'_, B>
where
    B: Backend,
{
    type Target = str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl<B> Borrow<str> for HipStr<'_, B>
where
    B: Backend,
{
    #[inline]
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl<B> Hash for HipStr<'_, B>
where
    B: Backend,
{
    #[inline]
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.as_str().hash(state);
    }
}

// Formatting

impl<B> fmt::Debug for HipStr<'_, B>
where
    B: Backend,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.as_str(), f)
    }
}

impl<B> fmt::Display for HipStr<'_, B>
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
pub struct SliceError<'a, 'borrow, B>
where
    B: Backend,
{
    kind: SliceErrorKind,
    start: usize,
    end: usize,
    string: &'a HipStr<'borrow, B>,
}

impl<B> Eq for SliceError<'_, '_, B> where B: Backend {}

impl<B> PartialEq for SliceError<'_, '_, B>
where
    B: Backend,
{
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
            && self.start == other.start
            && self.end == other.end
            && self.string == other.string
    }
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

impl<B> fmt::Debug for SliceError<'_, '_, B>
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

impl<B> fmt::Display for SliceError<'_, '_, B>
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

impl<B> Error for SliceError<'_, '_, B> where B: Backend {}

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
pub struct FromUtf8Error<'borrow, B>
where
    B: Backend,
{
    pub(super) bytes: HipByt<'borrow, B>,
    pub(super) error: Utf8Error,
}

impl<B> Eq for FromUtf8Error<'_, B> where B: Backend {}

impl<B> PartialEq for FromUtf8Error<'_, B>
where
    B: Backend,
{
    fn eq(&self, other: &Self) -> bool {
        self.bytes == other.bytes && self.error == other.error
    }
}

impl<B> Clone for FromUtf8Error<'_, B>
where
    B: Backend,
{
    fn clone(&self) -> Self {
        Self {
            bytes: self.bytes.clone(),
            error: self.error,
        }
    }
}

impl<B> fmt::Debug for FromUtf8Error<'_, B>
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
    // #[allow(clippy::missing_const_for_fn)] // cannot const it for now, clippy bug
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

impl<B> fmt::Display for FromUtf8Error<'_, B>
where
    B: Backend,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.error, f)
    }
}

impl<B> Error for FromUtf8Error<'_, B> where B: Backend {}

/// A wrapper type for a mutably borrowed [`String`] out of a [`HipStr`].
pub struct RefMut<'a, 'borrow, B>
where
    B: Backend,
{
    result: &'a mut HipStr<'borrow, B>,
    owned: String,
}

impl<B> Drop for RefMut<'_, '_, B>
where
    B: Backend,
{
    fn drop(&mut self) {
        let owned = core::mem::take(&mut self.owned);
        *self.result = HipStr::from(owned);
    }
}

impl<B> Deref for RefMut<'_, '_, B>
where
    B: Backend,
{
    type Target = String;
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

#[derive(Clone, Copy)]
struct AsBytes<T>(T);

impl<T: AsRef<str>> AsRef<[u8]> for AsBytes<T> {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref().as_bytes()
    }
}
