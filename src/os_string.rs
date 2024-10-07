//! OS string.
//!
//! This module provides the [`HipOsStr`] as well as the associated helper type [`RefMut`].

use core::hash::Hash;
use core::ops::{Deref, DerefMut};
use std::ffi::{OsStr, OsString};

use crate::alloc::borrow::Cow;
use crate::alloc::fmt;
use crate::bytes::HipByt;
use crate::string::HipStr;
use crate::Backend;

mod cmp;
mod convert;

#[cfg(feature = "serde")]
mod serde;

#[cfg(test)]
mod tests;

/// Smart OS string, i.e. shared and cheaply clonable OS string.
///
/// Internally used the same representations as [`HipByt`].
///
/// # Examples
///
/// You can create a `HipStr` from anything that implements [`OsStr`], typically:
///
/// - string slices ([`&str`], [`&OsStr`], [`&Path`]),
/// - owned strings ([`String`], [`OsString`], [`PathBuf`], [`Box<str>`][Box]),
/// - clone-on-write smart pointers ([`Cow`]) to string slice,
/// - “Hip”-strings ([`HipStr`], [`HipOsStr`], [`HipPath`]),
///
/// with [`From`]:
///
/// ```
/// # use hipstr::HipOsStr;
/// let hello = HipOsStr::from("Hello");
/// ```
///
/// When possible, `HipOsStr::from` takes ownership of the underlying string
/// buffer:
///
/// ```
/// # use hipstr::HipOsStr;
/// # use std::ffi::OsStr;
/// let world_os = OsStr::new("World").to_os_string();
/// let world = HipOsStr::from(world_os); // here there is only one heap-allocation
/// ```
///
/// For borrowing string slice, you can also use the no-copy [`HipOsStr::borrowed`]
/// (like [`Cow::Borrowed`](std::borrow::Cow)):
///
/// ```
/// # use hipstr::HipOsStr;
/// let hello = HipOsStr::borrowed("Hello, world!");
/// ```
///
/// # Representations
///
/// Like `HipByt`, `HipOsStr` has three possible internal representations:
///
/// * borrow
/// * inline string
/// * shared heap allocated string
///
/// [`&OsStr`]: std::ffi::OsStr
/// [`&Path`]: std::path::Path
/// [`PathBuf`]: std::path::PathBuf
/// [`HipStr`]: crate::string::HipStr
/// [`HipPath`]: crate::path::HipPath
#[repr(transparent)]
pub struct HipOsStr<'borrow, B>(pub(crate) HipByt<'borrow, B>)
where
    B: Backend;

impl<'borrow, B> HipOsStr<'borrow, B>
where
    B: Backend,
{
    /// Creates an empty `HipOsStr`.
    ///
    /// Function provided for [`OsString::new`] replacement.
    ///
    /// # ⚠️ Stability warning!
    ///
    /// The used representation of the empty string is unspecified.
    /// It may be *borrowed* or *inlined* but will never be allocated.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipOsStr;
    /// let s = HipOsStr::new();
    /// ```
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self(HipByt::new())
    }

    /// Creates a new `HipOsStr` with the given capacity.
    ///
    /// The returned `HipOsStr` will be able to hold at least `capacity` bytes
    /// without reallocating or changing representation.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipOsStr;
    /// let mut s = HipOsStr::with_capacity(42);
    /// for _ in 0..42 {
    ///     s.push("*");
    /// }
    /// assert_eq!(s, "*".repeat(42).as_str());
    /// ```
    #[inline]
    #[must_use]
    pub fn with_capacity(cap: usize) -> Self {
        Self(HipByt::with_capacity(cap))
    }

    /// Creates a new `HipOsStr` from a static os string slice without copying the slice.
    ///
    /// Requires only `impl AsRef<OsStr>`: it accepts `&str`, `&OsStr`, and `&Path` for instance.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipOsStr;
    /// let s = HipOsStr::borrowed("hello");
    /// assert_eq!(s.len(), 5);
    /// ```
    #[must_use]
    pub fn borrowed<S: AsRef<OsStr> + ?Sized>(value: &'borrow S) -> Self {
        Self(HipByt::borrowed(value.as_ref().as_encoded_bytes()))
    }

    /// Returns `true` if this `HipOsStr` uses the inline representation, `false` otherwise.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipOsStr;
    /// let s = HipOsStr::borrowed("hello");
    /// assert!(!s.is_inline());
    ///
    /// let s = HipOsStr::from("hello");
    /// assert!(s.is_inline());
    ///
    /// let s = HipOsStr::from("hello".repeat(10));
    /// assert!(!s.is_inline());
    /// ```
    #[inline]
    #[must_use]
    pub const fn is_inline(&self) -> bool {
        self.0.is_inline()
    }

    /// Returns `true` if this `HipOsStr` is a static string borrow, `false` otherwise.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipOsStr;
    /// let s = HipOsStr::borrowed("hello");
    /// assert!(s.is_borrowed());
    ///
    /// let s = HipOsStr::from("hello");
    /// assert!(!s.is_borrowed());
    ///
    /// let s = HipOsStr::from("hello".repeat(10));
    /// assert!(!s.is_borrowed());
    /// ```
    #[inline]
    #[must_use]
    pub const fn is_borrowed(&self) -> bool {
        self.0.is_borrowed()
    }

    /// Returns `true` if this `HipOsStr` is a shared heap-allocated string, `false` otherwise.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipOsStr;
    /// let s = HipOsStr::borrowed("hello");
    /// assert!(!s.is_allocated());
    ///
    /// let s = HipOsStr::from("hello");
    /// assert!(!s.is_allocated());
    ///
    /// let s = HipOsStr::from("hello".repeat(10));
    /// assert!(s.is_allocated());
    /// ```
    #[inline]
    #[must_use]
    pub const fn is_allocated(&self) -> bool {
        self.0.is_allocated()
    }

    /// Converts `self` into a static string slice if this `HipOsStr` is backed by a static borrow.
    ///
    /// # Errors
    ///
    /// Returns `Err(self)` if this `HipOsStr` is not a static borrow.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipOsStr;
    /// # use std::ffi::OsStr;
    /// let borrowed: &'static OsStr= "hipstr".as_ref();
    /// let s = HipOsStr::borrowed(borrowed);
    /// let c = s.into_borrowed();
    /// assert_eq!(c, Ok(borrowed));
    /// assert!(std::ptr::eq(borrowed, c.unwrap()));
    /// ```
    #[inline]
    pub fn into_borrowed(self) -> Result<&'borrow OsStr, Self> {
        self.0
            .into_borrowed()
            .map(|slice|
                // SAFETY: type invariant
                unsafe { OsStr::from_encoded_bytes_unchecked(slice) })
            .map_err(Self)
    }

    /// Returns the length of this `HipOsStr`, in bytes, not [`char`]s or
    /// graphemes. In other words, it might not be what a human considers the
    /// length of the string.
    ///
    /// As noted in [`OsStr::len`], the length is not the number of bytes used
    /// by the OS representation of this string, but by the Rust interoperabilty
    /// format which may differ significantly from both the OS representation
    /// and the native Rust representation.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipOsStr;
    /// let a = HipOsStr::from("(c)");
    /// assert_eq!(a.len(), 3);
    ///
    /// let b = HipOsStr::from("®");
    /// assert_eq!(b.len(), 2);
    /// assert_eq!(b.to_str().unwrap().chars().count(), 1);
    /// ```
    #[inline]
    #[must_use]
    pub const fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns `true` if this `HipOsStr` has a length of zero, and `false` otherwise.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipOsStr;
    /// let a = HipOsStr::new();
    /// assert!(a.is_empty());
    ///
    /// let b = HipOsStr::borrowed("ab");
    /// assert!(!b.is_empty());
    /// ```
    #[inline]
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Converts a `HipOsStr` into a `HipByt`.
    ///
    /// It consumes the `HipOsStr` without copying the content
    /// (if [shared][HipByt::is_allocated] or [static][HipByt::is_borrowed]).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipOsStr;
    /// let s = HipOsStr::from("hello");
    /// let b = s.into_bytes();
    ///
    /// assert_eq!(&[104, 101, 108, 108, 111][..], &b[..]);
    /// ```
    #[allow(clippy::missing_const_for_fn)] // cannot const it for now, clippy bug
    #[must_use]
    pub fn into_bytes(self) -> HipByt<'borrow, B> {
        self.0
    }

    /// Extracts an [`OsStr`] slice of the entire `HipOsStr`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipOsStr;
    /// # use std::ffi::OsStr;
    /// let s = HipOsStr::from("foobar");
    ///
    /// assert_eq!(OsStr::new("foobar"), s.as_os_str());
    /// ```
    #[inline]
    #[must_use]
    pub fn as_os_str(&self) -> &OsStr {
        // SAFETY: type invariant
        unsafe { OsStr::from_encoded_bytes_unchecked(self.0.as_slice()) }
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
    /// # use hipstr::HipOsStr;
    /// let mut s: String = String::with_capacity(42);
    /// s.extend('a'..='z');
    /// let string = HipOsStr::from(s);
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

    /// Converts `self` into an [`OsString`] without clone or allocation if possible.
    ///
    /// # Errors
    ///
    /// Returns `Err(self)` if it is impossible to take ownership of the string
    /// backing this `HipOsStr`.
    #[inline]
    pub fn into_os_string(self) -> Result<OsString, Self> {
        self.0
            .into_vec()
            // SAFETY: type invariant
            .map(|v| unsafe { OsString::from_encoded_bytes_unchecked(v) })
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
    /// # use hipstr::HipOsStr;
    /// let mut s = HipOsStr::borrowed("abc");
    /// {
    ///     let mut r = s.mutate();
    ///     r.push("def");
    ///     assert_eq!(r.as_os_str(), "abcdef");
    /// }
    /// assert_eq!(s, "abcdef");
    /// ```
    #[inline]
    #[must_use]
    pub fn mutate(&mut self) -> RefMut<'_, 'borrow, B> {
        // SAFETY: type invariant
        let owned = self.take_os_string();
        RefMut {
            result: self,
            owned,
        }
    }

    /// Appends a given string slice onto the end of this `HipOsStr`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipOsStr;
    /// let mut s = HipOsStr::from("cork");
    /// s.push("screw");
    /// assert_eq!(s, "corkscrew");
    /// ```
    #[inline]
    pub fn push(&mut self, addition: impl AsRef<OsStr>) {
        self.0.push_slice(addition.as_ref().as_encoded_bytes());
    }

    /// Makes the string owned, copying the data if it is actually borrowed.
    ///
    /// ```
    /// # use hipstr::HipOsStr;
    /// let s: String = ('a'..'z').collect();
    /// let s2 = s.clone();
    /// let h = HipOsStr::borrowed(&s[..]);
    /// // drop(s); // err, s is borrowed
    /// let h = h.into_owned();
    /// drop(s); // ok
    /// assert_eq!(h, s2.as_str());
    /// ```
    #[must_use]
    pub fn into_owned(self) -> HipOsStr<'static, B> {
        HipOsStr(self.0.into_owned())
    }

    #[inline]
    #[cfg(test)]
    pub(crate) fn as_ptr(&self) -> *const u8 {
        self.0.as_ptr()
    }

    /// Converts the `HipOsStr` into a [`HipStr`] if it contains valid Unicode data.
    ///
    /// # Errors
    ///
    /// If it contains invalid Unicode data, ownership of the original `HipOsStr` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::{HipStr,HipOsStr};
    ///
    /// let os = HipOsStr::from("foo");
    /// let s = os.into_str();
    /// assert_eq!(s, Ok(HipStr::from("foo")));
    /// ```
    #[inline]
    pub fn into_str(self) -> Result<HipStr<'borrow, B>, Self> {
        HipStr::from_utf8(self.0).map_err(|e| Self(e.bytes))
    }

    /// Converts a `HipOsStr` into a [`HipStr`] if the content is valid Unicode.
    ///
    /// This conversion may entail doing a check for UTF-8 validity.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::{HipOsStr, HipStr};
    /// let os_str = HipOsStr::from("foo");
    /// assert_eq!(os_str.to_str(), Some(HipStr::from("foo")));
    /// ```
    #[must_use]
    pub fn to_str(&self) -> Option<HipStr<'borrow, B>> {
        let _ = self.as_os_str().to_str()?;
        // SAFETY: the previous line checked the encoding
        Some(unsafe { HipStr::from_utf8_unchecked(self.0.clone()) })
    }

    /// Converts a `HipOsStr` to a [`HipStr`].
    ///
    /// Any non-Unicode sequences are replaced with
    /// [`U+FFFD REPLACEMENT CHARACTER`][U+FFFD].
    ///
    /// [U+FFFD]: std::char::REPLACEMENT_CHARACTER
    ///
    /// # Examples
    ///
    /// Calling `to_str_lossy` on an `HipStr` with invalid unicode:
    ///
    /// ```
    /// # use hipstr::HipOsStr;
    /// // Note, due to differences in how Unix and Windows represent strings,
    /// // we are forced to complicate this example, setting up example `HipOsStr`s
    /// // with different source data and via different platform extensions.
    /// // Understand that in reality you could end up with such example invalid
    /// // sequences simply through collecting user command line arguments, for
    /// // example.
    ///
    /// #[cfg(unix)] {
    ///     use std::ffi::OsStr;
    ///     use std::os::unix::ffi::OsStrExt;
    ///
    ///     // Here, the values 0x66 and 0x6f correspond to 'f' and 'o'
    ///     // respectively. The value 0x80 is a lone continuation byte, invalid
    ///     // in a UTF-8 sequence.
    ///     let source = [0x66, 0x6f, 0x80, 0x6f];
    ///     let os_str = OsStr::from_bytes(&source[..]);
    ///     let hip_os_str = HipOsStr::from(os_str);
    ///
    ///     assert_eq!(hip_os_str.to_str_lossy(), "fo�o");
    /// }
    /// #[cfg(windows)] {
    ///     use std::ffi::OsString;
    ///     use std::os::windows::prelude::*;
    ///
    ///     // Here the values 0x0066 and 0x006f correspond to 'f' and 'o'
    ///     // respectively. The value 0xD800 is a lone surrogate half, invalid
    ///     // in a UTF-16 sequence.
    ///     let source = [0x0066, 0x006f, 0xD800, 0x006f];
    ///     let os_string = OsString::from_wide(&source[..]);
    ///     let hip_os_str = HipOsStr::from(os_string);
    ///
    ///     assert_eq!(hip_os_str.to_str_lossy(), "fo�o");
    /// }
    /// ```
    #[inline]
    #[must_use]
    pub fn to_str_lossy(&self) -> HipStr<'borrow, B> {
        match self.as_os_str().to_string_lossy() {
            Cow::Borrowed(_) => unsafe { HipStr::from_utf8_unchecked(self.0.clone()) },
            Cow::Owned(s) => HipStr::from(s),
        }
    }

    pub(crate) fn take_os_string(&mut self) -> OsString {
        // SAFETY: type invariant
        unsafe { OsString::from_encoded_bytes_unchecked(self.0.take_vec()) }
    }

    /// Extracts a slice as its own `HipOsStr` based on the given subslice `&OsStr`.
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
    /// # use hipstr::HipOsStr;
    /// # use std::path::Path;
    /// # use std::ffi::OsStr;
    /// let a = HipOsStr::from("abc/def");
    /// let p: &Path = a.as_ref();
    /// let n: &OsStr = p.file_name().unwrap();
    /// assert_eq!(a.slice_ref(n), HipOsStr::from("def"));
    /// ```
    #[inline]
    #[must_use]
    pub fn slice_ref(&self, slice: &OsStr) -> Self {
        Self(self.0.slice_ref(slice.as_encoded_bytes()))
    }

    /// Returns a slice as it own `HipStr` based on the given subslice `&OsStr`.
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
    /// # use hipstr::HipOsStr;
    /// # use std::path::Path;
    /// # use std::ffi::OsStr;
    /// let a = HipOsStr::from("abc");
    /// let sl: &OsStr = unsafe { OsStr::from_encoded_bytes_unchecked(&a.as_encoded_bytes()[0..2]) };
    /// assert_eq!(a.try_slice_ref(sl), Some(HipOsStr::from("ab")));
    /// assert!(a.try_slice_ref("z".as_ref()).is_none());
    /// ```
    #[inline]
    pub fn try_slice_ref(&self, slice: &OsStr) -> Option<Self> {
        self.0.try_slice_ref(slice.as_encoded_bytes()).map(Self)
    }

    /// Extracts a slice as its own `HipOsStr` based on the given subslice `&OsStr`.
    ///
    /// # Safety
    ///
    /// The slice MUST be a part of this `HipOsStr`.
    #[inline]
    #[must_use]
    pub fn slice_ref_unchecked(&self, slice: &OsStr) -> Self {
        // SAFETY
        unsafe { Self(self.0.slice_ref_unchecked(slice.as_encoded_bytes())) }
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
    /// # use hipstr::HipOsStr;
    /// let mut s = HipOsStr::with_capacity(100);
    /// s.push("abc");
    /// s.shrink_to_fit();
    /// assert_eq!(s.capacity(), HipOsStr::inline_capacity());
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
    /// # use hipstr::HipOsStr;
    /// let mut s = HipOsStr::with_capacity(100);
    /// s.shrink_to(4);
    /// assert_eq!(s.capacity(), HipOsStr::inline_capacity());
    /// ```
    #[inline]
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.0.shrink_to(min_capacity);
    }
}

impl<B> HipOsStr<'static, B>
where
    B: Backend,
{
    /// Creates a new `HipOsStr` from a static string slice without copying the slice.
    ///
    /// Handy shortcut to make a `HipOsStr<'static, _>` out of a `&'static str`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipOsStr;
    /// let s = HipOsStr::from_static("hello");
    /// assert_eq!(s.len(), 5);
    /// ```
    #[inline]
    #[must_use]
    pub const fn from_static(value: &'static str) -> Self {
        // SAFETY: value is a valid UTF-8
        HipOsStr(HipByt::borrowed(value.as_bytes()))
    }
}

// Manual implementation needed to remove trait bound on B::RawPointer.
impl<B> Clone for HipOsStr<'_, B>
where
    B: Backend,
{
    #[inline]
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

// Manual implementation needed to remove trait bound on B::RawPointer.
impl<B> Default for HipOsStr<'_, B>
where
    B: Backend,
{
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<B> Deref for HipOsStr<'_, B>
where
    B: Backend,
{
    type Target = OsStr;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_os_str()
    }
}

impl<B> Hash for HipOsStr<'_, B>
where
    B: Backend,
{
    #[inline]
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.as_os_str().hash(state);
    }
}

// Formatting

impl<B> fmt::Debug for HipOsStr<'_, B>
where
    B: Backend,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.as_os_str(), f)
    }
}

/// A wrapper type for a mutably borrowed [`String`] out of a [`HipOsStr`].
pub struct RefMut<'a, 'borrow, B>
where
    B: Backend,
{
    result: &'a mut HipOsStr<'borrow, B>,
    owned: OsString,
}

impl<B> fmt::Debug for RefMut<'_, '_, B>
where
    B: Backend,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.owned.fmt(f)
    }
}

impl<B> Drop for RefMut<'_, '_, B>
where
    B: Backend,
{
    fn drop(&mut self) {
        let owned = core::mem::take(&mut self.owned);
        *self.result = HipOsStr::from(owned);
    }
}

impl<B> Deref for RefMut<'_, '_, B>
where
    B: Backend,
{
    type Target = OsString;
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
