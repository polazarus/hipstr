//! Cross-platform path.
//!
//! This module provides the [`HipPath`] type as well as the associated helper type [`RefMut`].

use core::hash::Hash;
use core::ops::{Deref, DerefMut};
use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};

use crate::alloc::fmt;
use crate::bytes::HipByt;
use crate::os_string::HipOsStr;
use crate::string::HipStr;
use crate::Backend;

mod cmp;
mod convert;

#[cfg(feature = "serde")]
pub mod serde;

#[cfg(test)]
mod tests;

/// Smart path, i.e. shared and cheaply clonable path.
///
/// Internally used the same representations as [`HipByt`].
///
/// # Examples
///
/// You can create a `HipPath` from anything that implements [`OsStr`], typically:
///
/// - string slices ([`&str`], [`&OsStr`], [`&Path`]),
/// - owned strings ([`String`], [`OsString`], [`PathBuf`], [`Box<str>`][Box]),
/// - clone-on-write smart pointers ([`Cow`][std::borrow::Cow]) to string slice,
/// - “Hip”-strings ([`HipStr`], [`HipOsStr`], [`HipPath`]),
///
/// with [`From`]:
///
/// ```
/// # use hipstr::HipPath;
/// let hello = HipPath::from("Hello");
/// ```
///
/// When possible, `HipPath::from` takes ownership of the underlying string
/// buffer:
///
/// ```
/// # use hipstr::HipPath;
/// # use std::path::PathBuf;
/// let world_os = PathBuf::from("World");
/// let world = HipPath::from(world_os); // here there is only one heap-allocation
/// ```
///
/// For borrowing string slice, you can also use the no-copy [`HipPath::borrowed`]
/// (like [`Cow::Borrowed`](std::borrow::Cow)):
///
/// ```
/// # use hipstr::HipPath;
/// let hello = HipPath::borrowed("Hello, world!");
/// ```
///
/// # Representations
///
/// Like `HipByt`, `HipPath` has three possible internal representations:
///
/// * borrow
/// * inline string
/// * shared heap allocated string
///
/// [`&OsStr`]: std::ffi::OsStr
/// [`&Path`]: std::path::Path
/// [`HipStr`]: crate::string::HipStr
/// [`HipOsStr``]: crate::string::HipOsStr
#[repr(transparent)]
#[allow(clippy::module_name_repetitions)]
pub struct HipPath<'borrow, B>(HipOsStr<'borrow, B>)
where
    B: Backend;

impl<'borrow, B> HipPath<'borrow, B>
where
    B: Backend,
{
    /// Creates an empty `HipPath`.
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
    /// # use hipstr::HipPath;
    /// let s = HipPath::new();
    /// ```
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self(HipOsStr::new())
    }

    /// Creates a new `HipPath` from a static os string slice without copying the slice.
    ///
    /// Requires only `impl AsRef<Path>`: it accepts `&str`, `&OsStr`, and `&Path` for instance.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipPath;
    /// # use std::path::Path;
    /// let s = HipPath::borrowed("hello");
    /// assert_eq!(s, Path::new("hello"));
    /// ```
    #[must_use]
    #[inline]
    pub fn borrowed<P: AsRef<Path> + ?Sized>(value: &'borrow P) -> Self {
        Self(HipOsStr::borrowed(value.as_ref().as_os_str()))
    }

    /// Returns `true` if this `HipPath` uses the inline representation, `false` otherwise.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipPath;
    /// let s = HipPath::borrowed("hello");
    /// assert!(!s.is_inline());
    ///
    /// let s = HipPath::from("hello");
    /// assert!(s.is_inline());
    ///
    /// let s = HipPath::from("hello".repeat(10));
    /// assert!(!s.is_inline());
    /// ```
    #[inline]
    #[must_use]
    pub const fn is_inline(&self) -> bool {
        self.0.is_inline()
    }

    /// Returns `true` if this `HipPath` is a static string borrow, `false` otherwise.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipPath;
    /// let s = HipPath::borrowed("hello");
    /// assert!(s.is_borrowed());
    ///
    /// let s = HipPath::from("hello");
    /// assert!(!s.is_borrowed());
    ///
    /// let s = HipPath::from("hello".repeat(10));
    /// assert!(!s.is_borrowed());
    /// ```
    #[inline]
    #[must_use]
    pub const fn is_borrowed(&self) -> bool {
        self.0.is_borrowed()
    }

    /// Returns `true` if this `HipPath` is a shared heap-allocated string, `false` otherwise.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipPath;
    /// let s = HipPath::borrowed("hello");
    /// assert!(!s.is_allocated());
    ///
    /// let s = HipPath::from("hello");
    /// assert!(!s.is_allocated());
    ///
    /// let s = HipPath::from("hello".repeat(10));
    /// assert!(s.is_allocated());
    /// ```
    #[inline]
    #[must_use]
    pub const fn is_allocated(&self) -> bool {
        self.0.is_allocated()
    }

    /// Converts `self` into a static string slice if this `HipPath` is backed by a static borrow.
    ///
    /// # Errors
    ///
    /// Returns `Err(self)` if this `HipPath` is not a static borrow.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipPath;
    /// # use std::path::Path;
    /// let borrowed: &'static Path = "hipstr".as_ref();
    /// let s = HipPath::borrowed(borrowed);
    /// let c = s.into_borrowed();
    /// assert_eq!(c, Ok(borrowed));
    /// assert!(std::ptr::eq(borrowed, c.unwrap()));
    /// ```
    #[inline]
    pub fn into_borrowed(self) -> Result<&'borrow Path, Self> {
        self.0.into_borrowed().map(Path::new).map_err(Self)
    }

    /// Converts a `HipPath` into a `HipOsStr`.
    ///
    /// It consumes the `HipPath` without copying the content
    /// (if [shared][HipPath::is_allocated] or [borrowed][HipPath::is_borrowed]).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipPath;
    /// let s = HipPath::from("hello");
    /// let b = s.into_os_str();
    ///
    /// assert_eq!(b, "hello");
    /// ```
    #[allow(clippy::missing_const_for_fn)] // cannot const it for now, clippy bug
    #[must_use]
    pub fn into_os_str(self) -> HipOsStr<'borrow, B> {
        self.0
    }

    /// Yields a [`Path`] slice of the entire `HipPath`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipPath;
    /// # use std::path::Path;
    /// let s = HipPath::from("foobar");
    ///
    /// assert_eq!(Path::new("foobar"), s.as_path());
    /// ```
    #[inline]
    #[must_use]
    pub fn as_path(&self) -> &Path {
        Path::new(self.0.as_os_str())
    }

    /// Yields an [`OsStr`] slice of the entire `HipPath`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipPath;
    /// let s = HipPath::from("foobar");
    ///
    /// assert_eq!("foobar", s.as_os_str());
    /// ```
    #[inline]
    #[must_use]
    pub fn as_os_str(&self) -> &OsStr {
        self.0.as_os_str()
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
    /// # use hipstr::HipPath;
    /// let mut s: String = String::with_capacity(42);
    /// s.extend('a'..='z');
    /// let string = HipPath::from(s);
    /// assert_eq!(string.as_os_str().len(), 26);
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
    /// backing this `HipPath`.
    #[inline]
    pub fn into_os_string(self) -> Result<OsString, Self> {
        self.0.into_os_string().map_err(Self)
    }

    /// Converts `self` into a [`PathBuf`] without clone or allocation if possible.
    ///
    /// # Errors
    ///
    /// Returns `Err(self)` if it is impossible to take ownership of the string
    /// backing this `HipPath`.
    #[inline]
    pub fn into_path_buf(self) -> Result<PathBuf, Self> {
        self.0.into_os_string().map(PathBuf::from).map_err(Self)
    }

    /// Returns a mutable handle to the underlying [`PathBuf`].
    ///
    /// This operation may reallocate a new buffer if either:
    ///
    /// - the representation is not an allocated buffer (inline array or static borrow),
    /// - the underlying buffer is shared.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hipstr::HipPath;
    /// # use std::path::Path;
    /// let mut s = HipPath::borrowed("abc");
    /// {
    ///     let mut r = s.mutate();
    ///     r.push("def");
    ///     assert_eq!(&*r, Path::new("abc/def"));
    /// }
    /// assert_eq!(s, Path::new("abc/def"));
    /// ```
    #[inline]
    #[must_use]
    pub fn mutate(&mut self) -> RefMut<'_, 'borrow, B> {
        let owned = self.take_path_buf();
        RefMut {
            result: self,
            owned,
        }
    }

    fn take_path_buf(&mut self) -> PathBuf {
        PathBuf::from(self.0.take_os_string())
    }

    // /// Appends a given string slice onto the end of this `HipPath`.
    // ///
    // /// # Examples
    // ///
    // /// Basic usage:
    // ///
    // /// ```
    // /// # use hipstr::HipPath;
    // /// let mut s = HipPath::from("cork");
    // /// s.push_str("screw");
    // /// assert_eq!(s, "corkscrew");
    // /// ```
    // #[inline]
    // pub fn push_str(&mut self, addition: impl AsRef<OsStr>) {
    //     self.0.push_slice(addition.as_ref().as_encoded_bytes());
    // }

    // /// Appends the given [`char`] to the end of this `HipPath`.
    // ///
    // /// # Examples
    // ///
    // /// Basic usage:
    // ///
    // /// ```
    // /// # use hipstr::HipPath;
    // /// let mut s = HipPath::from("abc");
    // ///
    // /// s.push('1');
    // /// s.push('2');
    // /// s.push('3');
    // ///
    // /// assert_eq!(s, "abc123");
    // /// ```
    // #[inline]
    // pub fn push(&mut self, ch: char) {
    //     let mut data = [0; 4];
    //     let s = ch.encode_utf8(&mut data);
    //     self.0.push_slice(s.as_bytes());
    // }

    /// Makes the path owned, copying the data if it is actually borrowed.
    ///
    /// ```
    /// # use hipstr::HipPath;
    /// let s: String = ('a'..'z').collect();
    /// let s2 = s.clone();
    /// let h = HipPath::borrowed(&s[..]);
    /// // drop(s); // err, s is borrowed
    /// let h = h.into_owned();
    /// drop(s); // ok
    /// assert_eq!(h.as_os_str(), s2.as_str());
    /// ```
    #[must_use]
    pub fn into_owned(self) -> HipPath<'static, B> {
        HipPath(self.0.into_owned())
    }

    /// Converts the `HipPath` into a [`HipStr`] if it contains valid Unicode data.
    ///
    /// # Errors
    ///
    /// If it contains invalid Unicode data, ownership of the original `HipPath` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::{HipStr,HipPath};
    /// let os = HipPath::from("foo");
    /// let s = os.into_str();
    /// assert_eq!(s, Ok(HipStr::from("foo")));
    /// ```
    #[inline]
    pub fn into_str(self) -> Result<HipStr<'borrow, B>, Self> {
        self.0.into_str().map_err(Self)
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
    /// # use hipstr::{HipOsStr, HipPath};
    /// let mut s = HipOsStr::with_capacity(100);
    /// s.push("abc");
    /// let mut p = HipPath::from(s);
    /// assert!(p.capacity() >= 100);
    /// p.shrink_to_fit();
    /// assert_eq!(p.capacity(), HipPath::inline_capacity());
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
    /// # use hipstr::{HipOsStr, HipPath};
    /// let s = HipOsStr::with_capacity(100);
    /// let mut p = HipPath::from(s);
    /// p.shrink_to(4);
    /// assert_eq!(p.capacity(), HipPath::inline_capacity());
    /// ```
    #[inline]
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.0.shrink_to(min_capacity);
    }
}

impl<B> HipPath<'static, B>
where
    B: Backend,
{
    /// Creates a new `HipPath` from a static string slice without copying the slice.
    ///
    /// Handy shortcut to make a `HipPath<'static, _>` out of a `&'static str`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipPath;
    /// # use std::path::Path;
    /// let s = HipPath::from_static("hello");
    /// assert_eq!(s, Path::new("hello"));
    /// ```
    #[inline]
    #[must_use]
    pub const fn from_static(value: &'static str) -> Self {
        Self(HipOsStr::from_static(value))
    }
}

// Manual implementation needed to remove trait bound on B::RawPointer.
impl<'borrow, B> Clone for HipPath<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

// Manual implementation needed to remove trait bound on B::RawPointer.
impl<'borrow, B> Default for HipPath<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<'borrow, B> Deref for HipPath<'borrow, B>
where
    B: Backend,
{
    type Target = Path;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_path()
    }
}

impl<'borrow, B> Hash for HipPath<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.as_path().hash(state);
    }
}

// Formatting

impl<'borrow, B> fmt::Debug for HipPath<'borrow, B>
where
    B: Backend,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.as_path(), f)
    }
}

/// A wrapper type for a mutably borrowed [`String`] out of a [`HipPath`].
pub struct RefMut<'a, 'borrow, B>
where
    B: Backend,
{
    result: &'a mut HipPath<'borrow, B>,
    owned: PathBuf,
}

impl<'a, 'borrow, B> fmt::Debug for RefMut<'a, 'borrow, B>
where
    B: Backend,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.owned.fmt(f)
    }
}

impl<'a, 'borrow, B> Drop for RefMut<'a, 'borrow, B>
where
    B: Backend,
{
    fn drop(&mut self) {
        let owned = core::mem::take(&mut self.owned);
        *self.result = HipPath::from(owned);
    }
}

impl<'a, 'borrow, B> Deref for RefMut<'a, 'borrow, B>
where
    B: Backend,
{
    type Target = PathBuf;
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
