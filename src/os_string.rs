//! Platform strings: [`HipOsStr`], [`SmallOsStr`], [`TinyOsStr`].

use alloc::borrow::Cow;
use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;
use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};

use super::enc::{self, Bytes, Utf8};
use super::family::{impl_cmp, impl_std_glue};
use super::hip::Hip;
use super::repr::Repr;
pub use crate::hip::RefMut;

#[cfg(test)]
mod tests;

super::generic_aliases!(
    enc::OsStr,
    HipOsStr,
    SmallOsStr,
    TinyOsStr,
    "platform string"
);

impl_std_glue!(enc::OsStr, OsStr, OsString);

impl_cmp!(enc::OsStr as OsStr;
    [] OsStr, [] &OsStr, [] OsString, [] &OsString, [] Box<OsStr>, [] &Box<OsStr>,
    [] Cow<'_, OsStr>, [] &Cow<'_, OsStr>,
);
impl_cmp!(enc::OsStr as Path;
    [] Path, [] &Path, [] PathBuf, [] &PathBuf, [] Box<Path>, [] &Box<Path>,
    [] Cow<'_, Path>, [] &Cow<'_, Path>,
);

impl<'a, R: Repr<'a, u8>> AsRef<Path> for Hip<enc::OsStr, R> {
    #[inline]
    fn as_ref(&self) -> &Path {
        Path::new(self.as_inner())
    }
}

impl<'a, R: Repr<'a, u8>> From<String> for Hip<enc::OsStr, R> {
    /// Adopts the buffer when it does not fit inline (no copy).
    #[inline]
    fn from(value: String) -> Self {
        Self::from_owned(value.into())
    }
}

impl<'a, R: Repr<'a, u8>> From<Box<str>> for Hip<enc::OsStr, R> {
    #[inline]
    fn from(value: Box<str>) -> Self {
        Self::from(String::from(value))
    }
}

impl<'a, R: Repr<'a, u8>> From<Cow<'a, str>> for Hip<enc::OsStr, R> {
    /// Borrows `Cow::Borrowed` (copies if the representation cannot borrow).
    #[inline]
    fn from(value: Cow<'a, str>) -> Self {
        match value {
            Cow::Borrowed(s) => Self::from_inner_borrowed(OsStr::new(s)),
            Cow::Owned(s) => Self::from(s),
        }
    }
}

impl<'a, R: Repr<'a, u8>> From<&Hip<Utf8, R>> for Hip<enc::OsStr, R> {
    /// Shares the storage (no copy).
    #[inline]
    fn from(value: &Hip<Utf8, R>) -> Self {
        Self::from(value.clone())
    }
}

impl<'a, R: Repr<'a, u8>> From<Hip<enc::OsStr, R>> for Hip<Bytes, R> {
    /// The encoded bytes, keeping the representation (no copy).
    #[inline]
    fn from(value: Hip<enc::OsStr, R>) -> Self {
        value.into_bytes()
    }
}

impl<'a, R: Repr<'a, u8>> From<Hip<enc::OsStr, R>> for Vec<u8> {
    /// The encoded bytes, O(1) when the value uniquely owns an adopted buffer.
    #[inline]
    fn from(value: Hip<enc::OsStr, R>) -> Self {
        value.into_os_string().into_encoded_bytes()
    }
}

impl<'a, R: Repr<'a, u8>> Hip<enc::OsStr, R> {
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
        self.as_inner()
    }

    /// Raw pointer to the first encoded byte.
    #[inline]
    #[must_use]
    pub fn as_ptr(&self) -> *const u8 {
        self.bytes().as_ptr()
    }

    /// The encoded bytes (see [`OsStr::as_encoded_bytes`]).
    #[inline]
    #[must_use]
    pub fn as_encoded_bytes(&self) -> &[u8] {
        self.bytes()
    }

    /// Converts into an `OsString`, in O(1) when the value uniquely owns an
    /// adopted buffer, by copying otherwise.
    #[inline]
    #[must_use]
    pub fn into_os_string(self) -> OsString {
        self.into_owned_std()
    }

    /// Appends a given string slice onto the end of this `HipOsStr`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipOsStr;
    /// # use std::ffi::OsStr;
    /// let mut s = HipOsStr::from("cork");
    /// s.push("screw");
    /// assert_eq!(s, OsStr::new("corkscrew"));
    /// ```
    #[inline]
    pub fn push(&mut self, addition: impl AsRef<OsStr>) {
        // SAFETY: concatenation of encoded OS strings is a valid encoded OS string
        unsafe { self.push_bytes(addition.as_ref().as_encoded_bytes()) }
    }

    /// The string slice, if valid UTF-8.
    #[inline]
    #[must_use]
    pub fn to_str(&self) -> Option<&str> {
        self.as_os_str().to_str()
    }

    /// Lossy conversion to a string.
    #[inline]
    #[must_use]
    pub fn to_string_lossy(&self) -> alloc::borrow::Cow<'_, str> {
        self.as_os_str().to_string_lossy()
    }

    /// Returns the borrowed slice if this `HipOsStr` is actually borrowed,
    /// `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipOsStr;
    /// # use std::ffi::OsStr;
    /// let abc: &'static OsStr = OsStr::new("abc");
    /// let s = HipOsStr::borrowed(abc);
    /// let c: Option<&'static OsStr> = s.as_borrowed();
    /// assert_eq!(c, Some(abc));
    /// assert!(std::ptr::eq(abc, c.unwrap()));
    ///
    /// let s2 = HipOsStr::from(abc);
    /// assert!(s2.as_borrowed().is_none());
    /// ```
    #[inline]
    #[must_use]
    pub fn as_borrowed(&self) -> Option<&'a OsStr> {
        self.borrowed_inner()
    }

    /// Converts `self` into a string slice with the `'borrow` lifetime if this
    /// `HipOsStr` is backed by a borrow.
    ///
    /// # Errors
    ///
    /// Returns `Err(self)` if this `HipOsStr` is not borrowed.
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
    pub fn into_borrowed(self) -> Result<&'a OsStr, Self> {
        match self.borrowed_inner() {
            Some(b) => Ok(b),
            None => Err(self),
        }
    }

    /// Converts a `HipOsStr` into a `HipByt`.
    ///
    /// It consumes the `HipOsStr` without copying the content
    /// (if [shared][Self::is_allocated] or [borrowed][Self::is_borrowed]).
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
    #[inline]
    #[must_use]
    pub const fn into_bytes(self) -> Hip<Bytes, R> {
        // SAFETY: no invariant on bytes
        unsafe { Hip::from_repr(self.into_repr()) }
    }

    /// Converts a `HipOsStr` to a `HipStr`.
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
    #[must_use]
    pub fn to_str_lossy(&self) -> Hip<Utf8, R> {
        match self.as_os_str().to_string_lossy() {
            // SAFETY: valid UTF-8
            Cow::Borrowed(_) => unsafe { Hip::from_repr(self.repr().clone()) },
            Cow::Owned(s) => Hip::from(s),
        }
    }

    /// Converts the `HipOsStr` into a `HipStr` if it contains valid Unicode data.
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
    pub fn into_str(self) -> Result<Hip<Utf8, R>, Self> {
        if self.to_str().is_some() {
            // SAFETY: checked UTF-8
            Ok(unsafe { Hip::from_repr(self.into_repr()) })
        } else {
            Err(self)
        }
    }
}

impl<'a, R: Repr<'a, u8>> From<&str> for Hip<enc::OsStr, R> {
    #[inline]
    fn from(value: &str) -> Self {
        Self::from_inner(OsStr::new(value))
    }
}

impl<'a, R: Repr<'a, u8>> From<Hip<Utf8, R>> for Hip<enc::OsStr, R> {
    /// Keeps the representation (no copy): UTF-8 is a valid encoded OS string.
    #[inline]
    fn from(value: Hip<Utf8, R>) -> Self {
        // SAFETY: UTF-8 bytes are valid encoded OS string bytes
        unsafe { Self::from_repr(value.into_repr()) }
    }
}

impl<'a, B: super::backend::Backend> Hip<enc::OsStr, super::repr::Wide<'a, u8, B>> {
    /// Creates a new `HipOsStr` from a `'static` string slice without copying
    /// the slice.
    ///
    /// # Representation
    ///
    /// The created `HipOsStr` is _borrowed_.
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
        Self::from_repr_const(super::repr::Wide::borrowed(value.as_bytes()))
    }

    /// Creates a new `HipOsStr` from an OS string slice without copying the
    /// slice.
    ///
    /// Requires only `impl AsRef<OsStr>`: it accepts `&str`, `&OsStr`, and
    /// `&Path` for instance.
    ///
    /// To create a `HipOsStr` from a `'static` string slice `const`-ly, see
    /// [`HipOsStr::from_static`].
    ///
    /// # Representation
    ///
    /// The created `HipOsStr` is _borrowed_.
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
    #[inline]
    #[must_use]
    pub fn borrowed(value: &'a (impl AsRef<OsStr> + ?Sized)) -> Self {
        Self::from_inner_borrowed(value.as_ref())
    }
}

impl<'a, B: super::backend::Backend> Hip<enc::OsStr, super::repr::Small<'a, u8, B>> {
    /// Creates a new `HipOsStr` from a `'static` string slice without copying
    /// the slice.
    ///
    /// # Representation
    ///
    /// The created `HipOsStr` is _borrowed_.
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
        Self::from_repr_const(super::repr::Small::borrowed(value.as_bytes()))
    }

    /// Creates a new `HipOsStr` from an OS string slice without copying the
    /// slice.
    ///
    /// Requires only `impl AsRef<OsStr>`: it accepts `&str`, `&OsStr`, and
    /// `&Path` for instance.
    ///
    /// To create a `HipOsStr` from a `'static` string slice `const`-ly, see
    /// [`HipOsStr::from_static`].
    ///
    /// # Representation
    ///
    /// The created `HipOsStr` is _borrowed_.
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
    #[inline]
    #[must_use]
    pub fn borrowed(value: &'a (impl AsRef<OsStr> + ?Sized)) -> Self {
        Self::from_inner_borrowed(value.as_ref())
    }
}
