//! Paths: [`HipPath`], [`SmallPath`], [`TinyPath`].

use alloc::borrow::Cow;
use alloc::boxed::Box;
use alloc::string::String;
use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};

use super::enc::{self, Utf8};
use super::family::{impl_cmp, impl_std_glue};
use super::hip::Hip;
use super::repr::Repr;
pub use crate::hip::RefMut;

/// `serde` helpers.
#[cfg(feature = "serde")]
pub mod serde {
    #[cfg(test)]
    use ::serde::Deserialize;

    pub use crate::serde_impl::path::borrow_deserialize;

    #[cfg(test)]
    mod tests;
}

#[cfg(test)]
mod tests;

super::generic_aliases!(enc::Path, HipPath, SmallPath, TinyPath, "path");

impl_std_glue!(enc::Path, Path, PathBuf);

impl_cmp!(enc::Path as Path;
    [] Path, [] &Path, [] PathBuf, [] &PathBuf, [] Box<Path>, [] &Box<Path>,
    [] Cow<'_, Path>, [] &Cow<'_, Path>,
    [] OsStr, [] &OsStr, [] OsString, [] &OsString, [] Cow<'_, OsStr>, [] &Cow<'_, OsStr>,
);
impl_cmp!(enc::Path as OsStr; [] Box<OsStr>, [] &Box<OsStr>);

impl<'a, R1: Repr<'a, u8>, R2: Repr<'a, u8>> PartialEq<Hip<enc::OsStr, R2>> for Hip<enc::Path, R1> {
    #[inline]
    fn eq(&self, other: &Hip<enc::OsStr, R2>) -> bool {
        self.as_path() == <Hip<enc::OsStr, R2> as AsRef<Path>>::as_ref(other)
    }
}

impl<'a, R1: Repr<'a, u8>, R2: Repr<'a, u8>> PartialEq<Hip<enc::Path, R2>> for Hip<enc::OsStr, R1> {
    #[inline]
    fn eq(&self, other: &Hip<enc::Path, R2>) -> bool {
        <Self as AsRef<Path>>::as_ref(self) == other.as_path()
    }
}

impl<'a, R: Repr<'a, u8>> AsRef<OsStr> for Hip<enc::Path, R> {
    #[inline]
    fn as_ref(&self) -> &OsStr {
        self.as_os_str()
    }
}

impl<'a, R: Repr<'a, u8>> From<&OsStr> for Hip<enc::Path, R> {
    #[inline]
    fn from(value: &OsStr) -> Self {
        Self::from_inner(Path::new(value))
    }
}

impl<'a, R: Repr<'a, u8>> From<OsString> for Hip<enc::Path, R> {
    /// Adopts the buffer when it does not fit inline (no copy).
    #[inline]
    fn from(value: OsString) -> Self {
        Self::from_owned(value.into())
    }
}

impl<'a, R: Repr<'a, u8>> From<String> for Hip<enc::Path, R> {
    /// Adopts the buffer when it does not fit inline (no copy).
    #[inline]
    fn from(value: String) -> Self {
        Self::from_owned(value.into())
    }
}

impl<'a, R: Repr<'a, u8>> From<Box<str>> for Hip<enc::Path, R> {
    #[inline]
    fn from(value: Box<str>) -> Self {
        Self::from(String::from(value))
    }
}

impl<'a, R: Repr<'a, u8>> From<Cow<'a, str>> for Hip<enc::Path, R> {
    /// Borrows `Cow::Borrowed` (copies if the representation cannot borrow).
    #[inline]
    fn from(value: Cow<'a, str>) -> Self {
        match value {
            Cow::Borrowed(s) => Self::from_inner_borrowed(Path::new(s)),
            Cow::Owned(s) => Self::from(s),
        }
    }
}

impl<'a, R: Repr<'a, u8>> From<Cow<'a, OsStr>> for Hip<enc::Path, R> {
    /// Borrows `Cow::Borrowed` (copies if the representation cannot borrow).
    #[inline]
    fn from(value: Cow<'a, OsStr>) -> Self {
        match value {
            Cow::Borrowed(s) => Self::from_inner_borrowed(Path::new(s)),
            Cow::Owned(s) => Self::from(s),
        }
    }
}

impl<'a, R: Repr<'a, u8>> From<&Hip<Utf8, R>> for Hip<enc::Path, R> {
    /// Shares the storage (no copy).
    #[inline]
    fn from(value: &Hip<Utf8, R>) -> Self {
        Self::from(value.clone())
    }
}

impl<'a, R: Repr<'a, u8>> From<&Hip<enc::OsStr, R>> for Hip<enc::Path, R> {
    /// Shares the storage (no copy).
    #[inline]
    fn from(value: &Hip<enc::OsStr, R>) -> Self {
        Self::from(value.clone())
    }
}

impl<'a, R: Repr<'a, u8>> From<Hip<enc::Path, R>> for OsString {
    /// O(1) when the value uniquely owns an adopted buffer.
    #[inline]
    fn from(value: Hip<enc::Path, R>) -> Self {
        value.into_os_string()
    }
}

impl<'a, R: Repr<'a, u8>> From<Hip<enc::Path, R>> for Hip<enc::OsStr, R> {
    /// Keeps the representation (no copy).
    #[inline]
    fn from(value: Hip<enc::Path, R>) -> Self {
        value.into_os_str()
    }
}

impl<'a, R: Repr<'a, u8>> From<&Hip<enc::Path, R>> for Hip<enc::OsStr, R> {
    /// Shares the storage (no copy).
    #[inline]
    fn from(value: &Hip<enc::Path, R>) -> Self {
        value.clone().into_os_str()
    }
}

impl<'a, R: Repr<'a, u8>> Hip<enc::Path, R> {
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
        self.as_inner()
    }

    /// Yields an [`OsStr`] slice of the entire `HipPath`.
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
    /// assert_eq!(Path::new("foobar"), s.as_os_str());
    /// ```
    #[inline]
    #[must_use]
    pub fn as_os_str(&self) -> &OsStr {
        self.as_path().as_os_str()
    }

    /// Converts into a `PathBuf`, in O(1) when the value uniquely owns an
    /// adopted buffer, by copying otherwise.
    #[inline]
    #[must_use]
    pub fn into_path_buf(self) -> PathBuf {
        self.into_owned_std()
    }

    /// Extends the path with `path` (see `PathBuf::push`: an absolute `path`
    /// replaces the current one).
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipPath;
    /// # use std::path::Path;
    /// let mut p = HipPath::borrowed("/tmp");
    /// p.push("file.bk");
    /// assert_eq!(p, Path::new("/tmp/file.bk"));
    /// p.push("/etc");
    /// assert_eq!(p, Path::new("/etc"));
    /// ```
    pub fn push(&mut self, path: impl AsRef<Path>) {
        self.mutate().push(path);
    }

    /// Truncates to the parent (see `PathBuf::pop`), in O(1) and without
    /// copying a borrowed or shared value.
    ///
    /// Returns `false` and does nothing if there is no parent.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipPath;
    /// # use std::path::Path;
    /// let mut p = HipPath::borrowed("/spirited/away.rs");
    /// assert!(p.pop());
    /// assert_eq!(p, Path::new("/spirited"));
    /// assert!(p.is_borrowed());
    /// assert!(p.pop());
    /// assert!(!p.pop());
    /// assert_eq!(p, Path::new("/"));
    /// ```
    pub fn pop(&mut self) -> bool {
        let Some(parent) = self.as_path().parent() else {
            return false;
        };
        let len = parent.as_os_str().len();
        // SAFETY: the parent is a prefix of the path
        unsafe { self.truncate_bytes(len) };
        true
    }

    /// Replaces the file name (see `PathBuf::set_file_name`).
    pub fn set_file_name(&mut self, file_name: impl AsRef<OsStr>) {
        self.mutate().set_file_name(file_name);
    }

    /// Replaces the extension (see `PathBuf::set_extension`).
    ///
    /// Returns `false` and does nothing if there is no file name.
    pub fn set_extension(&mut self, extension: impl AsRef<OsStr>) -> bool {
        if self.as_path().file_name().is_none() {
            return false;
        }
        self.mutate().set_extension(extension)
    }

    /// Appends an extension (see `PathBuf::add_extension`).
    ///
    /// Returns `false` and does nothing if there is no file name.
    ///
    /// # Panics
    ///
    /// Panics if the extension contains a path separator.
    pub fn add_extension(&mut self, extension: impl AsRef<OsStr>) -> bool {
        if self.as_path().file_name().is_none() {
            return false;
        }
        self.mutate().add_extension(extension)
    }

    /// Converts into a `String` if valid UTF-8 (see `PathBuf::into_string`).
    ///
    /// For a conversion keeping the storage, see [`into_str`](Self::into_str).
    ///
    /// # Errors
    ///
    /// Returns the value unchanged if it is not valid UTF-8.
    pub fn into_string(self) -> Result<String, Self> {
        if self.as_path().to_str().is_some() {
            Ok(self.into_path_buf().into_string().unwrap_or_default())
        } else {
            Err(self)
        }
    }

    /// Converts into a boxed path.
    #[inline]
    #[must_use]
    pub fn into_boxed_path(self) -> Box<Path> {
        self.into_path_buf().into_boxed_path()
    }

    /// Leaks the path, returning a mutable reference to it (see
    /// `PathBuf::leak`).
    #[inline]
    #[must_use]
    pub fn leak<'b>(self) -> &'b mut Path {
        self.into_path_buf().leak()
    }

    /// Converts into an `OsString` (see [`into_path_buf`](Self::into_path_buf)).
    #[inline]
    #[must_use]
    pub fn into_os_string(self) -> OsString {
        self.into_path_buf().into_os_string()
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
    /// # use std::path::Path;
    /// let s = HipPath::from("hello");
    /// let b = s.into_os_str();
    ///
    /// assert_eq!(b, Path::new("hello"));
    /// ```
    #[inline]
    #[must_use]
    pub fn into_os_str(self) -> Hip<enc::OsStr, R> {
        // SAFETY: same encoding of bytes
        unsafe { Hip::from_repr(self.into_repr()) }
    }

    /// Returns the borrowed slice if this `Path` is actually borrowed, `None`
    /// otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipPath;
    /// # use std::path::Path;
    /// let abc: &'static Path = Path::new("abc");
    /// let s = HipPath::borrowed(abc);
    /// let c: Option<&'static Path> = s.as_borrowed();
    /// assert_eq!(c, Some(abc));
    /// assert!(std::ptr::eq(abc, c.unwrap()));
    ///
    /// let s2 = HipPath::from(abc);
    /// assert!(s2.as_borrowed().is_none());
    /// ```
    #[inline]
    #[must_use]
    pub fn as_borrowed(&self) -> Option<&'a Path> {
        self.borrowed_inner()
    }

    /// Converts `self` into a path slice with the `'borrow` lifetime if this
    /// `HipPath` is backed by a borrow.
    ///
    /// # Errors
    ///
    /// Returns `Err(self)` if this `HipPath` is not borrowed.
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
    pub fn into_borrowed(self) -> Result<&'a Path, Self> {
        match self.borrowed_inner() {
            Some(b) => Ok(b),
            None => Err(self),
        }
    }

    /// Converts the `HipPath` into a `HipStr` if it contains valid Unicode data.
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
    pub fn into_str(self) -> Result<Hip<Utf8, R>, Self> {
        if self.as_path().to_str().is_some() {
            // SAFETY: checked UTF-8
            Ok(unsafe { Hip::from_repr(self.into_repr()) })
        } else {
            Err(self)
        }
    }
}

impl<'a, R: Repr<'a, u8>> From<&str> for Hip<enc::Path, R> {
    #[inline]
    fn from(value: &str) -> Self {
        Self::from_inner(Path::new(value))
    }
}

impl<'a, R: Repr<'a, u8>> From<Hip<Utf8, R>> for Hip<enc::Path, R> {
    /// Keeps the representation (no copy).
    #[inline]
    fn from(value: Hip<Utf8, R>) -> Self {
        // SAFETY: UTF-8 bytes are valid encoded OS string bytes
        unsafe { Self::from_repr(value.into_repr()) }
    }
}

impl<'a, R: Repr<'a, u8>> From<Hip<enc::OsStr, R>> for Hip<enc::Path, R> {
    /// Keeps the representation (no copy).
    #[inline]
    fn from(value: Hip<enc::OsStr, R>) -> Self {
        // SAFETY: same encoding of bytes
        unsafe { Self::from_repr(value.into_repr()) }
    }
}

impl<'a, B: super::backend::Backend> Hip<enc::Path, super::repr::Wide<'a, u8, B>> {
    /// Creates a new `HipPath` from a static string slice without copying the slice.
    ///
    /// # Representation
    ///
    /// The created `HipPath` is _borrowed_.
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
        Self::from_repr_const(super::repr::Wide::borrowed(value.as_bytes()))
    }

    /// Creates a new `HipPath` from an OS string slice without copying the
    /// slice.
    ///
    /// Requires only `impl AsRef<Path>`: it accepts `&str`, `&OsStr`, and
    /// `&Path` for instance.
    ///
    /// To create a `HipPath` from a `'static` string slice `const`-ly, see
    /// [`HipPath::from_static`].
    ///
    /// # Representation
    ///
    /// The created `HipPath` is _borrowed_.
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
    #[inline]
    #[must_use]
    pub fn borrowed(value: &'a (impl AsRef<Path> + ?Sized)) -> Self {
        Self::from_inner_borrowed(value.as_ref())
    }
}

impl<'a, B: super::backend::Backend> Hip<enc::Path, super::repr::Small<'a, u8, B>> {
    /// Creates a new `HipPath` from a static string slice without copying the slice.
    ///
    /// # Representation
    ///
    /// The created `HipPath` is _borrowed_.
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
        Self::from_repr_const(super::repr::Small::borrowed(value.as_bytes()))
    }

    /// Creates a new `HipPath` from an OS string slice without copying the
    /// slice.
    ///
    /// Requires only `impl AsRef<Path>`: it accepts `&str`, `&OsStr`, and
    /// `&Path` for instance.
    ///
    /// To create a `HipPath` from a `'static` string slice `const`-ly, see
    /// [`HipPath::from_static`].
    ///
    /// # Representation
    ///
    /// The created `HipPath` is _borrowed_.
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
    #[inline]
    #[must_use]
    pub fn borrowed(value: &'a (impl AsRef<Path> + ?Sized)) -> Self {
        Self::from_inner_borrowed(value.as_ref())
    }
}
