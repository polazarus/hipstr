//! Paths: [`HipPath`], [`SmallPath`], [`TinyPath`].

use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};

use super::enc::{self, Utf8};
use super::family::impl_std_glue;
use super::hip::Hip;
use super::repr::Repr;

super::generic_aliases!(enc::Path, HipPath, SmallPath, TinyPath, "path");

impl_std_glue!(enc::Path, Path, PathBuf);

impl<'a, R: Repr<'a, u8>> Hip<enc::Path, R> {
    /// The path slice.
    #[inline]
    #[must_use]
    pub fn as_path(&self) -> &Path {
        self.as_inner()
    }

    /// The path as a platform string.
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

    /// Converts into an `OsString` (see [`into_path_buf`](Self::into_path_buf)).
    #[inline]
    #[must_use]
    pub fn into_os_string(self) -> OsString {
        self.into_path_buf().into_os_string()
    }

    /// Converts into a platform string, keeping the representation (no copy).
    #[inline]
    #[must_use]
    pub fn into_os_str(self) -> Hip<enc::OsStr, R> {
        // SAFETY: same encoding of bytes
        unsafe { Hip::from_repr(self.into_repr()) }
    }

    /// The borrowed value, with its full lifetime, if borrowed.
    ///
    /// Not `const`: std's `OsStr`/`Path` conversions are not `const`.
    #[inline]
    #[must_use]
    pub fn as_borrowed(&self) -> Option<&'a Path> {
        self.borrowed_inner()
    }

    /// Returns the borrowed value, with its full lifetime, or `Err(self)`.
    ///
    /// # Errors
    ///
    /// Returns `Err(self)` if the value is not borrowed.
    #[inline]
    pub fn into_borrowed(self) -> Result<&'a Path, Self> {
        match self.borrowed_inner() {
            Some(b) => Ok(b),
            None => Err(self),
        }
    }

    /// Converts into a UTF-8 string, keeping the representation (no copy).
    ///
    /// # Errors
    ///
    /// Returns `Err(self)` if the path is not valid UTF-8.
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
    /// Borrows the value without copying.
    #[inline]
    #[must_use]
    pub fn borrowed(value: &'a (impl AsRef<Path> + ?Sized)) -> Self {
        Self::from_inner_borrowed(value.as_ref())
    }
}

impl<'a, B: super::backend::Backend> Hip<enc::Path, super::repr::Small<'a, u8, B>> {
    /// Borrows the value without copying.
    #[inline]
    #[must_use]
    pub fn borrowed(value: &'a (impl AsRef<Path> + ?Sized)) -> Self {
        Self::from_inner_borrowed(value.as_ref())
    }
}
