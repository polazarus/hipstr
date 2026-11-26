//! Platform strings: [`HipOsStr`], [`SmallOsStr`], [`TinyOsStr`].

use std::ffi::{OsStr, OsString};

use super::enc::{self, Utf8};
use super::family::impl_std_glue;
use super::hip::Hip;
use super::repr::Repr;

super::generic_aliases!(
    enc::OsStr,
    HipOsStr,
    SmallOsStr,
    TinyOsStr,
    "platform string"
);

impl_std_glue!(enc::OsStr, OsStr, OsString);

impl<'a, R: Repr<'a, u8>> Hip<enc::OsStr, R> {
    /// The platform string slice.
    #[inline]
    #[must_use]
    pub fn as_os_str(&self) -> &OsStr {
        self.as_inner()
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

    /// Appends a platform string.
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

    /// Converts into a UTF-8 string, keeping the representation (no copy).
    ///
    /// # Errors
    ///
    /// Returns `Err(self)` if the value is not valid UTF-8.
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
    /// Borrows the value without copying.
    #[inline]
    #[must_use]
    pub fn borrowed(value: &'a (impl AsRef<OsStr> + ?Sized)) -> Self {
        Self::from_inner_borrowed(value.as_ref())
    }
}

impl<'a, B: super::backend::Backend> Hip<enc::OsStr, super::repr::Small<'a, u8, B>> {
    /// Borrows the value without copying.
    #[inline]
    #[must_use]
    pub fn borrowed(value: &'a (impl AsRef<OsStr> + ?Sized)) -> Self {
        Self::from_inner_borrowed(value.as_ref())
    }
}
