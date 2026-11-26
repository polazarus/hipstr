//! UTF-8 strings: [`HipStr`], [`SmallStr`], [`TinyStr`].

use alloc::borrow::Cow;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;
use core::str::Utf8Error;

use super::enc::{Bytes, Utf8};
use super::family::{impl_borrowed_ctors, impl_std_glue};
use super::hip::Hip;
use super::repr::Repr;

super::generic_aliases!(Utf8, HipStr, SmallStr, TinyStr, "string");

impl_std_glue!(Utf8, str, String);
impl_borrowed_ctors!(Utf8, str, |value| value.as_bytes());
super::hip::impl_const_typed_accessors!(Utf8, str, |b| core::str::from_utf8_unchecked(b));

/// `const` string accessors and UTF-8 conversions, per representation.
macro_rules! impl_const_str {
    ($([$($lt:lifetime)?] $repr:ty),* $(,)?) => {$(
        impl<$($lt,)? B: super::backend::Backend> Hip<Utf8, $repr> {
            /// The string slice.
            #[inline]
            #[must_use]
            pub const fn as_str(&self) -> &str {
                self.as_typed()
            }

            /// The bytes.
            #[inline]
            #[must_use]
            pub const fn as_bytes(&self) -> &[u8] {
                self.repr().as_slice()
            }

            /// Converts bytes into a string, keeping the representation (no copy).
            ///
            /// # Errors
            ///
            /// Returns the bytes back, with the UTF-8 error, if they are not UTF-8.
            pub const fn from_utf8(bytes: Hip<Bytes, $repr>) -> Result<Self, FromUtf8Error<$repr>> {
                match core::str::from_utf8(bytes.repr().as_slice()) {
                    // SAFETY: checked
                    Ok(_) => Ok(unsafe { Self::from_utf8_unchecked(bytes) }),
                    Err(error) => Err(FromUtf8Error { bytes, error }),
                }
            }

            /// Converts bytes into a string without checking (no copy).
            ///
            /// # Safety
            ///
            /// The bytes must be valid UTF-8.
            #[inline]
            #[must_use]
            pub const unsafe fn from_utf8_unchecked(bytes: Hip<Bytes, $repr>) -> Self {
                // SAFETY: precondition
                unsafe { Self::from_repr(bytes.into_repr()) }
            }
        }
    )*};
}

impl_const_str!(
    ['a] super::repr::Wide<'a, u8, B>,
    ['a] super::repr::Small<'a, u8, B>,
    [] super::repr::Tiny<u8, B>,
);

impl<'a, R: Repr<'a, u8>> Hip<Utf8, R> {
    /// Generic version of `from_utf8` (the public one is `const`, per repr).
    pub(crate) fn from_utf8_generic(bytes: Hip<Bytes, R>) -> Result<Self, FromUtf8Error<R>> {
        match core::str::from_utf8(bytes.as_inner()) {
            // SAFETY: checked
            Ok(_) => Ok(unsafe { Self::from_repr(bytes.into_repr()) }),
            Err(error) => Err(FromUtf8Error { bytes, error }),
        }
    }

    /// Converts into bytes, keeping the representation (no copy).
    #[inline]
    #[must_use]
    pub const fn into_bytes(self) -> Hip<Bytes, R> {
        // SAFETY: no invariant on bytes
        unsafe { Hip::from_repr(self.into_repr()) }
    }

    /// Converts into a `String`, in O(1) when the value uniquely owns an
    /// adopted buffer, by copying otherwise.
    #[inline]
    #[must_use]
    pub fn into_string(self) -> String {
        self.into_owned_std()
    }

    /// Mutable access without copying, if inline or uniquely owned.
    #[inline]
    pub fn as_mut_str(&mut self) -> Option<&mut str> {
        if self.repr().is_unique() {
            Some(self.to_mut_str())
        } else {
            None
        }
    }

    /// Mutable access, copying first if borrowed or shared.
    #[inline]
    #[allow(
        clippy::wrong_self_convention,
        reason = "same name as on the current types"
    )]
    pub fn to_mut_str(&mut self) -> &mut str {
        // SAFETY: `str`'s safe API preserves UTF-8
        let bytes = unsafe { self.repr_mut() }.to_mut_slice();
        // SAFETY: type invariant
        unsafe { core::str::from_utf8_unchecked_mut(bytes) }
    }

    /// Appends a string slice.
    #[inline]
    pub fn push_str(&mut self, addition: &str) {
        // SAFETY: concatenation of UTF-8 is UTF-8
        unsafe { self.push_bytes(addition.as_bytes()) }
    }

    /// Appends a character.
    #[inline]
    pub fn push(&mut self, ch: char) {
        self.push_str(ch.encode_utf8(&mut [0; 4]));
    }

    /// Removes and returns the last character.
    pub fn pop(&mut self) -> Option<char> {
        let ch = self.as_inner().chars().next_back()?;
        // SAFETY: cut at a character boundary
        unsafe { self.truncate_bytes(self.bytes().len() - ch.len_utf8()) };
        Some(ch)
    }

    /// Shortens to `new_len` bytes; no-op if `new_len` is greater than the length.
    ///
    /// # Panics
    ///
    /// Panics if `new_len` does not lie on a character boundary.
    pub fn truncate(&mut self, new_len: usize) {
        if new_len < self.bytes().len() {
            assert!(
                self.as_inner().is_char_boundary(new_len),
                "new length is not a char boundary"
            );
            // SAFETY: cut at a character boundary
            unsafe { self.truncate_bytes(new_len) };
        }
    }

    /// Converts bytes into a string, replacing invalid sequences with `U+FFFD`.
    ///
    /// Keeps the representation (no copy) when the bytes are valid.
    #[must_use]
    pub fn from_utf8_lossy(bytes: Hip<Bytes, R>) -> Self {
        match String::from_utf8_lossy(bytes.as_inner()) {
            // SAFETY: valid UTF-8, as `Borrowed` is only returned when valid
            Cow::Borrowed(_) => unsafe { Self::from_repr(bytes.into_repr()) },
            Cow::Owned(s) => Self::from(s),
        }
    }

    /// Decodes UTF-16.
    ///
    /// # Errors
    ///
    /// Returns an error if `v` contains invalid data.
    pub fn from_utf16(v: &[u16]) -> Result<Self, alloc::string::FromUtf16Error> {
        String::from_utf16(v).map(Self::from)
    }

    /// Decodes UTF-16, replacing invalid data with `U+FFFD`.
    #[must_use]
    pub fn from_utf16_lossy(v: &[u16]) -> Self {
        Self::from(String::from_utf16_lossy(v))
    }

    /// Repeats the string `n` times.
    ///
    /// # Panics
    ///
    /// Panics if the capacity overflows.
    #[must_use]
    pub fn repeat(&self, n: usize) -> Self {
        let len = self
            .bytes()
            .len()
            .checked_mul(n)
            .expect("capacity overflow");
        let mut result = Self::with_capacity(len);
        for _ in 0..n {
            result.push_str(self.as_inner());
        }
        result
    }

    /// ASCII lower-case copy.
    #[must_use]
    pub fn to_ascii_lowercase(&self) -> Self {
        let mut result = self.clone();
        result.make_ascii_lowercase();
        result
    }

    /// ASCII upper-case copy.
    #[must_use]
    pub fn to_ascii_uppercase(&self) -> Self {
        let mut result = self.clone();
        result.make_ascii_uppercase();
        result
    }

    /// Converts to ASCII lower case in place (copying first if needed).
    pub fn make_ascii_lowercase(&mut self) {
        if self.as_inner().bytes().any(|b| b.is_ascii_uppercase()) {
            self.to_mut_str().make_ascii_lowercase();
        }
    }

    /// Converts to ASCII upper case in place (copying first if needed).
    pub fn make_ascii_uppercase(&mut self) {
        if self.as_inner().bytes().any(|b| b.is_ascii_lowercase()) {
            self.to_mut_str().make_ascii_uppercase();
        }
    }

    /// Unicode lower-case copy.
    #[must_use]
    pub fn to_lowercase(&self) -> Self {
        Self::from(self.as_inner().to_lowercase())
    }

    /// Unicode upper-case copy.
    #[must_use]
    pub fn to_uppercase(&self) -> Self {
        Self::from(self.as_inner().to_uppercase())
    }

    /// Concatenates string slices.
    #[must_use]
    pub fn concat_slices(slices: &[&str]) -> Self {
        Self::concat(slices)
    }

    /// Concatenates strings.
    #[must_use]
    pub fn concat<S: AsRef<str>, I: IntoIterator<Item = S>>(slices: I) -> Self
    where
        I::IntoIter: Clone,
    {
        let iter = slices.into_iter();
        let len = iter.clone().map(|s| s.as_ref().len()).sum();
        let mut result = Self::with_capacity(len);
        for s in iter {
            result.push_str(s.as_ref());
        }
        result
    }

    /// Joins string slices with a separator.
    #[must_use]
    pub fn join_slices(slices: &[&str], sep: &str) -> Self {
        Self::join(slices, sep)
    }

    /// Joins strings with a separator.
    #[must_use]
    pub fn join<S: AsRef<str>, I: IntoIterator<Item = S>>(slices: I, sep: impl AsRef<str>) -> Self
    where
        I::IntoIter: Clone,
    {
        let sep = sep.as_ref();
        let iter = slices.into_iter();
        let (count, len) = iter
            .clone()
            .fold((0usize, 0usize), |(c, l), s| (c + 1, l + s.as_ref().len()));
        let mut result = Self::with_capacity(len + sep.len() * count.saturating_sub(1));
        for (i, s) in iter.enumerate() {
            if i > 0 {
                result.push_str(sep);
            }
            result.push_str(s.as_ref());
        }
        result
    }
}

impl<'a, R: Repr<'a, u8>> fmt::Display for Hip<Utf8, R> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_inner().fmt(f)
    }
}

impl<'a, R: Repr<'a, u8>> fmt::Write for Hip<Utf8, R> {
    #[inline]
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.push_str(s);
        Ok(())
    }
}

impl<'a, R: Repr<'a, u8>> AsRef<[u8]> for Hip<Utf8, R> {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.bytes()
    }
}

impl<'a, R: Repr<'a, u8>> From<char> for Hip<Utf8, R> {
    #[inline]
    fn from(ch: char) -> Self {
        Self::from_inner(ch.encode_utf8(&mut [0; 4]))
    }
}

impl<'a, R: Repr<'a, u8>> TryFrom<Hip<Bytes, R>> for Hip<Utf8, R> {
    type Error = FromUtf8Error<R>;

    #[inline]
    fn try_from(bytes: Hip<Bytes, R>) -> Result<Self, Self::Error> {
        Self::from_utf8_generic(bytes)
    }
}

impl<'a, R: Repr<'a, u8>> TryFrom<Vec<u8>> for Hip<Utf8, R> {
    type Error = alloc::string::FromUtf8Error;

    #[inline]
    fn try_from(bytes: Vec<u8>) -> Result<Self, Self::Error> {
        String::from_utf8(bytes).map(Self::from)
    }
}

impl<'a, R: Repr<'a, u8>> TryFrom<&[u8]> for Hip<Utf8, R> {
    type Error = Utf8Error;

    #[inline]
    fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
        core::str::from_utf8(bytes).map(Self::from_inner)
    }
}

impl<'a, R: Repr<'a, u8>> From<Hip<Utf8, R>> for Hip<Bytes, R> {
    #[inline]
    fn from(s: Hip<Utf8, R>) -> Self {
        s.into_bytes()
    }
}

impl<'a, R: Repr<'a, u8>> From<Hip<Utf8, R>> for Vec<u8> {
    /// O(1) when the value uniquely owns an adopted buffer.
    #[inline]
    fn from(s: Hip<Utf8, R>) -> Self {
        s.into_owned_std().into_bytes()
    }
}

impl<'a, R: Repr<'a, u8>> core::str::FromStr for Hip<Utf8, R> {
    type Err = core::convert::Infallible;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self::from_inner(s))
    }
}

impl<'a, 'b, R: Repr<'a, u8>> Extend<&'b str> for Hip<Utf8, R> {
    fn extend<I: IntoIterator<Item = &'b str>>(&mut self, iter: I) {
        for s in iter {
            self.push_str(s);
        }
    }
}

impl<'a, R: Repr<'a, u8>> Extend<char> for Hip<Utf8, R> {
    fn extend<I: IntoIterator<Item = char>>(&mut self, iter: I) {
        let iter = iter.into_iter();
        // SAFETY: reserving does not change the content
        unsafe { self.repr_mut() }.reserve(iter.size_hint().0);
        for ch in iter {
            self.push(ch);
        }
    }
}

impl<'a, 'b, R: Repr<'a, u8>> FromIterator<&'b str> for Hip<Utf8, R> {
    fn from_iter<I: IntoIterator<Item = &'b str>>(iter: I) -> Self {
        let mut result = Self::default();
        result.extend(iter);
        result
    }
}

impl<'a, R: Repr<'a, u8>> FromIterator<char> for Hip<Utf8, R> {
    fn from_iter<I: IntoIterator<Item = char>>(iter: I) -> Self {
        let mut result = Self::default();
        result.extend(iter);
        result
    }
}

/// Error of [`Hip::<Utf8, _>::from_utf8`], giving the bytes back.
pub struct FromUtf8Error<R> {
    bytes: Hip<Bytes, R>,
    error: Utf8Error,
}

impl<'a, R: Repr<'a, u8>> FromUtf8Error<R> {
    /// The bytes that failed to convert.
    #[inline]
    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        self.bytes.as_inner()
    }

    /// Returns the bytes back.
    #[inline]
    #[must_use]
    pub fn into_bytes(self) -> Hip<Bytes, R> {
        self.bytes
    }

    /// The underlying UTF-8 error.
    #[inline]
    #[must_use]
    pub const fn utf8_error(&self) -> Utf8Error {
        self.error
    }
}

impl<'a, R: Repr<'a, u8>> fmt::Debug for FromUtf8Error<R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("FromUtf8Error")
            .field("bytes", &self.bytes)
            .field("error", &self.error)
            .finish()
    }
}

impl<R> fmt::Display for FromUtf8Error<R> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.error.fmt(f)
    }
}

impl<'a, R: Repr<'a, u8>> core::error::Error for FromUtf8Error<R> {}
