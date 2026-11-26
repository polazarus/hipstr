//! UTF-8 strings: [`HipStr`], [`SmallStr`], [`TinyStr`].

use alloc::borrow::Cow;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;
use core::str::Utf8Error;

use super::enc::{Bytes, Utf8};
use super::family::{impl_borrowed_ctors, impl_cmp, impl_std_glue};
use super::hip::Hip;
use super::repr::Repr;
pub use crate::hip::RefMut;
pub use crate::pattern::{DoubleEndedPattern, IterWrapper, Pattern, ReversePattern};
pub use crate::slice::{SliceError, SliceErrorKind};

/// `serde` helpers.
#[cfg(feature = "serde")]
pub mod serde {
    pub use crate::serde_impl::string::borrow_deserialize;

    #[cfg(test)]
    mod tests;
}

#[cfg(all(feature = "borsh", test))]
mod borsh {
    use borsh::io::ErrorKind;
    use borsh::{BorshDeserialize, BorshSerialize};

    mod tests;
}

#[cfg(test)]
mod tests;

super::generic_aliases!(Utf8, HipStr, SmallStr, TinyStr, "string");

impl_std_glue!(Utf8, str, String);
impl_borrowed_ctors!(Utf8, str, |value| value.as_bytes());

impl_cmp!(Utf8 as str;
    [] str, [] &str, [] String, [] &String, [] alloc::boxed::Box<str>, [] &alloc::boxed::Box<str>,
    [] Cow<'_, str>, [] &Cow<'_, str>,
);
#[cfg(feature = "std")]
impl_cmp!(Utf8 as std::ffi::OsStr;
    [] std::ffi::OsStr, [] &std::ffi::OsStr, [] std::ffi::OsString, [] &std::ffi::OsString,
);

#[cfg(feature = "std")]
impl<'a, R: Repr<'a, u8>> AsRef<std::ffi::OsStr> for Hip<Utf8, R> {
    #[inline]
    fn as_ref(&self) -> &std::ffi::OsStr {
        std::ffi::OsStr::new(self.as_inner())
    }
}

#[cfg(feature = "std")]
impl<'a, R: Repr<'a, u8>> AsRef<std::path::Path> for Hip<Utf8, R> {
    #[inline]
    fn as_ref(&self) -> &std::path::Path {
        std::path::Path::new(self.as_inner())
    }
}

#[cfg(feature = "std")]
impl<'a, R: Repr<'a, u8>> From<Hip<Utf8, R>> for std::ffi::OsString {
    /// O(1) when the value uniquely owns an adopted buffer.
    #[inline]
    fn from(value: Hip<Utf8, R>) -> Self {
        value.into_owned_std().into()
    }
}

#[cfg(feature = "std")]
impl<'a, R: Repr<'a, u8>> std::net::ToSocketAddrs for Hip<Utf8, R> {
    type Iter = std::vec::IntoIter<std::net::SocketAddr>;

    #[inline]
    fn to_socket_addrs(&self) -> std::io::Result<Self::Iter> {
        self.as_inner().to_socket_addrs()
    }
}

impl<'a, R: Repr<'a, u8>> TryFrom<&Hip<Bytes, R>> for Hip<Utf8, R> {
    type Error = FromUtf8Error<R>;

    /// Shares the storage of `bytes` (no copy).
    #[inline]
    fn try_from(bytes: &Hip<Bytes, R>) -> Result<Self, Self::Error> {
        Self::from_utf8_generic(bytes.clone())
    }
}
super::hip::impl_const_typed_accessors!(Utf8, str, |b| core::str::from_utf8_unchecked(b), |v| v
    .as_bytes());

/// `const` string accessors and UTF-8 conversions, per representation.
macro_rules! impl_const_str {
    ($([$($lt:lifetime)?] $repr:ty),* $(,)?) => {$(
        impl<$($lt,)? B: super::backend::Backend> Hip<Utf8, $repr> {
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
                self.as_typed()
            }

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
            #[inline]
            #[must_use]
            pub const fn as_bytes(&self) -> &[u8] {
                self.repr().as_slice()
            }

            /// Converts a `HipByt` (a sequence of bytes) to a `HipStr`.
            ///
            /// Both `HipByt` and `HipStr` are made of bytes, so this function
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
            pub const fn from_utf8(bytes: Hip<Bytes, $repr>) -> Result<Self, FromUtf8Error<$repr>> {
                match core::str::from_utf8(bytes.repr().as_slice()) {
                    // SAFETY: checked
                    Ok(_) => Ok(unsafe { Self::from_utf8_unchecked(bytes) }),
                    Err(error) => Err(FromUtf8Error { bytes, error }),
                }
            }

            /// Converts a `HipByt` to a `HipStr` without checking that the
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

    /// Converts a `HipStr` into a `HipByt`.
    ///
    /// It consumes the `HipStr` without copying the content
    /// (if shared or static).
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
    pub fn to_mut_str(&mut self) -> &mut str {
        // SAFETY: `str`'s safe API preserves UTF-8
        let bytes = unsafe { self.repr_mut() }.to_mut_slice();
        // SAFETY: type invariant
        unsafe { core::str::from_utf8_unchecked_mut(bytes) }
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
        // SAFETY: concatenation of UTF-8 is UTF-8
        unsafe { self.push_bytes(addition.as_bytes()) }
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
        self.push_str(ch.encode_utf8(&mut [0; 4]));
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
    pub fn pop(&mut self) -> Option<char> {
        let ch = self.as_inner().chars().next_back()?;
        // SAFETY: cut at a character boundary
        unsafe { self.truncate_bytes(self.bytes().len() - ch.len_utf8()) };
        Some(ch)
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

    /// Converts a `HipByt` to a `HipStr`, including invalid characters.
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
    #[must_use]
    pub fn from_utf8_lossy(bytes: Hip<Bytes, R>) -> Self {
        match String::from_utf8_lossy(bytes.as_inner()) {
            // SAFETY: valid UTF-8, as `Borrowed` is only returned when valid
            Cow::Borrowed(_) => unsafe { Self::from_repr(bytes.into_repr()) },
            Cow::Owned(s) => Self::from(s),
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
    pub fn from_utf16(v: &[u16]) -> Result<Self, alloc::string::FromUtf16Error> {
        String::from_utf16(v).map(Self::from)
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
    #[must_use]
    pub fn from_utf16_lossy(v: &[u16]) -> Self {
        Self::from(String::from_utf16_lossy(v))
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
    #[must_use]
    pub fn repeat(&self, n: usize) -> Self {
        match n {
            0 => return Self::default(),
            1 => return self.clone(),
            _ => {}
        }
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
    #[must_use]
    pub fn to_ascii_lowercase(&self) -> Self {
        let mut result = self.clone();
        result.make_ascii_lowercase();
        result
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
    #[must_use]
    pub fn to_ascii_uppercase(&self) -> Self {
        let mut result = self.clone();
        result.make_ascii_uppercase();
        result
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
    pub fn make_ascii_lowercase(&mut self) {
        if self.as_inner().bytes().any(|b| b.is_ascii_uppercase()) {
            self.to_mut_str().make_ascii_lowercase();
        }
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
    pub fn make_ascii_uppercase(&mut self) {
        if self.as_inner().bytes().any(|b| b.is_ascii_lowercase()) {
            self.to_mut_str().make_ascii_uppercase();
        }
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
    #[must_use]
    pub fn to_lowercase(&self) -> Self {
        Self::from(self.as_inner().to_lowercase())
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
    #[must_use]
    pub fn to_uppercase(&self) -> Self {
        Self::from(self.as_inner().to_uppercase())
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
    #[must_use]
    pub fn concat_slices(slices: &[&str]) -> Self {
        Self::concat(slices)
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
        assert_eq!(result.bytes().len(), len, "inconsistent iterator");
        result
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
    #[must_use]
    pub fn join_slices(slices: &[&str], sep: &str) -> Self {
        Self::join(slices, sep)
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
        let expected = len + sep.len() * count.saturating_sub(1);
        let mut result = Self::with_capacity(expected);
        for (i, s) in iter.enumerate() {
            if i > 0 {
                result.push_str(sep);
            }
            result.push_str(s.as_ref());
        }
        assert_eq!(result.bytes().len(), expected, "inconsistent iterator");
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
    #[inline]
    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        self.bytes.as_inner()
    }

    /// Converts a `HipStr` into a `HipByt`.
    ///
    /// It consumes the `HipStr` without copying the content
    /// (if shared or static).
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
    #[inline]
    #[must_use]
    pub fn into_bytes(self) -> Hip<Bytes, R> {
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

impl<'a, R: Repr<'a, u8>> Clone for FromUtf8Error<R> {
    fn clone(&self) -> Self {
        Self {
            bytes: self.bytes.clone(),
            error: self.error,
        }
    }
}

impl<'a, R: Repr<'a, u8>> PartialEq for FromUtf8Error<R> {
    fn eq(&self, other: &Self) -> bool {
        self.bytes == other.bytes && self.error == other.error
    }
}

impl<'a, R: Repr<'a, u8>> Eq for FromUtf8Error<R> {}

impl<R> fmt::Display for FromUtf8Error<R> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.error.fmt(f)
    }
}

impl<'a, R: Repr<'a, u8>> core::error::Error for FromUtf8Error<R> {}
