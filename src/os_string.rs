//! Platform strings: [`HipOsStr`], [`SmallOsStr`], [`TinyOsStr`].

use alloc::borrow::Cow;
use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;
use std::ffi::{OsStr, OsString};
use std::path::Path;

use super::enc::{self, Bytes, Utf8};
use super::family::impl_std_glue;
use super::hip::Hip;
use super::repr::Repr;
pub use crate::hip::RefMut;

#[cfg(test)]
mod tests;

/// WTF-8 (the encoding of Windows OS strings) helpers; compiled for tests on
/// every platform.
#[cfg(any(windows, test))]
mod wtf8 {
    /// The surrogate encoded by the 3 bytes `b` (`ED A0..BF 80..BF`), if any.
    fn surrogate(b: &[u8; 3]) -> Option<u32> {
        match *b {
            [0xED, b1 @ 0xA0..=0xBF, b2 @ 0x80..=0xBF] => {
                Some(0xD000 | u32::from(b1 & 0x3F) << 6 | u32::from(b2 & 0x3F))
            }
            _ => None,
        }
    }

    /// If `head` ends with a lone high surrogate and `tail` starts with a
    /// lone low one, the 4-byte UTF-8 encoding of the code point they form
    /// (to replace those 6 bytes).
    #[allow(
        clippy::cast_possible_truncation,
        reason = "each value is masked to fit its byte (cp < 0x110000)"
    )]
    pub fn join_surrogates(head: &[u8], tail: &[u8]) -> Option<[u8; 4]> {
        let hi = surrogate(head.last_chunk()?)?;
        let lo = surrogate(tail.first_chunk()?)?;
        if !(0xD800..0xDC00).contains(&hi) || !(0xDC00..0xE000).contains(&lo) {
            return None;
        }
        let cp = 0x10000 + ((hi - 0xD800) << 10) + (lo - 0xDC00);
        Some([
            0xF0 | (cp >> 18) as u8,
            0x80 | (cp >> 12 & 0x3F) as u8,
            0x80 | (cp >> 6 & 0x3F) as u8,
            0x80 | (cp & 0x3F) as u8,
        ])
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        // U+1F600 = D83D DE00
        const HI: [u8; 3] = [0xED, 0xA0, 0xBD];
        const LO: [u8; 3] = [0xED, 0xB8, 0x80];

        #[test]
        fn joins_a_split_pair() {
            let joined =
                join_surrogates(&[b'a', HI[0], HI[1], HI[2]], &[LO[0], LO[1], LO[2], b'b']);
            assert_eq!(joined, Some(*"\u{1F600}".as_bytes().first_chunk().unwrap()));
        }

        #[test]
        fn leaves_the_rest() {
            assert_eq!(join_surrogates(&HI, b"x"), None, "lone high");
            assert_eq!(join_surrogates(b"x", &LO), None, "lone low");
            assert_eq!(join_surrogates(&LO, &HI), None, "reversed");
            assert_eq!(join_surrogates(&HI, &HI), None, "two highs");
            assert_eq!(join_surrogates(&LO, &LO), None, "two lows");
            // U+D7FF (ED 9F BF) is not a surrogate
            assert_eq!(join_surrogates(&[0xED, 0x9F, 0xBF], &LO), None);
            assert_eq!(join_surrogates(&HI, &[0xED, 0xB8]), None, "short tail");
            assert_eq!(join_surrogates(&HI, b"xyz"), None, "not a surrogate");
            assert_eq!(join_surrogates(&[0xA0, 0xBD], &LO), None, "short head");
            assert_eq!(join_surrogates(b"", b""), None);
            // a well-formed 4-byte code point is not split
            assert_eq!(join_surrogates("\u{1F600}".as_bytes(), &LO), None);
        }
    }
}

super::generic_aliases!(
    enc::OsStr,
    HipOsStr,
    SmallOsStr,
    TinyOsStr,
    "platform string"
);

impl_std_glue!(enc::OsStr, OsStr, OsString);

/// `const` accessors, per representation (`as_os_str` cannot be `const`:
/// std's conversions from bytes are not, and `OsStr`'s layout is not
/// guaranteed).
macro_rules! impl_const_os_str {
    ($(#[$m:meta] [$($lt:lifetime)?] $repr:ty),* $(,)?) => {$(
        #[$m]
        impl<$($lt,)? B: super::backend::Backend> Hip<enc::OsStr, $repr> {
            /// The encoded bytes (see [`OsStr::as_encoded_bytes`]).
            #[inline]
            #[must_use]
            pub const fn as_encoded_bytes(&self) -> &[u8] {
                self.repr().as_slice()
            }
        }
    )*};
}

crate::repr::for_each_repr!(impl_const_os_str);

impl<'a, R: Repr<'a>> AsRef<Path> for Hip<enc::OsStr, R> {
    #[inline]
    fn as_ref(&self) -> &Path {
        Path::new(self.as_inner())
    }
}

impl<'a, R: Repr<'a>> From<String> for Hip<enc::OsStr, R> {
    /// Adopts the buffer when it does not fit inline (no copy).
    #[inline]
    fn from(value: String) -> Self {
        Self::from_owned(value.into())
    }
}

impl<'a, R: Repr<'a>> From<Box<str>> for Hip<enc::OsStr, R> {
    #[inline]
    fn from(value: Box<str>) -> Self {
        Self::from(String::from(value))
    }
}

impl<'a, R: Repr<'a>> From<Cow<'a, str>> for Hip<enc::OsStr, R> {
    /// Borrows `Cow::Borrowed` (copies if the representation cannot borrow).
    #[inline]
    fn from(value: Cow<'a, str>) -> Self {
        match value {
            Cow::Borrowed(s) => Self::from_inner_borrowed(OsStr::new(s)),
            Cow::Owned(s) => Self::from(s),
        }
    }
}

impl<'a, R: Repr<'a>> From<Hip<enc::OsStr, R>> for Vec<u8> {
    /// The encoded bytes, O(1) when the value uniquely owns an adopted buffer.
    #[inline]
    fn from(value: Hip<enc::OsStr, R>) -> Self {
        value.into_os_string().into_encoded_bytes()
    }
}

impl<'a, R: Repr<'a>> Hip<enc::OsStr, R> {
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
        let addition = addition.as_ref().as_encoded_bytes();
        // WTF-8 (Windows): a lone high surrogate at the end and a lone low
        // one at the start join into one code point, as `OsString::push` does
        #[cfg(windows)]
        if let Some(joined) = wtf8::join_surrogates(self.as_encoded_bytes(), addition) {
            let len = self.as_encoded_bytes().len();
            // SAFETY: the 3-byte surrogates at the junction replaced by the
            // 4-byte encoding of their code point: well-formed WTF-8
            unsafe {
                self.truncate_bytes(len - 3);
                self.push_bytes(&joined);
                self.push_bytes(&addition[3..]);
            }
            return;
        }
        // SAFETY: on Unix-like platforms any bytes; on Windows, no surrogate
        // pair split at the junction
        unsafe { self.push_bytes(addition) }
    }

    /// Converts encoded bytes into an OS string, adopting the buffer (see
    /// `OsString::from_encoded_bytes_unchecked`).
    ///
    /// # Safety
    ///
    /// Same as `OsString::from_encoded_bytes_unchecked`: the bytes must come
    /// from `as_encoded_bytes` / `into_encoded_bytes` of OS strings on the
    /// same platform and Rust version, possibly concatenated or split at
    /// valid boundaries.
    #[inline]
    #[must_use]
    pub unsafe fn from_encoded_bytes_unchecked(bytes: Vec<u8>) -> Self {
        // SAFETY: precondition
        Self::from_owned(unsafe { OsString::from_encoded_bytes_unchecked(bytes) })
    }

    /// Converts into its encoded bytes (see `OsString::into_encoded_bytes`).
    ///
    /// For a conversion keeping the storage, see [`into_bytes`](Self::into_bytes).
    #[inline]
    #[must_use]
    pub fn into_encoded_bytes(self) -> Vec<u8> {
        self.into_os_string().into_encoded_bytes()
    }

    /// Converts into a `String` if valid UTF-8 (see `OsString::into_string`).
    ///
    /// For a conversion keeping the storage, see [`into_str`](Self::into_str).
    ///
    /// # Errors
    ///
    /// Returns the value unchanged if it is not valid UTF-8.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipOsStr;
    /// assert_eq!(HipOsStr::from("abc").into_string().unwrap(), "abc");
    /// ```
    pub fn into_string(self) -> Result<String, Self> {
        if self.to_str().is_some() {
            Ok(self.into_os_string().into_string().unwrap_or_default())
        } else {
            Err(self)
        }
    }

    /// Converts into a boxed OS string.
    #[inline]
    #[must_use]
    pub fn into_boxed_os_str(self) -> Box<OsStr> {
        self.into_os_string().into_boxed_os_str()
    }

    /// Leaks the OS string, returning a mutable reference to it (see
    /// `OsString::leak`).
    #[inline]
    #[must_use]
    pub fn leak<'b>(self) -> &'b mut OsStr {
        self.into_os_string().leak()
    }

    /// Converts ASCII letters to lowercase in place (see
    /// `OsStr::make_ascii_lowercase`), copying a borrowed or shared value
    /// first.
    #[inline]
    pub fn make_ascii_lowercase(&mut self) {
        // SAFETY: ASCII bytes stand alone in the platform encoding (as in
        // std's own implementation): changing their case keeps it valid
        unsafe { self.bytes_mut() }.make_ascii_lowercase();
    }

    /// Converts ASCII letters to uppercase in place (see
    /// `OsStr::make_ascii_uppercase`), copying a borrowed or shared value
    /// first.
    #[inline]
    pub fn make_ascii_uppercase(&mut self) {
        // SAFETY: see `make_ascii_lowercase`
        unsafe { self.bytes_mut() }.make_ascii_uppercase();
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
            // SAFETY: valid UTF-8
            Cow::Owned(s) => unsafe { Hip::from_repr(R::from_vec(s.into_bytes())) },
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

impl<'a, R: Repr<'a>> From<&str> for Hip<enc::OsStr, R> {
    #[inline]
    fn from(value: &str) -> Self {
        Self::from_inner(OsStr::new(value))
    }
}

#[cfg(feature = "hip")]
impl<'a, B: super::backend::Backend> Hip<enc::OsStr, super::repr::Wide<'a, B>> {
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

#[cfg(feature = "small")]
impl<'a, B: super::backend::Backend> Hip<enc::OsStr, super::repr::Small<'a, B>> {
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
