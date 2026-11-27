//! The editing part of `String`'s API for the string family
//! ([`HipStr`](crate::HipStr), [`SmallStr`](crate::SmallStr),
//! [`TinyStr`](crate::TinyStr)).
//!
//! Mutating methods copy borrowed or shared values first (copy-on-write);
//! `retain` keeps them as they are when every character is kept.

use alloc::boxed::Box;
use alloc::string::{FromUtf16Error, String};
use alloc::vec::Vec;
use core::fmt;
use core::iter::FusedIterator;
use core::marker::PhantomData;
use core::ops::{Range, RangeBounds};

use crate::enc::Utf8;
use crate::hip::Hip;
use crate::repr::Repr;
use crate::slice::range_or_panic;

impl<'a, R: Repr<'a, u8>> Hip<Utf8, R> {
    /// Decodes UTF-16 little-endian bytes (see `String::from_utf16le`).
    ///
    /// # Errors
    ///
    /// Returns an error if the bytes are not valid UTF-16 or have an odd length.
    #[inline]
    pub fn from_utf16le(v: &[u8]) -> Result<Self, FromUtf16Error> {
        String::from_utf16le(v).map(Self::from)
    }

    /// Decodes UTF-16 little-endian bytes, replacing invalid data with
    /// `U+FFFD` (see `String::from_utf16le_lossy`).
    #[inline]
    #[must_use]
    pub fn from_utf16le_lossy(v: &[u8]) -> Self {
        Self::from(String::from_utf16le_lossy(v))
    }

    /// Decodes UTF-16 big-endian bytes (see `String::from_utf16be`).
    ///
    /// # Errors
    ///
    /// Returns an error if the bytes are not valid UTF-16 or have an odd length.
    #[inline]
    pub fn from_utf16be(v: &[u8]) -> Result<Self, FromUtf16Error> {
        String::from_utf16be(v).map(Self::from)
    }

    /// Decodes UTF-16 big-endian bytes, replacing invalid data with
    /// `U+FFFD` (see `String::from_utf16be_lossy`).
    #[inline]
    #[must_use]
    pub fn from_utf16be_lossy(v: &[u8]) -> Self {
        Self::from(String::from_utf16be_lossy(v))
    }

    /// Converts a vector of bytes to a string, replacing invalid UTF-8 with
    /// `U+FFFD`, and reusing the buffer when valid (see
    /// `String::from_utf8_lossy_owned`).
    #[inline]
    #[must_use]
    pub fn from_utf8_lossy_owned(v: Vec<u8>) -> Self {
        Self::from(String::from_utf8_lossy_owned(v))
    }

    #[track_caller]
    fn assert_boundary(&self, index: usize, what: &str) {
        assert!(
            self.as_inner().is_char_boundary(index),
            "{what} index {index} is not a char boundary"
        );
    }

    #[track_caller]
    fn char_range(&self, range: impl RangeBounds<usize>) -> Range<usize> {
        let range = range_or_panic(range, self.bytes().len());
        self.assert_boundary(range.start, "start");
        self.assert_boundary(range.end, "end");
        range
    }

    /// # Safety
    ///
    /// `range` must lie on char boundaries.
    #[inline]
    unsafe fn replace_bytes(&mut self, range: Range<usize>, with: &str) {
        // SAFETY: cut at char boundaries, filled with UTF-8 (precondition)
        unsafe { self.splice_bytes(range, with.as_bytes()) }
    }

    /// Inserts a character at byte index `idx`.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is out of bounds or not on a char boundary.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let mut s = HipStr::from("ac");
    /// s.insert(1, 'b');
    /// assert_eq!(s, "abc");
    /// ```
    #[track_caller]
    pub fn insert(&mut self, idx: usize, ch: char) {
        self.insert_str(idx, ch.encode_utf8(&mut [0; 4]));
    }

    /// Inserts a string slice at byte index `idx`.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is out of bounds or not on a char boundary.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let mut s = HipStr::from("held");
    /// s.insert_str(2, "llo wor");
    /// assert_eq!(s, "hello world");
    /// ```
    #[track_caller]
    pub fn insert_str(&mut self, idx: usize, string: &str) {
        let range = self.char_range(idx..idx);
        // SAFETY: checked boundary
        unsafe { self.replace_bytes(range, string) };
    }

    /// Removes and returns the character at byte index `idx`.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is not on a char boundary or not before the end.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let mut s = HipStr::from("été");
    /// assert_eq!(s.remove(0), 'é');
    /// assert_eq!(s, "té");
    /// ```
    #[track_caller]
    pub fn remove(&mut self, idx: usize) -> char {
        let Some(ch) = self.as_inner()[idx..].chars().next() else {
            panic!("cannot remove a char from the end of a string");
        };
        // SAFETY: a whole character
        unsafe { self.replace_bytes(idx..idx + ch.len_utf8(), "") };
        ch
    }

    /// Replaces the bytes in `range` by `replace_with`.
    ///
    /// # Panics
    ///
    /// Panics if the range is out of bounds or not on char boundaries.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let mut s = HipStr::from("α is alpha");
    /// let end = s.find(' ').unwrap();
    /// s.replace_range(..end, "Α");
    /// assert_eq!(s, "Α is alpha");
    /// ```
    #[track_caller]
    pub fn replace_range(&mut self, range: impl RangeBounds<usize>, replace_with: &str) {
        let range = self.char_range(range);
        // SAFETY: checked boundaries
        unsafe { self.replace_bytes(range, replace_with) };
    }

    /// Keeps the characters for which `f` returns `true`, in order.
    ///
    /// Borrowed and shared values are not copied when every character is
    /// kept.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let mut s = HipStr::from("f_o_ob_ar");
    /// s.retain(|c| c != '_');
    /// assert_eq!(s, "foobar");
    /// ```
    pub fn retain(&mut self, mut f: impl FnMut(char) -> bool) {
        struct Guard<'g, 'a, R: Repr<'a, u8>> {
            hip: &'g mut Hip<Utf8, R>,
            read: usize,
            write: usize,
            len: usize,
            borrow: PhantomData<&'a ()>,
        }
        impl<'a, R: Repr<'a, u8>> Drop for Guard<'_, 'a, R> {
            fn drop(&mut self) {
                // SAFETY: `[0, write)` holds whole kept characters and
                // `[read, len)` the unvisited ones: moving them together
                // restores valid UTF-8
                unsafe {
                    let bytes = self.hip.bytes_mut();
                    bytes.copy_within(self.read..self.len, self.write);
                    self.hip.truncate_bytes(self.len - (self.read - self.write));
                }
            }
        }

        // first rejected character, without touching the storage
        let Some((first, ch)) = self.as_inner().char_indices().find(|&(_, c)| !f(c)) else {
            return;
        };
        let len = self.bytes().len();
        let mut g = Guard {
            hip: self,
            read: first + ch.len_utf8(),
            write: first,
            len,
            borrow: PhantomData,
        };
        while g.read < len {
            // SAFETY: the guard restores the invariant, even on panic
            let bytes = unsafe { g.hip.bytes_mut() };
            // SAFETY: `read` is at a char boundary of the original string
            let ch = unsafe { core::str::from_utf8_unchecked(&bytes[g.read..]) }
                .chars()
                .next()
                .unwrap();
            let n = ch.len_utf8();
            let keep = f(ch);
            if keep {
                bytes.copy_within(g.read..g.read + n, g.write);
                g.write += n;
            }
            g.read += n;
        }
    }

    /// Splits in two at byte index `at`: `self` keeps `[0, at)` and the rest
    /// is returned.
    ///
    /// # Panics
    ///
    /// Panics if `at` is out of bounds or not on a char boundary.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let mut hello = HipStr::from("Hello, World!");
    /// let world = hello.split_off(7);
    /// assert_eq!(hello, "Hello, ");
    /// assert_eq!(world, "World!");
    /// ```
    #[track_caller]
    #[must_use = "use `.truncate()` if you don't need the other half"]
    pub fn split_off(&mut self, at: usize) -> Self {
        let range = self.char_range(at..);
        let tail = Self::from(&self.as_inner()[range]);
        // SAFETY: checked boundary
        unsafe { self.truncate_bytes(at) };
        tail
    }

    /// Appends a copy of the bytes in `src`.
    ///
    /// # Panics
    ///
    /// Panics if the range is out of bounds or not on char boundaries.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let mut s = HipStr::from("abcde");
    /// s.extend_from_within(2..);
    /// assert_eq!(s, "abcdecde");
    /// ```
    #[track_caller]
    pub fn extend_from_within(&mut self, src: impl RangeBounds<usize>) {
        let src = self.char_range(src);
        let len = self.bytes().len();
        // SAFETY: the zeroes (valid UTF-8) are overwritten by whole characters
        unsafe {
            self.repr_mut().resize(len + src.len(), 0);
            self.bytes_mut().copy_within(src, len);
        }
    }

    /// Removes the characters in the byte `range`, returning them as an
    /// iterator.
    ///
    /// The characters are removed when the iterator is dropped, even if it is
    /// not fully consumed. If it is leaked, the string is left unchanged.
    ///
    /// # Panics
    ///
    /// Panics if the range is out of bounds or not on char boundaries.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let mut s = HipStr::from("α is alpha, β is beta");
    /// let beta_offset = s.find('β').unwrap();
    /// let t: String = s.drain(..beta_offset).collect();
    /// assert_eq!(t, "α is alpha, ");
    /// assert_eq!(s, "β is beta");
    /// ```
    #[track_caller]
    pub fn drain(&mut self, range: impl RangeBounds<usize>) -> Drain<'_, 'a, R> {
        let range = self.char_range(range);
        Drain {
            front: range.start,
            back: range.end,
            range,
            hip: self,
            borrow: PhantomData,
        }
    }

    /// Converts into a boxed string slice.
    #[must_use]
    pub fn into_boxed_str(self) -> Box<str> {
        self.into_string().into_boxed_str()
    }

    /// Leaks the string, returning a mutable reference to it (see
    /// `String::leak`).
    #[must_use]
    pub fn leak<'b>(self) -> &'b mut str {
        self.into_string().leak()
    }
}

/// Draining iterator returned by [`Hip::drain`] on strings.
pub struct Drain<'h, 'a, R: Repr<'a, u8>> {
    hip: &'h mut Hip<Utf8, R>,
    range: Range<usize>,
    front: usize,
    back: usize,
    borrow: PhantomData<&'a ()>,
}

impl<'a, R: Repr<'a, u8>> Drain<'_, 'a, R> {
    /// The characters not yet yielded.
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.hip.as_inner()[self.front..self.back]
    }
}

impl<'a, R: Repr<'a, u8>> AsRef<str> for Drain<'_, 'a, R> {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl<'a, R: Repr<'a, u8>> AsRef<[u8]> for Drain<'_, 'a, R> {
    fn as_ref(&self) -> &[u8] {
        self.as_str().as_bytes()
    }
}

impl<'a, R: Repr<'a, u8>> fmt::Debug for Drain<'_, 'a, R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Drain").field(&self.as_str()).finish()
    }
}

impl<'a, R: Repr<'a, u8>> Iterator for Drain<'_, 'a, R> {
    type Item = char;

    #[inline]
    fn next(&mut self) -> Option<char> {
        let ch = self.as_str().chars().next()?;
        self.front += ch.len_utf8();
        Some(ch)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.as_str().chars().size_hint()
    }

    #[inline]
    fn last(mut self) -> Option<char> {
        self.next_back()
    }
}

impl<'a, R: Repr<'a, u8>> DoubleEndedIterator for Drain<'_, 'a, R> {
    #[inline]
    fn next_back(&mut self) -> Option<char> {
        let ch = self.as_str().chars().next_back()?;
        self.back -= ch.len_utf8();
        Some(ch)
    }
}

impl<'a, R: Repr<'a, u8>> FusedIterator for Drain<'_, 'a, R> {}

impl<'a, R: Repr<'a, u8>> Drop for Drain<'_, 'a, R> {
    fn drop(&mut self) {
        let range = core::mem::replace(&mut self.range, 0..0);
        // SAFETY: checked boundaries at creation
        unsafe { self.hip.replace_bytes(range, "") };
    }
}
