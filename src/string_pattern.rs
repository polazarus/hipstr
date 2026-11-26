//! Pattern-based methods of [`HipStr`], returning slices that share the
//! storage (O(1)). Only the 3-word representation can slice.

use core::str::{Lines, SplitAsciiWhitespace, SplitWhitespace};

use super::backend::Backend;
use super::pattern::{DoubleEndedPattern, IterWrapper, Pattern, ReversePattern};
use super::string::HipStr;

impl<'a, B: Backend> HipStr<'a, B> {
    /// Returns a string with leading and trailing whitespace removed.
    ///
    /// 'Whitespace' is defined according to the terms of the Unicode Derived
    /// Core Property `White_Space`, which includes newlines.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let s = HipStr::from("\n Hello\tworld\t\n");
    ///
    /// assert_eq!("Hello\tworld", s.trim());
    /// ```
    #[inline]
    #[must_use]
    pub fn trim(&self) -> Self {
        let s = self.as_str().trim();
        unsafe { self.slice_ref_unchecked(s) }
    }

    /// Returns a string with leading whitespace removed.
    ///
    /// 'Whitespace' is defined according to the terms of the Unicode Derived
    /// Core Property `White_Space`, which includes newlines.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let s = HipStr::from("\n Hello\tworld\t\n");
    ///
    /// assert_eq!("Hello\tworld\t\n", s.trim_start());
    /// ```
    #[inline]
    #[must_use]
    pub fn trim_start(&self) -> Self {
        let s = self.as_str().trim_start();
        unsafe { self.slice_ref_unchecked(s) }
    }

    /// Returns a string with trailing whitespace removed.
    ///
    /// 'Whitespace' is defined according to the terms of the Unicode Derived
    /// Core Property `White_Space`, which includes newlines.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let s = HipStr::from("\n Hello\tworld\t\n");
    ///
    /// assert_eq!("\n Hello\tworld", s.trim_end());
    /// ```
    #[inline]
    #[must_use]
    pub fn trim_end(&self) -> Self {
        let s = self.as_str().trim_end();
        unsafe { self.slice_ref_unchecked(s) }
    }

    /// An iterator over substrings of this string, separated by
    /// characters matched by a pattern.
    ///
    /// Works like [`str::split`], but yields `HipStr`s rather than string slices.
    ///
    /// See [`str::split`], for examples and possible patterns.
    #[inline]
    pub fn split<P: Pattern>(&self, pattern: P) -> IterWrapper<'_, 'a, B, P::Split<'_>> {
        IterWrapper::new(self, pattern.split(self.as_str()))
    }

    /// An iterator over substrings of this string, separated by
    /// characters matched by a pattern. Differs from the iterator produced by
    /// `split` in that `split_inclusive` leaves the matched part as the
    /// terminator of the substring.
    ///
    /// Works like [`str::split_inclusive`], but yields `HipStr`s rather than string slices.
    ///
    /// See [`str::split_inclusive`], for examples and possible patterns.
    #[inline]
    pub fn split_inclusive<P: Pattern>(
        &self,
        pattern: P,
    ) -> IterWrapper<'_, 'a, B, P::SplitInclusive<'_>> {
        IterWrapper::new(self, pattern.split_inclusive(self.as_str()))
    }

    /// An iterator over substrings of this string, separated by
    /// characters matched by a pattern and yielded in reverse order.
    ///
    /// Works like [`str::rsplit`], but yields `HipStr`s rather than string slices.
    ///
    /// See [`str::rsplit`], for examples and possible patterns.
    #[inline]
    pub fn rsplit<P: ReversePattern>(&self, pattern: P) -> IterWrapper<'_, 'a, B, P::RSplit<'_>> {
        IterWrapper::new(self, pattern.rsplit(self.as_str()))
    }

    /// An iterator over substrings of this string, separated by
    /// characters matched by a pattern.
    ///
    /// Equivalent to [`split`](Self::split), except that the trailing substring
    /// is skipped if empty.
    ///
    /// This method can be used for string data that is _terminated_,
    /// rather than _separated_ by a pattern.
    ///
    /// Works like [`str::split_terminator`], but yields `HipStr`s rather than string slices.
    ///
    /// See [`str::split_terminator`], for examples and possible patterns.
    #[inline]
    pub fn split_terminator<P: Pattern>(
        &self,
        pattern: P,
    ) -> IterWrapper<'_, 'a, B, P::SplitTerminator<'_>> {
        IterWrapper::new(self, pattern.split_terminator(self.as_str()))
    }

    /// An iterator over substrings of this string, separated by
    /// characters matched by a pattern and yielded in reverse order.
    ///
    /// Equivalent to [`rsplit`](Self::rsplit), except that the trailing
    /// substring is skipped if empty.
    ///
    /// This method can be used for string data that is _terminated_,
    /// rather than _separated_ by a pattern.
    ///
    /// Works like [`str::rsplit_terminator`], but yields `HipStr`s rather than string slices.
    ///
    /// See [`str::rsplit_terminator`], for examples and possible patterns.
    #[inline]
    pub fn rsplit_terminator<P: ReversePattern>(
        &self,
        pattern: P,
    ) -> IterWrapper<'_, 'a, B, P::RSplitTerminator<'_>> {
        IterWrapper::new(self, pattern.rsplit_terminator(self.as_str()))
    }

    /// An iterator over substrings of this string, separated by a
    /// pattern, restricted to returning at most `n` items.
    ///
    /// If `n` substrings are returned, the last substring (the `n`th substring)
    /// will contain the remainder of the string.
    ///
    /// Works like [`str::splitn`], but yields `HipStr`s rather than string slices.
    ///
    /// See [`str::splitn`], for examples and possible patterns.
    #[inline]
    pub fn splitn<P: Pattern>(
        &self,
        n: usize,
        pattern: P,
    ) -> IterWrapper<'_, 'a, B, P::SplitN<'_>> {
        IterWrapper::new(self, pattern.splitn(n, self.as_str()))
    }

    /// An iterator over substrings of this string, separated by a
    /// pattern, starting from the end of the string, restricted to returning
    /// at most `n` items.
    ///
    /// If `n` substrings are returned, the last substring (the `n`th substring)
    /// will contain the remainder of the string.
    ///
    /// Works like [`str::rsplitn`], but yields `HipStr`s rather than string slices.
    ///
    /// See [`str::rsplitn`], for examples and possible patterns.
    #[inline]
    pub fn rsplitn<P: ReversePattern>(
        &self,
        n: usize,
        pattern: P,
    ) -> IterWrapper<'_, 'a, B, P::RSplitN<'_>> {
        IterWrapper::new(self, pattern.rsplitn(n, self.as_str()))
    }

    /// Splits the string on the first occurrence of the specified delimiter and
    /// returns prefix before delimiter and suffix after delimiter.
    ///
    /// Works like [`str::split_once`], but returns `HipStr`s rather than string slices.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// assert_eq!(HipStr::from("cfg").split_once('='), None);
    /// assert_eq!(HipStr::from("cfg=").split_once('='), Some(("cfg".into(), "".into())));
    /// assert_eq!(HipStr::from("cfg=foo").split_once('='), Some(("cfg".into(), "foo".into())));
    /// assert_eq!(HipStr::from("cfg=foo=bar").split_once('='), Some(("cfg".into(), "foo=bar".into())));
    /// ```
    #[inline]
    pub fn split_once<P: Pattern>(&self, pattern: P) -> Option<(Self, Self)> {
        pattern
            .split_once(self.as_str())
            .map(|(a, b)| unsafe { (self.slice_ref_unchecked(a), self.slice_ref_unchecked(b)) })
    }

    /// Splits the string on the last occurrence of the specified delimiter and
    /// returns prefix before delimiter and suffix after delimiter.
    ///
    /// Works like [`str::rsplit_once`], but returns `HipStr`s rather than string slices.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// assert_eq!(HipStr::from("cfg").split_once('='), None);
    /// assert_eq!(HipStr::from("cfg=foo").rsplit_once('='), Some(("cfg".into(), "foo".into())));
    /// assert_eq!(HipStr::from("cfg=foo=bar").rsplit_once('='), Some(("cfg=foo".into(), "bar".into())));
    /// ```
    #[inline]
    pub fn rsplit_once<P: ReversePattern>(&self, pattern: P) -> Option<(Self, Self)> {
        pattern
            .rsplit_once(self.as_str())
            .map(|(a, b)| unsafe { (self.slice_ref_unchecked(a), self.slice_ref_unchecked(b)) })
    }

    /// An iterator over the disjoint matches of a pattern within the given string
    /// slice.
    ///
    /// Works like [`str::matches`], but yields `HipStr` rather than string slices.
    ///
    /// See [`str::matches`], for examples and possible patterns.
    #[inline]
    pub fn matches<P: Pattern>(&self, pattern: P) -> IterWrapper<'_, 'a, B, P::Matches<'_>> {
        IterWrapper::new(self, pattern.matches(self.as_str()))
    }

    /// An iterator over the disjoint matches of a pattern within this string slice,
    /// yielded in reverse order.
    ///
    /// Works like [`str::rmatches`], but yields `HipStr` rather than string slices.
    ///
    /// See [`str::rmatches`], for examples and possible patterns.
    #[inline]
    pub fn rmatches<P: ReversePattern>(
        &self,
        pattern: P,
    ) -> IterWrapper<'_, 'a, B, P::RMatches<'_>> {
        IterWrapper::new(self, pattern.rmatches(self.as_str()))
    }

    /// An iterator over the disjoint matches of a pattern within this string
    /// slice as well as the index that the match starts at.
    ///
    /// Works like [`str::match_indices`], but yields `(usize, HipStr)` pairs
    /// rather than `(usize, &str)` pairs.
    ///
    /// See [`str::match_indices`] for examples.
    #[inline]
    pub fn match_indices<P: Pattern>(
        &self,
        pattern: P,
    ) -> IterWrapper<'_, 'a, B, P::MatchIndices<'_>> {
        IterWrapper::new(self, pattern.match_indices(self.as_str()))
    }

    /// An iterator over the disjoint matches of a pattern within `self`,
    /// yielded in reverse order along with the index of the match.
    ///
    /// Works like [`str::rmatch_indices`], but yields `(usize, HipStr)` pairs
    /// rather than `(usize, &str)` pairs.
    ///
    /// See [`str::rmatch_indices`] for examples.
    #[inline]
    pub fn rmatch_indices<P: ReversePattern>(
        &self,
        pattern: P,
    ) -> IterWrapper<'_, 'a, B, P::RMatchIndices<'_>> {
        IterWrapper::new(self, pattern.rmatch_indices(self.as_str()))
    }

    /// Returns a new `HipStr` with leading and trailing whitespace removed.
    ///
    /// Works like [`str::trim_matches`], but returns a `HipStr` rather than a string slice.
    ///
    /// See [`str::trim_matches`] for examples and possible patterns.
    #[inline]
    #[must_use]
    pub fn trim_matches(&self, p: impl DoubleEndedPattern) -> Self {
        let s = p.trim_matches(self.as_str());
        unsafe { self.slice_ref_unchecked(s) }
    }

    /// Returns a string slice with leading whitespace removed.
    ///
    /// Works like [`str::trim_start_matches`], but returns a `HipStr` rather than a string slice.
    ///
    /// See [`str::trim_start_matches`] for examples and possible patterns.
    #[inline]
    #[must_use]
    pub fn trim_start_matches(&self, p: impl Pattern) -> Self {
        let s = p.trim_start_matches(self.as_str());
        unsafe { self.slice_ref_unchecked(s) }
    }

    /// Returns a string slice with trailing whitespace removed.
    ///
    /// Works like [`str::trim_end_matches`], but returns a `HipStr` rather than a string slice.
    ///
    /// See [`str::trim_end_matches`] for examples and possible patterns.
    #[inline]
    #[must_use]
    pub fn trim_end_matches(&self, p: impl ReversePattern) -> Self {
        let s = p.trim_end_matches(self.as_str());
        unsafe { self.slice_ref_unchecked(s) }
    }

    /// Returns a string with the prefix removed.
    ///
    /// If the string starts with the pattern `prefix`, returns substring after the prefix, wrapped
    /// in `Some`. Unlike `trim_start_matches`, this method removes the prefix exactly once.
    ///
    /// If the string does not start with `prefix`, returns `None`.
    ///
    /// Works like [`str::strip_prefix`], but returns a `HipStr` rather than a string slice.
    ///
    /// See [`str::strip_prefix`] for examples and possible patterns.
    #[inline]
    pub fn strip_prefix(&self, prefix: impl Pattern) -> Option<Self> {
        prefix
            .strip_prefix(self.as_str())
            .map(|s| unsafe { self.slice_ref_unchecked(s) })
    }

    /// Returns a string with the suffix removed.
    ///
    /// If the string ends with the pattern `suffix`, returns the substring before the suffix,
    /// wrapped in `Some`.  Unlike `trim_end_matches`, this method removes the suffix exactly once.
    ///
    /// If the string does not end with `suffix`, returns `None`.
    ///
    /// Works like [`str::strip_suffix`], but returns a `HipStr` rather than a
    /// string slice.
    ///
    /// See [`str::strip_suffix`] for examples and possible patterns.
    #[inline]
    pub fn strip_suffix(&self, suffix: impl ReversePattern) -> Option<Self> {
        suffix
            .strip_suffix(self.as_str())
            .map(|s| unsafe { self.slice_ref_unchecked(s) })
    }

    /// Splits a string by whitespace.
    ///
    /// Works like [`str::split_whitespace`], but yields `HipStr`s rather than
    /// string slices.
    ///
    /// See [`str::split_whitespace`] for examples.
    #[inline]
    pub fn split_whitespace(&self) -> IterWrapper<'_, 'a, B, SplitWhitespace<'_>> {
        IterWrapper::new(self, self.as_str().split_whitespace())
    }

    /// Splits a string by ASCII whitespace.
    ///
    /// Works like [`str::split_ascii_whitespace`], but yields `HipStr`s rather than
    /// string slices.
    ///
    /// See [`str::split_ascii_whitespace`] for examples.
    #[inline]
    pub fn split_ascii_whitespace(&self) -> IterWrapper<'_, 'a, B, SplitAsciiWhitespace<'_>> {
        IterWrapper::new(self, self.as_str().split_ascii_whitespace())
    }

    /// An iterator over the lines of a string.
    ///
    /// Works like [`str::split_ascii_whitespace`], but yields `HipStr`s rather than
    /// string slices.
    ///
    /// See [`str::split_ascii_whitespace`] for examples.
    #[inline]
    pub fn lines(&self) -> IterWrapper<'_, 'a, B, Lines<'_>> {
        IterWrapper::new(self, self.as_str().lines())
    }
}
