//! The `Vec<u8>` API of the byte string families ([`HipByt`](crate::HipByt)
//! and, with the `bstr` feature, [`HipBStr`](crate::HipBStr), in every size).
//!
//! Mutating methods copy borrowed or shared values first (copy-on-write).
//! Methods that may leave the content unchanged (`retain`, `dedup`, …) keep
//! borrowed or shared values as they are when nothing is removed.

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::fmt;
use core::iter::FusedIterator;
use core::marker::PhantomData;
use core::mem::MaybeUninit;
use core::ops::{Range, RangeBounds};

use crate::enc::Unconstrained;
use crate::hip::Hip;
use crate::repr::Repr;
use crate::slice::range_or_panic;

impl<'a, E: Unconstrained, R: Repr<'a>> Hip<E, R> {
    /// Creates a value of `length` bytes, the byte at index `i` being `f(i)`
    /// (see `Vec::from_fn`).
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let b = HipByt::from_fn(4, |i| i as u8 * 2);
    /// assert_eq!(b, [0, 2, 4, 6]);
    /// ```
    pub fn from_fn(length: usize, f: impl FnMut(usize) -> u8) -> Self {
        let mut repr = R::new();
        repr.reserve(length);
        (0..length).map(f).for_each(|b| repr.push(b));
        // SAFETY: no invariant
        unsafe { Self::from_repr(repr) }
    }

    /// Extracts a mutable slice of the entire `HipByt` if possible.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let mut s = HipByt::from(b"foo");
    /// let slice = s.as_mut_slice().unwrap();
    /// slice.copy_from_slice(b"bar");
    /// assert_eq!(b"bar", slice);
    /// ```
    #[inline]
    pub fn as_mut_slice(&mut self) -> Option<&mut [u8]> {
        if self.repr().is_unique() {
            Some(self.to_mut_slice())
        } else {
            None
        }
    }

    /// Extracts a mutable slice of the entire `HipByt` changing the
    /// representation (and thus _potentially reallocating_) if the current
    /// representation cannot be mutated.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let mut s = HipByt::borrowed(b"foo");
    /// let slice = s.to_mut_slice(); // change the representation to inline
    /// slice.copy_from_slice(b"bar");
    /// assert_eq!(b"bar", slice);
    /// ```
    #[inline]
    #[allow(
        clippy::wrong_self_convention,
        reason = "same name as on the current types"
    )]
    pub fn to_mut_slice(&mut self) -> &mut [u8] {
        self.raw_mut()
    }

    /// Appends all bytes of the slice.
    #[inline]
    pub fn extend_from_slice(&mut self, addition: &[u8]) {
        // SAFETY: no invariant
        unsafe { self.push_bytes(addition) }
    }

    /// The spare capacity: empty if the value is borrowed or shared (writing
    /// would need a copy first, see `reserve`).
    #[inline]
    pub fn spare_capacity_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        if !self.repr().is_unique() {
            return &mut [];
        }
        // SAFETY: no invariant on bytes
        let repr = unsafe { self.repr_mut() };
        repr.reserve(0);
        let (len, cap) = (repr.len(), repr.capacity());
        // SAFETY: unique after `reserve`, `cap - len` slots after the elements
        unsafe { core::slice::from_raw_parts_mut(repr.as_mut_ptr().add(len).cast(), cap - len) }
    }

    /// Sets the length.
    ///
    /// # Safety
    ///
    /// Shrinking is always allowed (O(1) for borrowed and shared values). When
    /// growing, `new_len` must not exceed [`capacity`](Self::capacity), the
    /// bytes up to `new_len` must be initialized, and the value must be inline
    /// or uniquely owned (e.g. after writing through
    /// [`spare_capacity_mut`](Self::spare_capacity_mut)).
    #[inline]
    pub unsafe fn set_len(&mut self, new_len: usize) {
        if new_len <= self.bytes().len() {
            // SAFETY: no invariant
            unsafe { self.truncate_bytes(new_len) };
        } else {
            debug_assert!(
                self.repr().is_unique(),
                "growing a borrowed or shared value"
            );
            // SAFETY: precondition
            unsafe { self.repr_mut().set_len(new_len) }
        }
    }

    /// Mutable bytes, copying first if borrowed or shared.
    #[inline]
    fn raw_mut(&mut self) -> &mut [u8] {
        // SAFETY: no invariant
        unsafe { self.bytes_mut() }
    }

    #[inline]
    fn splice_raw(&mut self, range: Range<usize>, with: &[u8]) {
        // SAFETY: no invariant (range checked by callers)
        unsafe { self.splice_bytes(range, with) }
    }

    /// Inserts a byte at `index`, shifting the following ones to the right.
    ///
    /// # Panics
    ///
    /// Panics if `index > len`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let mut b = HipByt::from(b"ac");
    /// b.insert(1, b'b');
    /// assert_eq!(b, b"abc");
    /// ```
    #[track_caller]
    pub fn insert(&mut self, index: usize, element: u8) {
        let len = self.bytes().len();
        assert!(
            index <= len,
            "insertion index (is {index}) should be <= len (is {len})"
        );
        self.splice_raw(index..index, &[element]);
    }

    /// Inserts a byte at `index` and returns a mutable reference to it.
    ///
    /// # Panics
    ///
    /// Panics if `index > len`.
    #[track_caller]
    pub fn insert_mut(&mut self, index: usize, element: u8) -> &mut u8 {
        self.insert(index, element);
        &mut self.raw_mut()[index]
    }

    /// Appends a byte and returns a mutable reference to it.
    pub fn push_mut(&mut self, value: u8) -> &mut u8 {
        let len = self.bytes().len();
        // SAFETY: no invariant
        unsafe { self.push_bytes(&[value]) };
        &mut self.raw_mut()[len]
    }

    /// Removes and returns the byte at `index`, shifting the following ones
    /// to the left.
    ///
    /// # Panics
    ///
    /// Panics if `index >= len`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let mut b = HipByt::from(b"abc");
    /// assert_eq!(b.remove(1), b'b');
    /// assert_eq!(b, b"ac");
    /// ```
    #[track_caller]
    pub fn remove(&mut self, index: usize) -> u8 {
        let len = self.bytes().len();
        assert!(
            index < len,
            "removal index (is {index}) should be < len (is {len})"
        );
        let value = self.bytes()[index];
        self.splice_raw(index..index + 1, &[]);
        value
    }

    /// Removes the byte at `index` and returns it, replacing it by the last
    /// byte (O(1), does not preserve the order).
    ///
    /// # Panics
    ///
    /// Panics if `index >= len`.
    #[track_caller]
    pub fn swap_remove(&mut self, index: usize) -> u8 {
        let len = self.bytes().len();
        assert!(
            index < len,
            "swap_remove index (is {index}) should be < len (is {len})"
        );
        let bytes = self.raw_mut();
        let value = bytes[index];
        bytes[index] = bytes[len - 1];
        // SAFETY: no invariant
        unsafe { self.truncate_bytes(len - 1) };
        value
    }

    /// Removes and returns the last byte if `predicate` returns `true` for it.
    pub fn pop_if(&mut self, predicate: impl FnOnce(&mut u8) -> bool) -> Option<u8> {
        let len = self.bytes().len();
        if len == 0 {
            return None;
        }
        let last = &mut self.raw_mut()[len - 1];
        if predicate(last) {
            let value = *last;
            // SAFETY: no invariant
            unsafe { self.truncate_bytes(len - 1) };
            Some(value)
        } else {
            None
        }
    }

    /// Keeps the bytes for which `f` returns `true`, in order.
    ///
    /// Borrowed and shared values are not copied when every byte is kept.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let mut b = HipByt::from(b"a1b2c3");
    /// b.retain(|b| b.is_ascii_alphabetic());
    /// assert_eq!(b, b"abc");
    /// ```
    pub fn retain(&mut self, mut f: impl FnMut(&u8) -> bool) {
        let Some(first) = self.bytes().iter().position(|b| !f(b)) else {
            return;
        };
        // `f` already rejected the byte at `first`: compact after it
        self.compact(first + 1, first, |_, b| f(b));
    }

    /// Keeps the bytes for which `f` returns `true`, in order, giving `f`
    /// mutable access.
    pub fn retain_mut(&mut self, mut f: impl FnMut(&mut u8) -> bool) {
        if self.bytes().is_empty() {
            return;
        }
        self.compact(0, 0, |_, b| f(b));
    }

    /// Removes consecutive repeated bytes.
    ///
    /// Borrowed and shared values are not copied when there is no repeat.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let mut b = HipByt::from(b"aabbbca");
    /// b.dedup();
    /// assert_eq!(b, b"abca");
    /// ```
    pub fn dedup(&mut self) {
        // first repeat, without touching the storage
        let Some(first) = self.bytes().windows(2).position(|w| w[0] == w[1]) else {
            return;
        };
        // the byte at `first + 1` repeats the last kept one
        self.compact(first + 2, first + 1, |kept, b| *b != *kept.last().unwrap());
    }

    /// Removes consecutive bytes that map to the same key.
    pub fn dedup_by_key<K: PartialEq>(&mut self, mut key: impl FnMut(&mut u8) -> K) {
        self.dedup_by(|a, b| key(a) == key(b));
    }

    /// Removes consecutive bytes for which `same_bucket(current, previous)`
    /// returns `true` (`previous` is the last byte kept).
    pub fn dedup_by(&mut self, mut same_bucket: impl FnMut(&mut u8, &mut u8) -> bool) {
        if self.bytes().len() < 2 {
            return;
        }
        self.compact(1, 1, |kept, b| !same_bucket(b, kept.last_mut().unwrap()));
    }

    /// Compacts the bytes from `read` on: each byte for which `keep(kept,
    /// byte)` returns `true` is moved to `write`, `kept` being the bytes kept
    /// so far. Panic-safe: the unprocessed bytes are kept.
    fn compact(
        &mut self,
        read: usize,
        write: usize,
        mut keep: impl FnMut(&mut [u8], &mut u8) -> bool,
    ) {
        struct Guard<'g, 'a, E: Unconstrained, R: Repr<'a>> {
            hip: &'g mut Hip<E, R>,
            read: usize,
            write: usize,
            len: usize,
            borrow: PhantomData<&'a ()>,
        }
        impl<'a, E: Unconstrained, R: Repr<'a>> Drop for Guard<'_, 'a, E, R> {
            fn drop(&mut self) {
                if self.read != self.write {
                    let bytes = self.hip.raw_mut();
                    bytes.copy_within(self.read..self.len, self.write);
                    // SAFETY: no invariant
                    unsafe { self.hip.truncate_bytes(self.len - (self.read - self.write)) };
                }
            }
        }
        let len = self.bytes().len();
        let mut g = Guard {
            hip: self,
            read,
            write,
            len,
            borrow: PhantomData,
        };
        let bytes = g.hip.raw_mut();
        while g.read < len {
            let (kept, rest) = bytes.split_at_mut(g.read);
            let mut b = rest[0];
            let k = keep(&mut kept[..g.write], &mut b);
            rest[0] = b;
            g.read += 1;
            if k {
                bytes[g.write] = b;
                g.write += 1;
            }
        }
    }

    /// Resizes to `new_len`, filling with `value` when growing.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let mut b = HipByt::from(b"ab");
    /// b.resize(4, b'!');
    /// assert_eq!(b, b"ab!!");
    /// b.resize(1, 0);
    /// assert_eq!(b, b"a");
    /// ```
    pub fn resize(&mut self, new_len: usize, value: u8) {
        // SAFETY: no invariant
        unsafe { self.repr_mut() }.resize(new_len, value);
    }

    /// Resizes to `new_len`, filling with the results of `f` when growing.
    pub fn resize_with(&mut self, new_len: usize, mut f: impl FnMut() -> u8) {
        let len = self.bytes().len();
        if new_len <= len {
            // SAFETY: no invariant
            unsafe { self.truncate_bytes(new_len) };
            return;
        }
        // SAFETY: no invariant
        let repr = unsafe { self.repr_mut() };
        repr.reserve(new_len - len);
        for _ in len..new_len {
            repr.push(f());
        }
    }

    /// Appends a copy of the bytes in `src`.
    ///
    /// # Panics
    ///
    /// Panics if the range is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let mut b = HipByt::from(b"abc");
    /// b.extend_from_within(..2);
    /// assert_eq!(b, b"abcab");
    /// ```
    #[track_caller]
    pub fn extend_from_within(&mut self, src: impl RangeBounds<usize>) {
        let len = self.bytes().len();
        let src = range_or_panic(src, len);
        let n = src.len();
        self.resize(len + n, 0);
        self.raw_mut().copy_within(src, len);
    }

    /// Splits in two at `at`: `self` keeps `[0, at)` and the rest is
    /// returned.
    ///
    /// # Panics
    ///
    /// Panics if `at > len`.
    #[track_caller]
    #[must_use = "use `.truncate()` if you don't need the other half"]
    pub fn split_off(&mut self, at: usize) -> Self {
        let len = self.bytes().len();
        assert!(
            at <= len,
            "`at` split index (is {at}) should be <= len (is {len})"
        );
        // SAFETY: no invariant
        let tail = unsafe { Self::from_repr(R::from_slice(&self.bytes()[at..])) };
        // SAFETY: no invariant
        unsafe { self.truncate_bytes(at) };
        tail
    }

    /// Moves all the bytes of `other` to the end of `self`, leaving `other`
    /// empty.
    pub fn append(&mut self, other: &mut Self) {
        if self.bytes().is_empty() {
            core::mem::swap(self, other);
        } else {
            self.extend_from_slice_inner(other.bytes());
            other.clear();
        }
    }

    #[inline]
    fn extend_from_slice_inner(&mut self, bytes: &[u8]) {
        // SAFETY: no invariant
        unsafe { self.push_bytes(bytes) }
    }

    /// Removes the bytes in `range`, returning them as an iterator.
    ///
    /// The bytes are removed when the iterator is dropped, even if it is not
    /// fully consumed. If it is leaked (e.g. with `mem::forget`), the value
    /// is left unchanged.
    ///
    /// # Panics
    ///
    /// Panics if the range is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let mut b = HipByt::from(b"abcdef");
    /// let drained: Vec<u8> = b.drain(1..3).collect();
    /// assert_eq!(drained, b"bc");
    /// assert_eq!(b, b"adef");
    /// ```
    #[track_caller]
    pub fn drain(&mut self, range: impl RangeBounds<usize>) -> Drain<'_, 'a, E, R> {
        let range = range_or_panic(range, self.bytes().len());
        Drain {
            front: range.start,
            back: range.end,
            range,
            hip: self,
            borrow: PhantomData,
        }
    }

    /// Replaces the bytes in `range` by those of `replace_with`, returning
    /// the removed bytes as an iterator.
    ///
    /// The replacement happens when the iterator is dropped.
    ///
    /// # Panics
    ///
    /// Panics if the range is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let mut b = HipByt::from(b"abcdef");
    /// let removed: Vec<u8> = b.splice(1..3, *b"XYZ").collect();
    /// assert_eq!(removed, b"bc");
    /// assert_eq!(b, b"aXYZdef");
    /// ```
    #[track_caller]
    pub fn splice<I: IntoIterator<Item = u8>>(
        &mut self,
        range: impl RangeBounds<usize>,
        replace_with: I,
    ) -> Splice<'_, 'a, E, R, I::IntoIter> {
        Splice {
            drain: self.drain(range),
            replace_with: replace_with.into_iter(),
        }
    }

    /// Removes and yields the bytes in `range` for which `filter` returns
    /// `true`, keeping the others in order.
    ///
    /// Bytes not yet visited when the iterator is dropped are kept.
    ///
    /// # Panics
    ///
    /// Panics if the range is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let mut b = HipByt::from(b"a1b2c3");
    /// let digits: Vec<u8> = b.extract_if(.., |b| b.is_ascii_digit()).collect();
    /// assert_eq!(digits, b"123");
    /// assert_eq!(b, b"abc");
    /// ```
    #[track_caller]
    pub fn extract_if<F: FnMut(&mut u8) -> bool>(
        &mut self,
        range: impl RangeBounds<usize>,
        filter: F,
    ) -> ExtractIf<'_, 'a, E, R, F> {
        let len = self.bytes().len();
        let range = range_or_panic(range, len);
        ExtractIf {
            read: range.start,
            write: range.start,
            end: range.end,
            len,
            filter,
            hip: self,
            borrow: PhantomData,
        }
    }

    /// Converts into a boxed slice (copying unless the value uniquely owns an
    /// adopted buffer of the exact size).
    #[must_use]
    pub fn into_boxed_slice(self) -> Box<[u8]> {
        // SAFETY: no invariant
        let bytes: Hip<crate::enc::Bytes, R> = unsafe { Hip::from_repr(self.into_repr()) };
        bytes.into_vec().into_boxed_slice()
    }

    /// Leaks the bytes, returning a mutable reference to them (see
    /// `Vec::leak`).
    #[must_use]
    pub fn leak<'b>(self) -> &'b mut [u8] {
        // SAFETY: no invariant
        let bytes: Hip<crate::enc::Bytes, R> = unsafe { Hip::from_repr(self.into_repr()) };
        bytes.into_vec().leak()
    }
}

/// Draining iterator returned by [`Hip::drain`] on byte strings.
pub struct Drain<'h, 'a, E: Unconstrained, R: Repr<'a>> {
    hip: &'h mut Hip<E, R>,
    range: Range<usize>,
    front: usize,
    back: usize,
    borrow: PhantomData<&'a ()>,
}

impl<'a, E: Unconstrained, R: Repr<'a>> Drain<'_, 'a, E, R> {
    /// The bytes not yet yielded.
    #[must_use]
    pub fn as_slice(&self) -> &[u8] {
        &self.hip.bytes()[self.front..self.back]
    }
}

impl<'a, E: Unconstrained, R: Repr<'a>> fmt::Debug for Drain<'_, 'a, E, R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Drain").field(&self.as_slice()).finish()
    }
}

impl<'a, E: Unconstrained, R: Repr<'a>> Iterator for Drain<'_, 'a, E, R> {
    type Item = u8;

    #[inline]
    fn next(&mut self) -> Option<u8> {
        if self.front == self.back {
            return None;
        }
        let b = self.hip.bytes()[self.front];
        self.front += 1;
        Some(b)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let n = self.back - self.front;
        (n, Some(n))
    }
}

impl<'a, E: Unconstrained, R: Repr<'a>> DoubleEndedIterator for Drain<'_, 'a, E, R> {
    #[inline]
    fn next_back(&mut self) -> Option<u8> {
        if self.front == self.back {
            return None;
        }
        self.back -= 1;
        Some(self.hip.bytes()[self.back])
    }
}

impl<'a, E: Unconstrained, R: Repr<'a>> ExactSizeIterator for Drain<'_, 'a, E, R> {}
impl<'a, E: Unconstrained, R: Repr<'a>> FusedIterator for Drain<'_, 'a, E, R> {}

impl<'a, E: Unconstrained, R: Repr<'a>> Drop for Drain<'_, 'a, E, R> {
    fn drop(&mut self) {
        let range = core::mem::replace(&mut self.range, 0..0);
        self.hip.splice_raw(range, &[]);
    }
}

/// Splicing iterator returned by [`Hip::splice`] on byte strings.
pub struct Splice<'h, 'a, E: Unconstrained, R: Repr<'a>, I: Iterator<Item = u8>> {
    drain: Drain<'h, 'a, E, R>,
    replace_with: I,
}

impl<'a, E: Unconstrained, R: Repr<'a>, I: Iterator<Item = u8> + fmt::Debug> fmt::Debug
    for Splice<'_, 'a, E, R, I>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Splice")
            .field("drain", &self.drain)
            .field("replace_with", &self.replace_with)
            .finish()
    }
}

impl<'a, E: Unconstrained, R: Repr<'a>, I: Iterator<Item = u8>> Iterator
    for Splice<'_, 'a, E, R, I>
{
    type Item = u8;

    #[inline]
    fn next(&mut self) -> Option<u8> {
        self.drain.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.drain.size_hint()
    }
}

impl<'a, E: Unconstrained, R: Repr<'a>, I: Iterator<Item = u8>> DoubleEndedIterator
    for Splice<'_, 'a, E, R, I>
{
    #[inline]
    fn next_back(&mut self) -> Option<u8> {
        self.drain.next_back()
    }
}

impl<'a, E: Unconstrained, R: Repr<'a>, I: Iterator<Item = u8>> ExactSizeIterator
    for Splice<'_, 'a, E, R, I>
{
}

impl<'a, E: Unconstrained, R: Repr<'a>, I: Iterator<Item = u8>> Drop for Splice<'_, 'a, E, R, I> {
    fn drop(&mut self) {
        let replacement: Vec<u8> = self.replace_with.by_ref().collect();
        let range = core::mem::replace(&mut self.drain.range, 0..0);
        self.drain.hip.splice_raw(range, &replacement);
    }
}

/// Iterator returned by [`Hip::extract_if`] on byte strings.
pub struct ExtractIf<'h, 'a, E: Unconstrained, R: Repr<'a>, F: FnMut(&mut u8) -> bool> {
    hip: &'h mut Hip<E, R>,
    read: usize,
    write: usize,
    end: usize,
    len: usize,
    filter: F,
    borrow: PhantomData<&'a ()>,
}

impl<'a, E: Unconstrained, R: Repr<'a>, F: FnMut(&mut u8) -> bool> fmt::Debug
    for ExtractIf<'_, 'a, E, R, F>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ExtractIf")
            .field("remaining", &&self.hip.bytes()[self.read..self.end])
            .finish_non_exhaustive()
    }
}

impl<'a, E: Unconstrained, R: Repr<'a>, F: FnMut(&mut u8) -> bool> Iterator
    for ExtractIf<'_, 'a, E, R, F>
{
    type Item = u8;

    fn next(&mut self) -> Option<u8> {
        while self.read < self.end {
            let bytes = self.hip.raw_mut();
            let mut b = bytes[self.read];
            let take = (self.filter)(&mut b);
            bytes[self.read] = b;
            self.read += 1;
            if take {
                return Some(b);
            }
            bytes[self.write] = b;
            self.write += 1;
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.end - self.read))
    }
}

impl<'a, E: Unconstrained, R: Repr<'a>, F: FnMut(&mut u8) -> bool> Drop
    for ExtractIf<'_, 'a, E, R, F>
{
    fn drop(&mut self) {
        if self.read != self.write {
            let bytes = self.hip.raw_mut();
            bytes.copy_within(self.read..self.len, self.write);
            // SAFETY: no invariant
            unsafe { self.hip.truncate_bytes(self.len - (self.read - self.write)) };
        }
    }
}
