//! Byte strings: [`HipByt`], [`SmallByt`], [`TinyByt`].

use alloc::borrow::Cow;
use alloc::boxed::Box;
use alloc::vec::Vec;

use super::enc::Bytes;
use super::family::{impl_borrowed_ctors, impl_cmp, impl_std_glue};
use super::hip::Hip;
use super::repr::Repr;
pub use crate::hip::RefMut;
pub use crate::slice::{SliceError, SliceErrorKind};
pub use crate::std_traits::IntoIter;
pub use crate::vec_ops::{Drain, ExtractIf, Splice};

/// `serde` helpers.
#[cfg(feature = "serde")]
pub mod serde {
    pub use crate::serde_impl::bytes::borrow_deserialize;

    #[cfg(test)]
    mod tests;
}

#[cfg(all(feature = "borsh", test))]
mod borsh {
    use borsh::{BorshDeserialize, BorshSerialize};

    mod tests;
}

#[cfg(test)]
mod tests;

super::generic_aliases!(Bytes, HipByt, SmallByt, TinyByt, "byte string");

impl_std_glue!(Bytes, [u8], Vec<u8>);
impl_borrowed_ctors!(Bytes, [u8], |value| value);

impl_cmp!(Bytes as [u8];
    [] [u8], [] &[u8], [const N: usize] [u8; N], [const N: usize] &[u8; N],
    [] Vec<u8>, [] &Vec<u8>, [] Box<[u8]>, [] &Box<[u8]>, [] Cow<'_, [u8]>, [] &Cow<'_, [u8]>,
);
super::hip::impl_const_typed_accessors!(Bytes, [u8], |b| b, |v| v);

/// `const` byte accessors, per representation.
macro_rules! impl_const_bytes {
    ($([$($lt:lifetime)?] $repr:ty),* $(,)?) => {$(
        impl<$($lt,)? B: super::backend::Backend> Hip<Bytes, $repr> {
            /// Extracts a slice of the entire `HipByt`.
            ///
            /// # Examples
            ///
            /// Basic usage:
            ///
            /// ```
            /// # use hipstr::HipByt;
            /// let s = HipByt::from(b"foobar");
            ///
            /// assert_eq!(b"foobar", s.as_slice());
            /// ```
            #[inline]
            #[must_use]
            pub const fn as_slice(&self) -> &[u8] {
                self.repr().as_slice()
            }
        }
    )*};
}

impl_const_bytes!(
    ['a] super::repr::Wide<'a, B>,
    ['a] super::repr::Small<'a, B>,
    [] super::repr::Tiny<B>,
);

impl<'a, R: Repr<'a>> Hip<Bytes, R> {
    /// Converts into a `Vec`, in O(1) when the value uniquely owns an
    /// adopted buffer, by copying otherwise.
    #[inline]
    #[must_use]
    pub fn into_vec(self) -> Vec<u8> {
        self.into_owned_std()
    }

    /// Appends a byte to this `HipByt`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let mut bytes = HipByt::from(b"abc");
    /// bytes.push(b'1');
    /// bytes.push(b'2');
    /// bytes.push(b'3');
    /// assert_eq!(bytes, b"abc123");
    /// ```
    #[inline]
    pub fn push(&mut self, value: u8) {
        // SAFETY: no invariant on bytes
        unsafe { self.push_bytes(&[value]) }
    }

    /// Appends all bytes of the slice to this `HipByt`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let mut bytes = HipByt::from(b"abc");
    /// bytes.push_slice(b"123");
    /// assert_eq!(bytes, b"abc123");
    /// ```
    #[inline]
    pub fn push_slice(&mut self, addition: &[u8]) {
        // SAFETY: no invariant on bytes
        unsafe { self.push_bytes(addition) }
    }

    /// Removes the last element from this `HipByt` and returns it, or [`None`]
    /// if it is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipByt;
    ///
    /// let mut h = HipByt::from(&[1, 2, 3]);
    /// assert_eq!(h.pop(), Some(3));
    /// assert_eq!(h, [1, 2]);
    /// ```
    #[inline]
    pub fn pop(&mut self) -> Option<u8> {
        // SAFETY: no invariant on bytes
        unsafe { self.repr_mut() }.pop()
    }

    /// Shortens this `HipByt` to the specified length.
    ///
    /// If the new length is greater than the current length, this has no effect.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let mut a = HipByt::from(b"abc");
    /// a.truncate(1);
    /// assert_eq!(a, b"a");
    /// ```
    #[inline]
    pub fn truncate(&mut self, new_len: usize) {
        // SAFETY: no invariant on bytes
        unsafe { self.truncate_bytes(new_len) }
    }

    /// Creates a new `HipByt` by copying this one `n` times.
    ///
    /// This function **will not allocate** if the new length is less than or
    /// equal to the maximum inline capacity.
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
    /// # use hipstr::HipByt;
    /// assert_eq!(HipByt::from(&[1, 2]).repeat(3), HipByt::from(&[1, 2, 1, 2, 1, 2]));
    /// ```
    ///
    /// A panic upon overflow:
    ///
    /// ```should_panic
    /// // this will panic at runtime
    /// # use hipstr::HipByt;
    /// HipByt::from(b"0123456789abcdef").repeat(usize::MAX);
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
            result.push_slice(self.bytes());
        }
        result
    }

    /// Returns a new `HipByt` containing a copy of this slice where each byte
    /// is mapped to its ASCII lower case equivalent.
    ///
    /// ASCII letters 'A' to 'Z' are mapped to 'a' to 'z',
    /// but non-ASCII letters are unchanged.
    ///
    /// To lowercase the value in-place, use [`make_ascii_lowercase`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hipstr::HipByt;
    /// let h = HipByt::from(b"!abc\0OK\x80");
    /// let h2 = h.to_ascii_lowercase();
    /// assert_eq!(h2, b"!abc\0ok\x80");
    /// ```
    ///
    /// [`make_ascii_lowercase`]: Self::make_ascii_lowercase
    #[must_use]
    pub fn to_ascii_lowercase(&self) -> Self {
        let mut result = self.clone();
        result.make_ascii_lowercase();
        result
    }

    /// Returns a new `HipByt` containing a copy of this slice where each byte
    /// is mapped to its ASCII lower case equivalent.
    ///
    /// ASCII letters 'A' to 'Z' are mapped to 'a' to 'z',
    /// but non-ASCII letters are unchanged.
    ///
    /// To lowercase the value in-place, use [`make_ascii_lowercase`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hipstr::HipByt;
    /// let h = HipByt::from(b"!abc\0OK\x80");
    /// let h2: HipByt = h.to_ascii_uppercase();
    /// assert_eq!(h2, b"!ABC\0OK\x80");
    /// ```
    ///
    /// [`make_ascii_lowercase`]: Self::make_ascii_lowercase
    #[must_use]
    pub fn to_ascii_uppercase(&self) -> Self {
        let mut result = self.clone();
        result.make_ascii_uppercase();
        result
    }

    /// Converts this slice to its ASCII lower case equivalent in-place.
    ///
    /// ASCII letters 'A' to 'Z' are mapped to 'a' to 'z',
    /// but non-ASCII letters are unchanged.
    ///
    /// To return a new lowercased value without modifying the existing one, use
    /// [`to_ascii_lowercase`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hipstr::HipByt;
    /// let mut h = HipByt::from(b"!abc\0OK\x80");
    /// h.make_ascii_lowercase();
    /// assert_eq!(h, b"!abc\0ok\x80");
    /// ```
    ///
    /// [`to_ascii_lowercase`]: Self::to_ascii_lowercase
    pub fn make_ascii_lowercase(&mut self) {
        if self.bytes().iter().any(u8::is_ascii_uppercase) {
            self.to_mut_slice().make_ascii_lowercase();
        }
    }

    /// Converts this slice to its ASCII upper case equivalent in-place.
    ///
    /// ASCII letters 'a' to 'z' are mapped to 'A' to 'Z',
    /// but non-ASCII letters are unchanged.
    ///
    /// To return a new uppercased value without modifying the existing one, use
    /// [`to_ascii_uppercase`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hipstr::HipByt;
    /// let mut h = HipByt::from(b"!abc\0OK\x80");
    /// h.make_ascii_uppercase();
    /// assert_eq!(h, b"!ABC\0OK\x80");
    /// ```
    ///
    /// [`to_ascii_uppercase`]: Self::to_ascii_uppercase
    pub fn make_ascii_uppercase(&mut self) {
        if self.bytes().iter().any(u8::is_ascii_lowercase) {
            self.to_mut_slice().make_ascii_uppercase();
        }
    }

    /// Concatenates some byte slices into a single `HipByt`.
    ///
    /// The related constructor [`HipByt::concat`] is more general but may be
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
    pub fn concat_slices(slices: &[&[u8]]) -> Self {
        Self::concat(slices)
    }

    /// Concatenates some byte slices (or things than can be seen as byte slice) into a new `HipByt`.
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
    /// # use hipstr::HipByt;
    /// let c  = HipByt::concat(&[b"hello".as_slice(), b" world", b"!"]);
    /// assert_eq!(c, b"hello world!");
    ///
    /// let c2 = HipByt::concat([b"hello".to_vec(), b" world".to_vec(), b"!".to_vec()]);
    /// assert_eq!(c2, b"hello world!");
    ///
    /// let c3 = HipByt::concat(vec![b"hello".as_slice(), b" world", b"!"].iter());
    /// assert_eq!(c3, b"hello world!");
    /// ```
    #[must_use]
    pub fn concat<S: AsRef<[u8]>, I: IntoIterator<Item = S>>(slices: I) -> Self
    where
        I::IntoIter: Clone,
    {
        let iter = slices.into_iter();
        let len = iter.clone().map(|s| s.as_ref().len()).sum();
        let mut result = Self::with_capacity(len);
        for s in iter {
            result.push_slice(s.as_ref());
        }
        assert_eq!(result.bytes().len(), len, "inconsistent iterator");
        result
    }

    /// Joins some byte slices with the given separator into a new `HipByt`, i.e.
    /// concatenates some byte slices, with a separator byte inserted between
    /// each pair of byte slices.
    ///
    /// The related constructor [`HipByt::join`] is more general but may be less
    /// efficient due to the absence of specialization in Rust.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let slices: &[&[u8]] = &[b"hello", b"world", b"rust"];
    /// let sep = b", ";
    /// let joined = HipByt::join_slices(slices, sep);
    /// assert_eq!(joined, b"hello, world, rust");
    /// ```
    #[must_use]
    pub fn join_slices(slices: &[&[u8]], sep: impl AsRef<[u8]>) -> Self {
        Self::join(slices, sep)
    }

    /// Joins some byte slices (or things than can be seen as byte slice) with
    /// the given separator into a new `HipByt`.
    ///
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
    /// ```rust
    /// # use hipstr::HipByt;
    /// let slices: &[&[u8]] = &[b"hello", b"world", b"rust"];
    /// let sep = b", ";
    /// let joined = HipByt::join(slices, sep);
    /// assert_eq!(joined, b"hello, world, rust");
    ///
    /// let joined = HipByt::join([b"hello".to_vec(), b"world".to_vec(), b"rust".to_vec()], sep.to_vec());
    /// assert_eq!(joined, b"hello, world, rust");
    ///
    /// let joined = HipByt::join(slices.to_vec().iter(), sep);
    /// assert_eq!(joined, b"hello, world, rust");
    /// ```
    #[must_use]
    pub fn join<S: AsRef<[u8]>, I: IntoIterator<Item = S>>(slices: I, sep: impl AsRef<[u8]>) -> Self
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
                result.push_slice(sep);
            }
            result.push_slice(s.as_ref());
        }
        assert_eq!(result.bytes().len(), expected, "inconsistent iterator");
        result
    }
}

impl<'a, R: Repr<'a>, const N: usize> From<&[u8; N]> for Hip<Bytes, R> {
    #[inline]
    fn from(value: &[u8; N]) -> Self {
        Self::from_inner(value)
    }
}
