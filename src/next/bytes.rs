//! Byte strings: [`HipByt`], [`SmallByt`], [`TinyByt`].

use alloc::vec::Vec;
use core::mem::MaybeUninit;

use super::enc::Bytes;
use super::family::{impl_borrowed_ctors, impl_std_glue};
use super::hip::Hip;
use super::repr::Repr;

super::generic_aliases!(Bytes, HipByt, SmallByt, TinyByt, "byte string");

impl_std_glue!(Bytes, [u8], Vec<u8>);
impl_borrowed_ctors!(Bytes, [u8], |value| value);
super::hip::impl_const_typed_accessors!(Bytes, [u8], |b| b);

/// `const` byte accessors, per representation.
macro_rules! impl_const_bytes {
    ($([$($lt:lifetime)?] $repr:ty),* $(,)?) => {$(
        impl<$($lt,)? B: super::backend::Backend> Hip<Bytes, $repr> {
            /// The byte slice.
            #[inline]
            #[must_use]
            pub const fn as_slice(&self) -> &[u8] {
                self.repr().as_slice()
            }
        }
    )*};
}

impl_const_bytes!(
    ['a] super::repr::Wide<'a, u8, B>,
    ['a] super::repr::Small<'a, u8, B>,
    [] super::repr::Tiny<u8, B>,
);

impl<'a, R: Repr<'a, u8>> Hip<Bytes, R> {
    /// Mutable access without copying, if inline or uniquely owned.
    #[inline]
    pub fn as_mut_slice(&mut self) -> Option<&mut [u8]> {
        if self.repr().is_unique() {
            Some(self.to_mut_slice())
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
    pub fn to_mut_slice(&mut self) -> &mut [u8] {
        // SAFETY: no invariant on bytes
        unsafe { self.repr_mut() }.to_mut_slice()
    }

    /// Converts into a `Vec`, in O(1) when the value uniquely owns an
    /// adopted buffer, by copying otherwise.
    #[inline]
    #[must_use]
    pub fn into_vec(self) -> Vec<u8> {
        self.into_owned_std()
    }

    /// Appends a byte.
    #[inline]
    pub fn push(&mut self, value: u8) {
        // SAFETY: no invariant on bytes
        unsafe { self.push_bytes(&[value]) }
    }

    /// Appends bytes.
    #[inline]
    pub fn push_slice(&mut self, addition: &[u8]) {
        // SAFETY: no invariant on bytes
        unsafe { self.push_bytes(addition) }
    }

    /// Alias of [`push_slice`](Self::push_slice), as on `Vec`.
    #[inline]
    pub fn extend_from_slice(&mut self, addition: &[u8]) {
        self.push_slice(addition);
    }

    /// Removes and returns the last byte.
    #[inline]
    pub fn pop(&mut self) -> Option<u8> {
        // SAFETY: no invariant on bytes
        unsafe { self.repr_mut() }.pop()
    }

    /// Shortens to `new_len` bytes; no-op if `new_len` is greater than the length.
    #[inline]
    pub fn truncate(&mut self, new_len: usize) {
        // SAFETY: no invariant on bytes
        unsafe { self.truncate_bytes(new_len) }
    }

    /// The spare capacity, after making the value uniquely owned.
    #[inline]
    pub fn spare_capacity_mut(&mut self) -> &mut [MaybeUninit<u8>] {
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
    /// `new_len` must not exceed [`capacity`](Self::capacity), the bytes up
    /// to `new_len` must be initialized, and the value must be uniquely owned
    /// (e.g. right after [`spare_capacity_mut`](Self::spare_capacity_mut)).
    #[inline]
    pub unsafe fn set_len(&mut self, new_len: usize) {
        // SAFETY: precondition
        unsafe { self.repr_mut().set_len(new_len) }
    }

    /// Repeats the bytes `n` times.
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
            result.push_slice(self.bytes());
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
        if self.bytes().iter().any(u8::is_ascii_uppercase) {
            self.to_mut_slice().make_ascii_lowercase();
        }
    }

    /// Converts to ASCII upper case in place (copying first if needed).
    pub fn make_ascii_uppercase(&mut self) {
        if self.bytes().iter().any(u8::is_ascii_lowercase) {
            self.to_mut_slice().make_ascii_uppercase();
        }
    }

    /// Concatenates byte slices.
    #[must_use]
    pub fn concat_slices(slices: &[&[u8]]) -> Self {
        Self::concat(slices)
    }

    /// Concatenates byte strings.
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
        result
    }

    /// Joins byte slices with a separator.
    #[must_use]
    pub fn join_slices(slices: &[&[u8]], sep: impl AsRef<[u8]>) -> Self {
        Self::join(slices, sep)
    }

    /// Joins byte strings with a separator.
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
        let mut result = Self::with_capacity(len + sep.len() * count.saturating_sub(1));
        for (i, s) in iter.enumerate() {
            if i > 0 {
                result.push_slice(sep);
            }
            result.push_slice(s.as_ref());
        }
        result
    }
}

impl<'a, R: Repr<'a, u8>, const N: usize> From<&[u8; N]> for Hip<Bytes, R> {
    #[inline]
    fn from(value: &[u8; N]) -> Self {
        Self::from_inner(value)
    }
}

impl<'a, R: Repr<'a, u8>> Extend<u8> for Hip<Bytes, R> {
    fn extend<I: IntoIterator<Item = u8>>(&mut self, iter: I) {
        let iter = iter.into_iter();
        // SAFETY: no invariant on bytes
        unsafe { self.repr_mut() }.reserve(iter.size_hint().0);
        for b in iter {
            self.push(b);
        }
    }
}

impl<'a, 'b, R: Repr<'a, u8>> Extend<&'b u8> for Hip<Bytes, R> {
    fn extend<I: IntoIterator<Item = &'b u8>>(&mut self, iter: I) {
        self.extend(iter.into_iter().copied());
    }
}

impl<'a, R: Repr<'a, u8>> FromIterator<u8> for Hip<Bytes, R> {
    fn from_iter<I: IntoIterator<Item = u8>>(iter: I) -> Self {
        let mut result = Self::default();
        result.extend(iter);
        result
    }
}
