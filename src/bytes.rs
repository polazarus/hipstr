//! Bytes.
//!
//! This module provides the [`HipByt`] type as well as the associated helper
//! and error types.

use alloc::fmt;
use alloc::vec::Vec;
use core::borrow::Borrow;
use core::hash::Hash;
use core::mem::{self, MaybeUninit};
use core::ops::{Deref, DerefMut, RangeBounds};
use core::ptr;

use rules_derive::rules_derive;

use crate::backend::Backend;
use crate::common::derives::ConstDefault;
use crate::common::RangeError;
use crate::vecs::hip::HipVec;

mod cmp;
mod convert;

#[cfg(feature = "borsh")]
mod borsh;
#[cfg(feature = "bstr")]
mod bstr;
#[cfg(feature = "serde")]
pub mod serde;

#[cfg(test)]
mod tests;

#[cfg(feature = "bstr")]
type Slice = ::bstr::BStr;

#[cfg(not(feature = "bstr"))]
type Slice = [u8];

/// Smart bytes, i.e. cheaply clonable and sliceable byte string.
///
/// # Examples
///
/// You can create a `HipStr` from a [byte slice (&`[u8]`)][slice], an owned
/// byte string ([`Vec<u8>`], [`Box<[u8]>`][std::boxed::Box]), or a
/// clone-on-write smart pointer ([`Cow<[u8]>`][std::borrow::Cow]) with
/// [`From`]:
///
/// ```
/// # use hipstr::HipByt;
/// let hello = HipByt::from(b"Hello".as_slice());
/// ```
///
/// When possible, `HipStr::from` takes ownership of the underlying buffer:
///
/// ```
/// # use hipstr::HipByt;
/// let vec = Vec::from(b"World".as_slice());
/// let world = HipByt::from(vec);
/// ```
///
/// To borrow a string slice, you can also use the no-copy constructor
/// [`HipByt::borrowed`]:
///
/// ```
/// # use hipstr::HipByt;
/// let hello = HipByt::borrowed(b"Hello, world!");
/// ```
///
/// # Representations
///
/// `HipByt` has three possible internal representations:
///
/// * borrow
/// * inline string
/// * shared heap allocated string
///
/// # Notable features
///
/// `HipByt` dereferences through the [`Deref`] trait to either `&[u8]` ot
/// [`&bstr::BStr`] if the feature flag `bstr` is set. [`bstr`] allows for
/// efficient string-like manipulation on non-guaranteed UTF-8 data.
///
/// In the same manner, [`HipByt::mutate`] returns a mutable handle [`RefMut`]
/// to a `Vec<[u8]>` or a [`bstr::BString`] if the flag `bstr` is set.
///
/// [`bstr`]: https://crates.io/crates/bstr
/// [`&bstr::BStr`]: https://docs.rs/bstr/latest/bstr/struct.BStr.html
/// [`bstr::BString`]: https://docs.rs/bstr/latest/bstr/struct.BString.html
/// [`Deref`]: core::ops::Deref
/// [`RefMut`]: super::RefMut
#[repr(transparent)]
#[rules_derive(ConstDefault(Self::new()))]
pub struct HipByt<'borrow, B: Backend>(pub(crate) HipVec<'borrow, u8, B>);

impl<'borrow, B: Backend> Clone for HipByt<'borrow, B>
where
    HipVec<'borrow, u8, B>: Clone,
{
    #[inline]
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<'borrow, B> HipByt<'borrow, B>
where
    B: Backend,
{
    pub(crate) const fn into_hipvec(self) -> HipVec<'borrow, u8, B> {
        unsafe { mem::transmute(self) }
    }

    // derived constructors

    /// Creates a new `HipByt` from a vector.
    #[inline]
    pub(crate) fn from_vec(vec: Vec<u8>) -> Self {
        Self(HipVec::from_vec(vec))
    }

    /// Creates a new `HipByt` from a slice.
    ///
    /// Will normalize the representation depending on the size of the slice.
    pub(crate) fn from_slice(bytes: &[u8]) -> Self {
        Self(HipVec::from_slice_copy(bytes))
    }

    /// Extracts a slice as its own `HipByt` based on the given subslice `&[u8]`.
    ///
    /// # Safety
    ///
    /// The slice MUST be a part of this `HipByt`
    ///
    /// # Panics
    ///
    /// When in debug build, panics if the slice is not a part of this `HipByt`.
    #[must_use]
    pub unsafe fn slice_ref_unchecked(&self, slice: &[u8]) -> Self {
        Self(unsafe { HipVec::slice_ref_copy(&self.0, slice).unwrap_unchecked() })
    }

    /// Makes the underlying data uniquely owned, copying if needed.
    #[doc(alias = "make_unique")]
    #[inline]
    pub fn detach(&mut self) {
        self.0.detach_copy();
    }

    /// Returns `true` it `self` is equal byte for byte to `other`.
    #[inline(never)]
    pub(crate) fn inherent_eq<B2: Backend>(&self, other: &HipByt<B2>) -> bool {
        // use memcmp directly to squeeze one more comparison
        extern "C" {
            fn memcmp(a: *const u8, b: *const u8, size: usize) -> core::ffi::c_int;
        }

        let len = self.len();
        if len != other.len() {
            return false;
        }

        let self_ptr = self.as_ptr();
        let other_ptr = other.as_ptr();
        if core::ptr::eq(self_ptr, other_ptr) {
            return true;
        }

        // use element size (just a remainder for now)
        let size = len * size_of::<u8>();

        // SAFETY: size checked above
        unsafe { memcmp(self_ptr, other_ptr, size) == 0 }
    }

    /// Creates an empty `HipByt`.
    ///
    /// Function provided for [`Vec::new`] replacement.
    ///
    /// # Representation
    ///
    /// <div class=warning>
    ///
    /// The used representation of the empty string is unspecified.
    /// It may be _borrowed_ or _inlined_ but will never be allocated.
    ///
    /// </div>
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let s = HipByt::new();
    /// ```
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self(HipVec::new())
    }

    /// Creates a new inline `HipByt` by copying the given slice.
    /// The slice **must not** be too large to be inlined.
    ///
    /// # Representation
    ///
    /// The created `HipByt` is _inline_.
    ///
    /// # Panics
    ///
    /// It panics if the slice is too large.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let s = HipByt::inline(b"hello\0");
    /// assert_eq!(s, b"hello\0");
    /// ```
    #[must_use]
    pub const fn inline(bytes: &[u8]) -> Self {
        Self(HipVec::inline_copy(bytes))
    }

    #[must_use]
    #[inline]
    pub(crate) const fn fit_inline(len: usize) -> bool {
        HipVec::<u8, B>::fit_inline(len)
    }

    /// Creates a new inline `HipByt` by copying the given the slice.
    /// Return `None` if the given slice is too large to be inlined.
    ///
    /// # Representation
    ///
    /// In case of success, the created `HipByt` is _inline_.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let s = HipByt::try_inline(b"hello\0").unwrap();
    /// assert_eq!(s, b"hello\0");
    /// ```
    #[must_use]
    #[inline]
    pub const fn try_inline(bytes: &[u8]) -> Option<Self> {
        if Self::fit_inline(bytes.len()) {
            Some(Self::inline(bytes))
        } else {
            None
        }
    }

    /// Creates a new `HipByt` with the given capacity.
    ///
    /// The final capacity depends on the representation and is not guaranteed
    /// to be exact. However, the returned `HipByt` will be able to hold at
    /// least `capacity` bytes without reallocating or changing representation.
    ///
    /// # Representation
    ///
    /// If the capacity is less or equal to the inline capacity, the
    /// representation will be *inline*.
    ///
    /// Otherwise, it will be *allocated*.
    ///
    /// The representation is **not normalized**.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let mut s = HipByt::with_capacity(42);
    /// let p = s.as_ptr();
    /// for _ in 0..42 {
    ///     s.push(b'*');
    /// }
    /// assert_eq!(s, [b'*'; 42]);
    /// assert_eq!(s.as_ptr(), p);
    /// ```
    #[inline]
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self(HipVec::with_capacity(capacity))
    }

    /// Creates a new `HipByt` from a byte slice.
    /// No heap allocation is performed.
    /// **The slice is not copied.**
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let b = HipByt::borrowed(b"hello\0");
    /// assert_eq!(b.len(), 6);
    /// ```
    #[must_use]
    #[inline]
    pub const fn borrowed(bytes: &'borrow [u8]) -> Self {
        Self(HipVec::borrowed(bytes))
    }

    /// Returns the length of this `HipByt`.
    ///
    /// # Example
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let a = HipByt::borrowed(b"\xDE\xAD\xBE\xEF");
    /// assert_eq!(a.len(), 4);
    /// ```
    #[inline]
    #[must_use]
    pub const fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns `true` if this `HipByt` has a length of zero, and `false` otherwise.
    ///
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let a = HipByt::new();
    /// assert!(a.is_empty());
    ///
    /// let b = HipByt::borrowed(b"ab");
    /// assert!(!b.is_empty());
    /// ```
    #[inline]
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns a raw pointer to the start of the byte sequence.
    ///
    /// The caller must ensure the `HipByt` outlives the pointer this function
    /// returns, or else it will end up dangling.
    /// Modifying the byte sequence may change representation or reallocate,
    /// which would invalid the returned pointer.
    #[inline]
    #[must_use]
    pub const fn as_ptr(&self) -> *const u8 {
        self.0.as_ptr()
    }

    /// Returns a raw mutable pointer to the start of the byte sequence.
    ///
    /// The caller must ensure the `HipByt` outlives the pointer this function
    /// returns, or else it will end up dangling.
    /// Modifying the byte sequence may change representation or reallocate,
    /// which would invalid the returned pointer.
    #[inline]
    #[must_use]
    pub fn as_mut_ptr(&mut self) -> Option<*mut u8> {
        self.0.as_mut_ptr()
    }

    /// Returns a raw mutable pointer to the start of the byte sequence.
    ///
    /// The caller must ensure the `HipByt` outlives the pointer this function
    /// returns, or else it will end up dangling. Modifying the byte sequence
    /// may change representation or reallocate, which would invalid the
    /// returned pointer.
    ///
    /// # Safety
    ///
    /// The caller must ensure the sequence is actually unique: not shared and
    /// not borrowed.
    ///
    /// # Panics
    ///
    /// In debug mode, this function panics if the sequence is borrowed or
    /// shared.
    #[inline]
    #[must_use]
    pub unsafe fn as_mut_ptr_unchecked(&mut self) -> *mut u8 {
        unsafe { self.0.as_mut_ptr_unchecked() }
    }

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
        self.0.as_slice()
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
    #[must_use]
    pub fn as_mut_slice(&mut self) -> Option<&mut [u8]> {
        self.0.as_mut_slice()
    }

    /// Extracts a mutable slice of the entire `HipByt`.
    ///
    /// # Safety
    ///
    /// This `HipByt` should not be shared or borrowed.
    ///
    /// # Panics
    ///
    /// In debug mode, panics if the sequence is borrowed or shared.
    #[inline]
    pub unsafe fn as_mut_slice_unchecked(&mut self) -> &mut [u8] {
        unsafe { self.0.as_mut_slice_unchecked() }
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
    #[doc(alias = "make_mut")]
    pub fn to_mut_slice(&mut self) -> &mut [u8] {
        self.0.to_mut_slice_copy()
    }

    /// Returns `true` if this `HipByt` uses the inline representation, `false` otherwise.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let s = HipByt::borrowed(b"hello");
    /// assert!(!s.is_inline());
    ///
    /// let s = HipByt::from(b"hello");
    /// assert!(s.is_inline());
    ///
    /// let s = HipByt::from(b"hello".repeat(10));
    /// assert!(!s.is_inline());
    /// ```
    #[inline]
    #[must_use]
    pub const fn is_inline(&self) -> bool {
        self.0.is_inline()
    }

    /// Returns `true` if this `HipByt` is a slice borrow, `false` otherwise.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let s = HipByt::borrowed(b"hello");
    /// assert!(s.is_borrowed());
    ///
    /// let s = HipByt::from(b"hello");
    /// assert!(!s.is_borrowed());
    ///
    /// let s = HipByt::from(b"hello".repeat(10));
    /// assert!(!s.is_borrowed());
    /// ```
    #[inline]
    #[must_use]
    pub const fn is_borrowed(&self) -> bool {
        self.0.is_borrowed()
    }

    /// Converts `self` into a borrowed slice if this `HipByt` is backed by a
    /// borrow.
    ///
    /// # Errors
    ///
    /// Returns `Err(self)` if this `HipByt` is not borrowed.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// static SEQ: &[u8] = &[1 ,2, 3];
    /// let s = HipByt::borrowed(SEQ);
    /// let c = s.into_borrowed();
    /// assert_eq!(c, Ok(SEQ));
    /// assert!(std::ptr::eq(SEQ, c.unwrap()));
    /// ```
    pub const fn into_borrowed(self) -> Result<&'borrow [u8], Self> {
        if self.is_borrowed() {
            // SAFETY: repr is checked above
            Ok(unsafe { self.into_hipvec().into_borrowed_unchecked() })
        } else {
            Err(self)
        }
    }

    /// Returns the borrowed slice if this `HipByt` is actually borrowed, `None`
    /// otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// static SEQ: &[u8] = &[1 ,2, 3];
    /// let s = HipByt::borrowed(SEQ);
    /// let c: Option<&'static [u8]> = s.as_borrowed();
    /// assert_eq!(c, Some(SEQ));
    /// assert!(std::ptr::eq(SEQ, c.unwrap()));
    ///
    /// let s2 = HipByt::from(SEQ);
    /// assert!(s2.as_borrowed().is_none());
    /// ```
    #[inline]
    #[must_use]
    pub const fn as_borrowed(&self) -> Option<&'borrow [u8]> {
        self.0.as_borrowed()
    }

    /// Returns `true` if this `HipByt` is a shared heap-allocated byte sequence, `false` otherwise.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let s = HipByt::borrowed(b"hello");
    /// assert!(!s.is_allocated());
    ///
    /// let s = HipByt::from(b"hello");
    /// assert!(!s.is_allocated());
    ///
    /// let s = HipByt::from(b"hello".repeat(10));
    /// assert!(s.is_allocated());
    /// ```
    #[inline]
    #[must_use]
    pub const fn is_allocated(&self) -> bool {
        self.0.is_allocated()
    }

    // TODO doc
    #[must_use]
    pub const fn is_wide(&self) -> bool {
        self.0.is_wide()
    }

    // TODO doc
    #[must_use]
    pub const fn is_thin(&self) -> bool {
        self.0.is_thin()
    }

    /// Returns `true` if the representation is normalized.
    #[inline]
    #[must_use]
    pub const fn is_normalized(&self) -> bool {
        self.is_inline() || self.is_borrowed() || self.len() > Self::inline_capacity()
    }

    /// Returns the maximal length for inline byte sequence.
    #[inline]
    #[must_use]
    pub const fn inline_capacity() -> usize {
        HipVec::<'borrow, u8, B>::INLINE_CAP
    }

    /// Returns the total number of bytes the backend can hold.
    ///
    /// # Example
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let mut vec: Vec<u8> = Vec::with_capacity(42);
    /// vec.extend(0..30);
    /// let bytes = HipByt::from(vec);
    /// assert_eq!(bytes.len(), 30);
    /// assert_eq!(bytes.capacity(), 42);
    ///
    /// let start = bytes.slice(0..29);
    /// assert_eq!(bytes.capacity(), 42); // same backend, same capacity
    /// ```
    #[inline]
    #[must_use]
    pub const fn capacity(&self) -> usize {
        self.0.capacity()
    }

    /// Converts `self` into a [`Vec`] without clone or allocation if possible.
    ///
    /// # Errors
    ///
    /// Returns `Err(self)` if it is impossible to take ownership of the vector
    /// backing this `HipByt`.
    #[inline]
    pub fn into_vec(self) -> Result<Vec<u8>, Self> {
        self.0.into_vec().map_err(Self)
    }

    /// Makes the data owned, copying it if the data is actually borrowed.
    ///
    /// Returns a new `HipByt` consuming this one.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let v = vec![42; 42];
    /// let h = HipByt::borrowed(&v[..]);
    /// // drop(v); // err, v is borrowed
    /// let h = h.into_owned();
    /// drop(v); // ok
    /// assert_eq!(h, [42; 42]);
    /// ```
    #[inline]
    #[must_use]
    pub fn into_owned(self) -> HipByt<'static, B> {
        HipByt(self.0.into_owned())
    }

    /// Extracts a slice as its own `HipByt`.
    ///
    /// # Panics
    ///
    /// Panics if the range is invalid: out of bounds or not at char boundaries.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let a = HipByt::from(b"abc");
    /// assert_eq!(a.slice(0..2), HipByt::from(b"ab"));
    /// ```
    #[must_use]
    #[track_caller]
    pub fn slice(&self, range: impl RangeBounds<usize>) -> Self {
        Self(self.0.slice(range))
    }

    /// Returns a `HipByt` of a range of bytes in this `HipByt`, if the range is
    /// valid.
    ///
    /// # Errors
    ///
    /// This function will return an error if the range is invalid.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let a = HipByt::from(b"abc");
    /// assert_eq!(a.try_slice(0..2), Ok(HipByt::from(b"ab")));
    /// assert!(a.try_slice(0..4).is_err());
    /// ```
    pub fn try_slice(&self, range: impl RangeBounds<usize>) -> Result<Self, RangeError> {
        self.0.try_slice(range).map(Self)
    }

    /// Extracts a slice as its own `HipByt`.
    ///
    /// # Safety
    ///
    /// `range` must be equivalent to some `a..b` with `a <= b <= len`.
    ///
    /// Panics in debug mode. UB in release mode.
    #[must_use]
    #[inline]
    #[track_caller]
    pub unsafe fn slice_unchecked(&self, range: impl RangeBounds<usize>) -> Self {
        // SAFETY: range is checked by the caller
        Self(unsafe { self.0.slice_unchecked(range) })
    }

    /// Extracts a slice as its own `HipByt` based on the given subslice `&[u8]`.
    ///
    /// # Panics
    ///
    /// Panics if `slice` is not part of `self`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let a = HipByt::from(b"abc");
    /// let sl = &a[0..2];
    /// assert_eq!(a.slice_ref(sl), HipByt::from(b"ab"));
    /// ```
    #[must_use]
    #[track_caller]
    pub fn slice_ref(&self, slice: &[u8]) -> Self {
        let Some(result) = self.try_slice_ref(slice) else {
            panic!("slice {slice:p} is not a part of {self:p}")
        };
        result
    }

    /// Returns a slice as it own `HipByt` based on the given subslice `&[u8]`.
    ///
    /// # Errors
    ///
    /// Returns `None` if `slice` is not a part of `self`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let a = HipByt::from(b"abc");
    /// let sl = &a[0..2];
    /// assert_eq!(a.try_slice_ref(sl), Some(HipByt::from(b"ab")));
    /// assert!(a.try_slice_ref(b"z").is_none());
    /// ```
    #[must_use]
    pub fn try_slice_ref(&self, range: &[u8]) -> Option<Self> {
        self.0.slice_ref_copy(range).map(Self)
    }

    /// Returns a mutable handle to the underlying [`Vec`].
    ///
    /// This operation may reallocate a new vector if either:
    ///
    /// - the representation is not _allocated_ (i.e. _inline_ or _borrowed_),
    /// - the underlying buffer is shared.
    ///
    /// At the end, when the [`RefMut`] is dropped, the underlying
    /// representation will be owned and normalized. That is, if the actual
    /// required capacity is less than or equal to the maximal inline capacity,
    /// the representation is _inline_; otherwise, the representation is
    /// _allocated_.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hipstr::HipByt;
    /// let mut s = HipByt::borrowed(b"abc");
    /// {
    ///     let mut r = s.mutate();
    ///     r.extend_from_slice(b"def");
    ///     assert_eq!(r.as_slice(), b"abcdef");
    /// }
    /// assert_eq!(s, b"abcdef");
    /// ```
    #[inline]
    #[must_use]
    pub fn mutate(&mut self) -> RefMut<'_, 'borrow, B> {
        // TODO support bstr
        RefMut(self.0.mutate_copy())
    }

    /// Truncates this `HipByt`, removing all contents.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let mut s = HipByt::from(b"foo");
    ///
    /// s.clear();
    ///
    /// assert!(s.is_empty());
    /// assert_eq!(0, s.len());
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        self.0.clear();
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
    pub fn pop(&mut self) -> Option<u8> {
        self.0.pop()
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
        self.0.push_copy(value);
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
    #[doc(alias = "extend_from_slice", alias = "append")]
    pub fn push_slice(&mut self, addition: &[u8]) {
        self.0.extend_from_slice_copy(addition);
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
        Self(self.0.repeat_copy(n))
    }

    /// Returns the remaining spare capacity of the vector as a slice of
    /// `MaybeUninit<T>`.
    ///
    /// The returned slice can be used to fill the vector with data (e.g. by
    /// reading from a file) before marking the data as initialized using the
    /// [`set_len`] method.
    ///
    /// [`set_len`]: HipByt::set_len
    #[inline]
    pub fn spare_capacity_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        self.0.spare_capacity_mut()
    }

    /// Forces the length of the vector to `new_len`.
    ///
    /// Does not normalize!
    ///
    /// # Safety
    ///
    /// * If the repr is inline, `new_len` should be must be less than or equal to `INLINE_CAPACITY`.
    /// * If `new_len` is greater than the current length:
    ///   * The elements at `old_len..new_len` must be initialized.
    ///   * The vector should not be shared.
    pub unsafe fn set_len(&mut self, new_len: usize) {
        unsafe {
            self.0.set_len(new_len);
        }
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
        self.0.truncate(new_len);
    }

    /// Shrinks the capacity of the vector with a lower bound.
    ///
    /// The capacity will remain at least as large as the given bound and the
    /// actual length of the vector.
    ///
    /// No-op if the representation is not allocated.
    ///
    /// # Representation stability
    ///
    /// The representation may change to inline if the required capacity is
    /// smaller than the inline capacity.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hipstr::HipByt;
    /// let mut s = HipByt::with_capacity(100);
    /// s.shrink_to(4);
    /// assert_eq!(s.capacity(), HipByt::inline_capacity());
    /// assert!(s.is_inline());
    /// ```
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.0.shrink_to(min_capacity);
    }

    /// Shrinks the capacity of the vector as much as possible.
    ///
    /// The capacity will remain at least as large as the actual length of the
    /// vector.
    ///
    /// No-op if the representation is not allocated.
    ///
    /// # Representation stability
    ///
    /// The allocated representation may change to *inline* if the required
    /// capacity is smaller than the inline capacity.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hipstr::HipByt;
    /// let mut s = HipByt::with_capacity(100);
    /// s.push_slice(b"abc");
    /// s.shrink_to_fit();
    /// assert_eq!(s.capacity(), HipByt::inline_capacity());
    /// ```
    pub fn shrink_to_fit(&mut self) {
        self.0.shrink_to_fit();
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
    #[inline]
    #[must_use]
    pub fn to_ascii_lowercase(&self) -> Self {
        let mut other = self.clone();
        other.to_mut_slice().make_ascii_lowercase();
        other
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
    #[inline]
    pub fn make_ascii_lowercase(&mut self) {
        self.to_mut_slice().make_ascii_lowercase();
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
    #[inline]
    #[must_use]
    pub fn to_ascii_uppercase(&self) -> Self {
        let mut other = self.clone();
        other.to_mut_slice().make_ascii_uppercase();
        other
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
    #[inline]
    pub fn make_ascii_uppercase(&mut self) {
        self.to_mut_slice().make_ascii_uppercase();
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
        let new_len = slices.iter().map(|e| e.len()).sum();

        if new_len == 0 {
            return Self::new();
        }

        let mut new = Self::with_capacity(new_len);
        let dst = new.spare_capacity_mut();
        let dst_ptr = dst.as_mut_ptr().cast();
        let final_ptr = slices.iter().fold(dst_ptr, |dst_ptr, slice| {
            let len = slice.len();
            unsafe {
                ptr::copy_nonoverlapping(slice.as_ptr(), dst_ptr, len);
                dst_ptr.add(len)
            }
        });

        debug_assert_eq!(
            {
                #[expect(clippy::cast_sign_loss)]
                let diff_u = unsafe { final_ptr.offset_from(dst_ptr) } as usize;
                diff_u
            },
            new_len
        );

        unsafe { new.set_len(new_len) };

        // check end pointer
        debug_assert_eq!(final_ptr.cast_const(), new.as_slice().as_ptr_range().end);

        new
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
    pub fn concat<E, I>(slices: I) -> Self
    where
        E: AsRef<[u8]>,
        I: IntoIterator<Item = E>,
        I::IntoIter: Clone,
    {
        let slices = slices.into_iter();
        let new_len = slices.clone().map(|e| e.as_ref().len()).sum();
        if new_len == 0 {
            return Self::new();
        }

        let mut new = Self::with_capacity(new_len);
        let dst = new.spare_capacity_mut();
        let dst_ptr: *mut u8 = dst.as_mut_ptr().cast();

        // compute the final pointer
        let final_ptr = unsafe { dst_ptr.add(new_len) };

        let _ = slices.fold(dst_ptr, |dst_ptr, slice| {
            let slice = slice.as_ref();
            let len = slice.len();
            let end_ptr = unsafe { dst_ptr.add(len) };
            assert!(end_ptr <= final_ptr, "slices changed during concat");
            unsafe {
                ptr::copy_nonoverlapping(slice.as_ptr(), dst_ptr, len);
                end_ptr
            }
        });

        unsafe { new.set_len(new_len) };
        debug_assert_eq!(final_ptr.cast_const(), new.as_slice().as_ptr_range().end);

        new
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
        let slices_len = slices.len();
        if slices_len == 0 {
            return Self::new();
        }

        let sep = sep.as_ref();
        let sep_len = sep.len();

        // computes the final length
        let slices_sum: usize = slices.iter().copied().map(<[_]>::len).sum();
        let new_len = (slices_len - 1) * sep_len + slices_sum;
        if new_len == 0 {
            return Self::new();
        }

        let mut new = Self::with_capacity(new_len);
        let dst = new.spare_capacity_mut();
        let dst_ptr: *mut u8 = dst.as_mut_ptr().cast();

        // compute the final pointer
        let final_ptr = unsafe { dst_ptr.add(new_len) };

        let mut iter = slices.iter().copied();

        // get first slice
        // SAFETY: segments > 0 is checked above
        let slice = unsafe { iter.next().unwrap_unchecked() };
        let len = slice.len();
        // SAFETY: dst_ptr + len cannot overflow
        let end_ptr = unsafe { dst_ptr.add(len) };
        debug_assert!(end_ptr <= final_ptr, "slices changed during concat");
        unsafe {
            ptr::copy_nonoverlapping(slice.as_ptr(), dst_ptr, len);
        }

        // remainder
        let _ = iter.fold(end_ptr, |mut dst_ptr, slice| {
            let end_ptr = unsafe { dst_ptr.add(sep_len) };
            debug_assert!(end_ptr <= final_ptr, "slices changed during concat");
            unsafe {
                ptr::copy_nonoverlapping(sep.as_ptr(), dst_ptr, sep_len);
            }
            dst_ptr = end_ptr;

            let len = slice.len();
            let end_ptr = unsafe { dst_ptr.add(len) };
            debug_assert!(end_ptr <= final_ptr, "slices changed during concat");
            unsafe {
                ptr::copy_nonoverlapping(slice.as_ptr(), dst_ptr, len);
            }

            end_ptr
        });

        unsafe { new.set_len(new_len) };
        debug_assert_eq!(final_ptr.cast_const(), new.as_slice().as_ptr_range().end);

        new
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
    pub fn join<E, I>(slices: I, sep: impl AsRef<[u8]>) -> Self
    where
        E: AsRef<[u8]>,
        I: IntoIterator<Item = E>,
        I::IntoIter: Clone,
    {
        let mut iter = slices.into_iter();

        // computes the final length
        let (segments, segments_len) = iter.clone().fold((0, 0), |(count, length), e| {
            (count + 1, length + e.as_ref().len())
        });
        if segments == 0 {
            return Self::new();
        }
        let sep = sep.as_ref();
        let sep_len = sep.len();
        let new_len = (segments - 1) * sep_len + segments_len;

        let mut new = Self::with_capacity(new_len);
        let dst = new.spare_capacity_mut();
        let dst_ptr: *mut u8 = dst.as_mut_ptr().cast();

        // computes the final pointer
        // SAFETY: `new_len` is the length of raw
        let final_ptr = unsafe { dst_ptr.add(new_len) };

        if let Some(first) = iter.next() {
            let first = first.as_ref();
            let len = first.len();

            let end_ptr = unsafe { dst_ptr.add(first.len()) };
            assert!(end_ptr <= final_ptr, "slices changed during concat");
            unsafe {
                ptr::copy_nonoverlapping(first.as_ptr(), dst_ptr, len);
            }

            let _ = iter.fold(end_ptr, |mut dst_ptr, slice| {
                let end_ptr = unsafe { dst_ptr.add(sep_len) };
                assert!(end_ptr <= final_ptr, "slices changed during concat");
                unsafe {
                    ptr::copy_nonoverlapping(sep.as_ptr(), dst_ptr, sep_len);
                }
                dst_ptr = end_ptr;

                let slice = slice.as_ref();
                let len = slice.len();
                let end_ptr = unsafe { dst_ptr.add(len) };
                assert!(end_ptr <= final_ptr, "slices changed during concat");
                unsafe {
                    ptr::copy_nonoverlapping(slice.as_ptr(), dst_ptr, len);
                }
                end_ptr
            });
        }

        // SAFETY: everything is initialized
        unsafe { new.set_len(new_len) };
        debug_assert_eq!(final_ptr.cast_const(), new.as_slice().as_ptr_range().end);

        new
    }
}

impl<B> HipByt<'static, B>
where
    B: Backend,
{
    /// Creates a new `HipByt` from a `'static` slice without copying the slice.
    ///
    /// Handy shortcut to make a `HipByt<'static, _>` out of a `&'static [u8]`.
    ///
    /// # Representation
    ///
    /// The created `HipByt` is _borrowed_.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let b = HipByt::from_static(b"hello\0");
    /// assert_eq!(b.len(), 6);
    /// ```
    #[inline]
    #[must_use]
    pub const fn from_static(bytes: &'static [u8]) -> Self {
        Self::borrowed(bytes)
    }
}

impl<B> Deref for HipByt<'_, B>
where
    B: Backend,
{
    type Target = Slice;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

impl<B> Borrow<[u8]> for HipByt<'_, B>
where
    B: Backend,
{
    #[inline]
    fn borrow(&self) -> &[u8] {
        self.as_slice()
    }
}

impl<B> Hash for HipByt<'_, B>
where
    B: Backend,
{
    #[inline]
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.as_slice().hash(state);
    }
}

// Formatting

impl<B> fmt::Debug for HipByt<'_, B>
where
    B: Backend,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_slice().fmt(f)
    }
}

/// Slice error kinds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SliceErrorKind {
    /// Start index should be less or equal to the end index
    StartGreaterThanEnd,

    /// Start index out of bounds
    StartOutOfBounds,

    /// End index out of bounds
    EndOutOfBounds,
}

/// A wrapper type for a mutably borrowed vector out of a [`HipByt`].
pub struct RefMut<'a, 'borrow, B: Backend>(pub(crate) crate::vecs::hip::RefMut<'a, 'borrow, u8, B>);

impl<B: Backend> RefMut<'_, '_, B> {
    #[cfg(feature = "bstr")]
    pub fn push_str(&mut self, value: &str) {
        self.0.extend_from_slice_copy(value.as_bytes());
    }

    #[cfg(feature = "bstr")]
    pub fn push_char(&mut self, value: char) {
        let mut buf = [0u8; 4];
        let s = value.encode_utf8(&mut buf);
        self.0.extend_from_slice_copy(s.as_bytes());
    }

    #[cfg(feature = "bstr")]
    pub fn push_byte(&mut self, value: u8) {
        self.0.push(value);
    }

    #[doc(alias = "push_slice", alias = "push_bytes")]
    pub fn extend_from_slice(&mut self, addition: &[u8]) {
        self.0.extend_from_slice_copy(addition);
    }

    #[cfg(feature = "bstr")]
    pub fn pop_char(&mut self) -> Option<char> {
        let (ch, width) = ::bstr::decode_last_utf8(self.as_slice());
        if width == 0 {
            return None;
        }

        let new_len = self.len() - width;
        // SAFETY: length decreases
        unsafe {
            self.0.set_len(new_len);
        }
        Some(ch.unwrap_or(core::char::REPLACEMENT_CHARACTER))
    }

    #[cfg(feature = "bstr")]
    pub const fn pop_byte(&mut self) -> Option<u8> {
        self.0.pop()
    }
}

impl<'a, 'b, B> Deref for RefMut<'a, 'b, B>
where
    B: Backend,
{
    type Target = crate::vecs::hip::RefMut<'a, 'b, u8, B>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<B> DerefMut for RefMut<'_, '_, B>
where
    B: Backend,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}
