//! The generic type behind every public alias: [`Hip<E, R>`].
//!
//! `E` is the [encoding](super::enc) (bytes, UTF-8, OS string, path) and `R`
//! the concrete [representation](super::repr) (`Wide<'a, B>`,
//! `Small<'a, B>` or `Tiny<B>`). Taking the concrete representation,
//! rather than a layout marker plus a lifetime, keeps the type covariant in
//! the borrow lifetime.
//!
//! This module holds what is written once for all encodings and sizes:
//! constructors, accessors, conversions with the std owned type, mutation
//! through a guard, and the comparison/hash/format traits.

use alloc::borrow::Cow;
use core::cmp::Ordering;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::mem::ManuallyDrop;
use core::ops::{Deref, DerefMut};

use super::backend::Backend;
use super::enc::Encoding;
use super::repr::{Kind, Repr, Small, Tiny, Wide};

/// Copy-on-write sequence of bytes with encoding `E` stored as `R`.
///
/// See the crate aliases ([`HipStr`](super::HipStr), [`SmallStr`](super::SmallStr),
/// [`TinyStr`](super::TinyStr), …) for documentation and examples.
#[repr(transparent)]
pub struct Hip<E: Encoding, R> {
    repr: R,
    enc: PhantomData<E>,
}

// ----- constructors that must be `const`, per representation -----

impl<'a, E: Encoding, B: Backend> Hip<E, Wide<'a, B>> {
    /// Creates an empty `HipStr`.
    ///
    /// Function provided for `String::new` replacement.
    ///
    /// # Representation
    ///
    /// ⚠️ Warning! The used representation of the empty string is unspecified.
    /// It may be *borrowed* or *inlined* but will never be allocated.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let s = HipStr::new();
    /// ```
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self::from_repr_const(Wide::inline_copy(E::EMPTY))
    }

    pub(crate) const fn from_repr_const(repr: Wide<'a, B>) -> Self {
        Self {
            repr,
            enc: PhantomData,
        }
    }
}

impl<'a, E: Encoding, B: Backend> Hip<E, Small<'a, B>> {
    /// Creates an empty `HipStr`.
    ///
    /// Function provided for `String::new` replacement.
    ///
    /// # Representation
    ///
    /// ⚠️ Warning! The used representation of the empty string is unspecified.
    /// It may be *borrowed* or *inlined* but will never be allocated.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let s = HipStr::new();
    /// ```
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self::from_repr_const(Small::inline_copy(E::EMPTY))
    }

    pub(crate) const fn from_repr_const(repr: Small<'a, B>) -> Self {
        Self {
            repr,
            enc: PhantomData,
        }
    }
}

impl<E: Encoding, B: Backend> Hip<E, Tiny<B>> {
    /// Creates an empty `HipStr`.
    ///
    /// Function provided for `String::new` replacement.
    ///
    /// # Representation
    ///
    /// ⚠️ Warning! The used representation of the empty string is unspecified.
    /// It may be *borrowed* or *inlined* but will never be allocated.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let s = HipStr::new();
    /// ```
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self::from_repr_const(Tiny::inline_copy(E::EMPTY))
    }

    pub(crate) const fn from_repr_const(repr: Tiny<B>) -> Self {
        Self {
            repr,
            enc: PhantomData,
        }
    }
}

// ----- encoding-agnostic accessors, `const`, per representation -----
//
// Written once by a macro rather than generically over `R`: a `const fn`
// cannot call trait methods on stable Rust, so these call each
// representation's own `const` methods.

macro_rules! impl_const_accessors {
    ($([$($lt:lifetime)?] $repr:ty),* $(,)?) => {$(
        impl<$($lt,)? E: Encoding, B: Backend> Hip<E, $repr> {
            /// Returns the length of this `HipStr`, in bytes, not [`char`]s or
            /// graphemes. In other words, it might not be what a human considers the
            /// length of the string.
            ///
            /// # Examples
            ///
            /// Basic usage:
            ///
            /// ```
            /// # use hipstr::HipStr;
            /// let a = HipStr::from("(c)");
            /// assert_eq!(a.len(), 3);
            ///
            /// let b = HipStr::from("®");
            /// assert_eq!(b.len(), 2);
            /// assert_eq!(b.chars().count(), 1);
            /// ```
            #[inline]
            #[must_use]
            pub const fn len(&self) -> usize {
                // C strings: without the NUL terminator, like `CStr::count_bytes`
                self.repr.len() - E::TERMINATOR
            }

            /// Returns `true` if this `HipStr` has a length of zero, and `false` otherwise.
            ///
            /// # Examples
            ///
            /// Basic usage:
            ///
            /// ```
            /// # use hipstr::HipStr;
            /// let a = HipStr::new();
            /// assert!(a.is_empty());
            ///
            /// let b = HipStr::borrowed("ab");
            /// assert!(!b.is_empty());
            /// ```
            #[inline]
            #[must_use]
            pub const fn is_empty(&self) -> bool {
                self.repr.len() == E::TERMINATOR
            }

            /// Extracts a raw pointer out of the `HipStr`.
            ///
            /// As strings are ultimately sequence of bytes, the raw pointer points to a
            /// [`u8`]. This pointer will be pointing to the first byte of the string.
            ///
            /// It is your responsibility to make sure that:
            ///
            /// - This `HipStr` outlives the pointer this function returns.
            ///
            /// - This `HipStr` is not modified in another way before the use of the
            ///   pointer. Modifying the byte sequence may change representation or
            ///   reallocate, which would invalid the returned pointer.
            ///
            /// - The returned pointer is never written to. If you need to mutate the
            ///   contents of the string slice, use [`as_mut_ptr`].
            ///
            /// [`as_mut_ptr`]: Self::as_mut_ptr
            ///
            /// # Examples
            ///
            /// ```
            /// # use hipstr::HipStr;
            /// let s = HipStr::from("Hello");
            /// let ptr = s.as_ptr();
            /// ```
            #[inline]
            #[must_use]
            pub const fn as_ptr(&self) -> *const u8 {
                self.repr.as_slice().as_ptr()
            }

            /// Returns `true` if this `HipStr` uses the inline representation, `false` otherwise.
            ///
            /// # Examples
            ///
            /// Basic usage:
            ///
            /// ```
            /// # use hipstr::HipStr;
            /// let s = HipStr::borrowed("hello");
            /// assert!(!s.is_inline());
            ///
            /// let s = HipStr::from("hello");
            /// assert!(s.is_inline());
            ///
            /// let s = HipStr::from("hello".repeat(10));
            /// assert!(!s.is_inline());
            /// ```
            #[inline]
            #[must_use]
            pub const fn is_inline(&self) -> bool {
                self.repr.is_inline()
            }

            /// Returns `true` if this `HipStr` is a string borrow, `false` otherwise.
            ///
            /// # Examples
            ///
            /// Basic usage:
            ///
            /// ```
            /// # use hipstr::HipStr;
            /// let s = HipStr::borrowed("hello");
            /// assert!(s.is_borrowed());
            ///
            /// let s = HipStr::from("hello");
            /// assert!(!s.is_borrowed());
            ///
            /// let s = HipStr::from("hello".repeat(10));
            /// assert!(!s.is_borrowed());
            /// ```
            #[inline]
            #[must_use]
            pub const fn is_borrowed(&self) -> bool {
                self.repr.is_borrowed()
            }

            /// Returns `true` if this `HipStr` is a shared heap-allocated string, `false` otherwise.
            ///
            /// # Examples
            ///
            /// Basic usage:
            ///
            /// ```
            /// # use hipstr::HipStr;
            /// let s = HipStr::borrowed("hello");
            /// assert!(!s.is_allocated());
            ///
            /// let s = HipStr::from("hello");
            /// assert!(!s.is_allocated());
            ///
            /// let s = HipStr::from("hello".repeat(10));
            /// assert!(s.is_allocated());
            /// ```
            #[inline]
            #[must_use]
            pub const fn is_allocated(&self) -> bool {
                self.repr.is_heap()
            }

            /// Whether the value uses its preferred representation: not
            /// allocated if it fits inline.
            #[inline]
            #[must_use]
            pub const fn is_normalized(&self) -> bool {
                !self.repr.is_heap()
                    || self.repr.len() > <$repr as Repr<'_>>::INLINE_CAPACITY
            }
        }
    )*};
}

impl_const_accessors!(['a] Wide<'a, B>, ['a] Small<'a, B>, [] Tiny<B>);

/// Implements the `const` typed accessors of an encoding whose byte
/// conversion is `const` (bytes and UTF-8), for every representation.
///
/// `$from` converts `&[u8]` to `&$slice` (unsafe, called on valid bytes);
/// `$to` converts `&$slice` to `&[u8]`.
macro_rules! impl_const_typed_accessors {
    ($enc:ty, $slice:ty, |$b:ident| $from:expr, |$v:ident| $to:expr) => {
        $crate::hip::impl_const_typed_accessors!(@one $enc, $slice, |$b| $from, |$v| $to, ['a] $crate::repr::Wide<'a, B>, 'a);
        $crate::hip::impl_const_typed_accessors!(@one $enc, $slice, |$b| $from, |$v| $to, ['a] $crate::repr::Small<'a, B>, 'a);
        $crate::hip::impl_const_typed_accessors!(@one $enc, $slice, |$b| $from, |$v| $to, ['a] $crate::repr::Tiny<B>, 'a);
    };
    (@one $enc:ty, $slice:ty, |$b:ident| $from:expr, |$v:ident| $to:expr, [$($lt:lifetime)?] $repr:ty, $blt:lifetime) => {
        // the conversion is safe for bytes (identity), unsafe otherwise
        #[allow(unused_unsafe)]
        impl<$($lt,)? B: $crate::backend::Backend> $crate::hip::Hip<$enc, $repr> {
            /// Returns the borrowed string slice if this `HipStr` is actually borrowed,
            /// `None` otherwise.
            ///
            /// # Examples
            ///
            /// ```
            /// # use hipstr::HipStr;
            /// static S: &str = "abc";
            /// let s = HipStr::borrowed(S);
            /// let c: Option<&'static str> = s.as_borrowed();
            /// assert_eq!(c, Some(S));
            /// assert!(std::ptr::eq(S, c.unwrap()));
            ///
            /// let s2 = HipStr::from(S);
            /// assert!(s2.as_borrowed().is_none());
            /// ```
            #[inline]
            #[must_use]
            pub const fn as_borrowed(&self) -> Option<&$blt $slice> {
                match self.repr().borrowed_slice() {
                    // SAFETY: type invariant
                    Some($b) => Some(unsafe { $from }),
                    None => None,
                }
            }

            /// Converts `self` into a string slice with the `'borrow` lifetime if this
            /// `HipStr` is backed by a borrow.
            ///
            /// # Errors
            ///
            /// Returns `Err(self)` if this `HipStr` is not a borrow.
            ///
            /// # Examples
            ///
            /// Basic usage:
            ///
            /// ```
            /// # use hipstr::HipStr;
            /// let borrowed = "hipstr";
            /// let s = HipStr::borrowed(borrowed);
            /// let c = s.into_borrowed();
            /// assert_eq!(c, Ok(borrowed));
            /// assert!(std::ptr::eq(borrowed, c.unwrap()));
            /// ```
            #[inline]
            pub const fn into_borrowed(self) -> Result<&$blt $slice, Self> {
                match self.repr().borrowed_slice() {
                    Some($b) => {
                        core::mem::forget(self);
                        // SAFETY: type invariant
                        Ok(unsafe { $from })
                    }
                    None => Err(self),
                }
            }

            /// Copies the value inline, in a `const` context too.
            ///
            /// # Panics
            ///
            /// Panics if the value is longer than the inline capacity.
            #[inline]
            #[must_use]
            pub const fn inline($v: &$slice) -> Self {
                Self::try_inline($v).expect("value too long to be inlined")
            }

            /// Copies the value inline, in a `const` context too; `None` if
            /// it is longer than the inline capacity.
            #[inline]
            #[must_use]
            pub const fn try_inline($v: &$slice) -> Option<Self> {
                let bytes: &[u8] = $to;
                // no `match` on an `Option` holding a value with drop glue:
                // const evaluation cannot prove the `None` arm drops nothing
                if bytes.len() <= <$repr as $crate::repr::Repr<'_>>::INLINE_CAPACITY {
                    Some(Self::from_repr_const(<$repr>::inline_copy(bytes)))
                } else {
                    None
                }
            }

            #[allow(dead_code, reason = "unused for bytes")]
            pub(crate) const fn as_typed(&self) -> &$slice {
                let $b = self.repr().as_slice();
                // SAFETY: type invariant
                unsafe { $from }
            }
        }
    };
}
pub(crate) use impl_const_typed_accessors;

// ----- everything else, once -----

impl<'a, E: Encoding, R: Repr<'a>> Hip<E, R> {
    /// # Safety
    ///
    /// The bytes must satisfy `E`'s invariant.
    #[inline]
    pub(crate) const unsafe fn from_repr(repr: R) -> Self {
        Self {
            repr,
            enc: PhantomData,
        }
    }

    #[inline]
    pub(crate) const fn repr(&self) -> &R {
        &self.repr
    }

    /// # Safety
    ///
    /// The caller must preserve `E`'s invariant.
    #[inline]
    pub(crate) const unsafe fn repr_mut(&mut self) -> &mut R {
        &mut self.repr
    }

    #[inline]
    pub(crate) const fn into_repr(self) -> R {
        let this = core::mem::ManuallyDrop::new(self);
        // SAFETY: `Hip` is `repr(transparent)` over `R` (the other field is a
        // ZST); the repr is moved out exactly once and `self` is forgotten
        unsafe { core::ptr::read((&raw const this).cast::<R>()) }
    }

    /// The borrowed value, with its full lifetime, if borrowed.
    #[inline]
    pub(crate) fn borrowed_inner(&self) -> Option<&'a E::Slice> {
        self.repr
            .as_borrowed()
            // SAFETY: type invariant
            .map(|bytes| unsafe { E::from_bytes_unchecked(bytes) })
    }

    #[inline]
    pub(crate) fn bytes(&self) -> &[u8] {
        self.repr.as_slice()
    }

    /// The value as its std borrowed form.
    #[inline]
    pub(crate) fn as_inner(&self) -> &E::Slice {
        // SAFETY: type invariant
        unsafe { E::from_bytes_unchecked(self.bytes()) }
    }

    /// Copies a borrowed value (inline when it fits).
    #[inline]
    pub(crate) fn from_inner(value: &E::Slice) -> Self {
        // SAFETY: bytes of a valid `E::Slice`
        unsafe { Self::from_repr(R::from_slice(E::as_bytes(value))) }
    }

    /// Borrows a value when the representation supports it, copies otherwise.
    #[inline]
    pub(crate) fn from_inner_borrowed(value: &'a E::Slice) -> Self {
        // SAFETY: bytes of a valid `E::Slice`
        unsafe { Self::from_repr(R::from_borrowed(E::as_bytes(value))) }
    }

    /// Takes an owned std value, adopting its buffer when it does not fit inline.
    #[inline]
    pub(crate) fn from_owned(value: E::Owned) -> Self {
        // SAFETY: bytes of a valid `E::Owned`
        unsafe { Self::from_repr(R::from_vec(E::owned_into_bytes(value))) }
    }

    /// Converts into the std owned form, in O(1) when the value uniquely owns
    /// an adopted buffer, by copying otherwise.
    #[inline]
    pub(crate) fn into_owned_std(self) -> E::Owned {
        // SAFETY: type invariant
        unsafe { E::owned_from_bytes_unchecked(self.repr.into_vec()) }
    }

    /// Creates a new `HipStr` with the given capacity.
    ///
    /// The final capacity depends on the representation and is not guaranteed
    /// to be exact. However, the returned `HipStr` will be able to hold at
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
    /// # use hipstr::HipStr;
    /// let mut s = HipStr::with_capacity(42);
    /// for _ in 0..42 {
    ///     s.push('*');
    /// }
    /// assert_eq!(s, "*".repeat(42));
    /// ```
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        let mut repr = R::from_slice(E::EMPTY);
        repr.reserve(capacity);
        // SAFETY: empty
        unsafe { Self::from_repr(repr) }
    }

    /// Maximal length stored inline.
    #[inline]
    #[must_use]
    pub const fn inline_capacity() -> usize {
        // C strings: without the NUL terminator
        R::INLINE_CAPACITY - E::TERMINATOR
    }

    /// Capacity of the owned storage: the inline capacity, the heap capacity,
    /// or the length if borrowed or shared (writing then needs a copy).
    #[inline]
    #[must_use]
    pub fn capacity(&self) -> usize {
        let raw = if self.repr.is_unique() {
            self.repr.capacity()
        } else {
            self.repr.len()
        };
        // C strings: without the NUL terminator
        raw.saturating_sub(E::TERMINATOR)
    }

    /// Makes the string owned, copying the data if it is actually borrowed.
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let s: String = ('a'..'z').collect();
    /// let h = HipStr::borrowed(&s[..]);
    /// // drop(s); // err, s is borrowed
    /// let h = h.into_owned();
    /// drop(s); // ok
    /// assert_eq!(h, ('a'..'z').collect::<String>());
    /// ```
    #[inline]
    #[must_use]
    pub fn into_owned(self) -> Hip<E, R::Owned> {
        // SAFETY: same bytes
        unsafe { Hip::from_repr(self.repr.into_owned()) }
    }

    /// Returns a mutable handle to the underlying `String`.
    ///
    /// This operation may reallocate a new string if either:
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
    /// # use hipstr::HipStr;
    /// let mut s = HipStr::borrowed("abc");
    /// {
    ///     let mut r = s.mutate();
    ///     r.push_str("def");
    ///     assert_eq!(r.as_str(), "abcdef");
    /// }
    /// assert_eq!(s, "abcdef");
    /// ```
    #[inline]
    pub fn mutate(&mut self) -> RefMut<'_, 'a, E, R> {
        // placeholder valid for `E` (observable if the guard is leaked)
        let repr = core::mem::replace(&mut self.repr, R::from_slice(E::EMPTY));
        // SAFETY: type invariant
        let owned = unsafe { E::owned_from_bytes_unchecked(repr.into_vec()) };
        RefMut {
            target: self,
            owned: ManuallyDrop::new(owned),
            borrow: PhantomData,
        }
    }

    /// Raw mutable pointer to the bytes, if inline or uniquely owned (no copy).
    #[inline]
    pub fn as_mut_ptr(&mut self) -> Option<*mut u8> {
        if self.repr.is_unique() {
            // SAFETY: unique: `reserve(0)` does not copy nor reallocate
            Some(unsafe { self.as_mut_ptr_unchecked() })
        } else {
            None
        }
    }

    /// Raw mutable pointer to the bytes.
    ///
    /// # Safety
    ///
    /// The value must be inline or uniquely owned (see
    /// [`as_mut_ptr`](Self::as_mut_ptr)), and writes must preserve `E`'s
    /// invariant.
    #[inline]
    pub unsafe fn as_mut_ptr_unchecked(&mut self) -> *mut u8 {
        debug_assert!(self.repr.is_unique());
        self.repr.reserve(0);
        // SAFETY: unique after `reserve`
        unsafe { self.repr.as_mut_ptr() }
    }

    /// Truncates to `len` bytes, without checking `E`'s invariant.
    ///
    /// # Safety
    ///
    /// The truncated bytes must satisfy `E`'s invariant.
    #[inline]
    pub(crate) unsafe fn truncate_bytes(&mut self, len: usize) {
        self.repr.truncate(len);
    }

    /// Appends bytes, without checking `E`'s invariant.
    ///
    /// # Safety
    ///
    /// The result must satisfy `E`'s invariant.
    #[inline]
    pub(crate) unsafe fn push_bytes(&mut self, bytes: &[u8]) {
        self.repr.extend_from_slice(bytes);
    }

    /// Truncates this `HipStr`, removing all contents.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let mut s = HipStr::from("foo");
    ///
    /// s.clear();
    ///
    /// assert!(s.is_empty());
    /// assert_eq!(0, s.len());
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        self.repr = R::from_slice(E::EMPTY);
    }

    /// Shrinks the capacity of the string as much as possible.
    ///
    /// The capacity will remain at least as large as the actual length of the
    /// string.
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
    /// # use hipstr::HipStr;
    /// let mut s = HipStr::with_capacity(100);
    /// s.push_str("abc");
    /// s.shrink_to_fit();
    /// assert_eq!(s.capacity(), HipStr::inline_capacity());
    /// ```
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.shrink_to(0);
    }

    /// Shrinks the capacity of the string with a lower bound.
    ///
    /// The capacity will remain at least as large as the given lower bound and
    /// the actual length of the string.
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
    /// # use hipstr::HipStr;
    /// let mut s = HipStr::with_capacity(100);
    /// s.shrink_to(4);
    /// assert_eq!(s.capacity(), HipStr::inline_capacity());
    /// ```
    pub fn shrink_to(&mut self, min_capacity: usize) {
        if !matches!(self.repr.kind(), Kind::Heap(_)) {
            return;
        }
        let target = min_capacity
            .saturating_add(E::TERMINATOR)
            .max(self.repr.len());
        // raw capacity of the (possibly shared) buffer
        if self.repr.capacity() > target {
            let mut repr = R::new();
            repr.reserve(target);
            repr.extend_from_slice(self.bytes());
            self.repr = repr;
        }
    }
}

impl<'a, E: Encoding, R: Repr<'a>> Hip<E, R> {
    /// Reserves capacity for at least `additional` more bytes, making the
    /// value uniquely owned (copying it first if borrowed or shared).
    ///
    /// Like `Vec::reserve`, the capacity grows geometrically.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipStr;
    /// let mut s = HipStr::borrowed("borrowed");
    /// s.reserve(100);
    /// assert!(!s.is_borrowed());
    /// assert!(s.capacity() >= 108);
    /// ```
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        self.repr.reserve(additional);
    }

    /// Reserves capacity for at least `additional` more bytes, making the
    /// value uniquely owned.
    ///
    /// Like `Vec::reserve_exact`, it does not deliberately over-allocate, but
    /// the representation may still round the capacity up.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows.
    #[inline]
    pub fn reserve_exact(&mut self, additional: usize) {
        crate::thin::unwrap_or_oom(self.repr.try_reserve(additional));
    }

    /// Tries to reserve capacity for at least `additional` more bytes,
    /// making the value uniquely owned.
    ///
    /// # Errors
    ///
    /// Returns an error if the capacity overflows or the allocator fails;
    /// the value is then unchanged.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let mut b = HipByt::from(b"abc");
    /// assert!(b.try_reserve(10).is_ok());
    /// assert!(b.try_reserve(usize::MAX).is_err());
    /// assert_eq!(b, b"abc");
    /// ```
    #[inline]
    pub fn try_reserve(
        &mut self,
        additional: usize,
    ) -> Result<(), alloc::collections::TryReserveError> {
        self.repr
            .try_reserve(additional)
            .map_err(crate::thin::TryReserveError::into_std)
    }

    /// Tries to reserve capacity for at least `additional` more bytes
    /// (see [`reserve_exact`](Self::reserve_exact)).
    ///
    /// # Errors
    ///
    /// Returns an error if the capacity overflows or the allocator fails;
    /// the value is then unchanged.
    #[inline]
    pub fn try_reserve_exact(
        &mut self,
        additional: usize,
    ) -> Result<(), alloc::collections::TryReserveError> {
        self.try_reserve(additional)
    }

    /// Mutable bytes, copying first if borrowed or shared.
    ///
    /// # Safety
    ///
    /// Writes must preserve `E`'s invariant.
    #[inline]
    pub(crate) unsafe fn bytes_mut(&mut self) -> &mut [u8] {
        self.repr.to_mut_slice()
    }

    /// Replaces the bytes in `range` by `with`.
    ///
    /// Leaves the value as is (possibly borrowed or shared) when nothing
    /// changes.
    ///
    /// # Safety
    ///
    /// `range` must be in bounds and the result must satisfy `E`'s invariant.
    pub(crate) unsafe fn splice_bytes(&mut self, range: core::ops::Range<usize>, with: &[u8]) {
        let len = self.repr.len();
        let core::ops::Range { start, end } = range;
        debug_assert!(start <= end && end <= len);
        if start == end && with.is_empty() {
            return;
        }
        if end == len {
            self.repr.truncate(start);
            self.repr.extend_from_slice(with);
            return;
        }
        let new_len = len - (end - start) + with.len();
        if new_len > len {
            // fill first, so that every byte up to `new_len` is initialized
            self.repr.resize(new_len, 0);
        }
        let bytes = self.repr.to_mut_slice();
        bytes.copy_within(end..len, start + with.len());
        bytes[start..start + with.len()].copy_from_slice(with);
        self.repr.truncate(new_len);
    }
}

/// Mutation guard returned by [`Hip::mutate`].
///
/// Dereferences to the std owned form; writes back on drop.
pub struct RefMut<'h, 'a, E: Encoding, R: Repr<'a>> {
    target: &'h mut Hip<E, R>,
    /// Taken back on drop only.
    owned: ManuallyDrop<E::Owned>,
    borrow: PhantomData<&'a ()>,
}

impl<'a, E: Encoding, R: Repr<'a>> Drop for RefMut<'_, 'a, E, R> {
    fn drop(&mut self) {
        // SAFETY: not used afterwards
        let owned = unsafe { ManuallyDrop::take(&mut self.owned) };
        *self.target = Hip::from_owned(owned);
    }
}

impl<'a, E: Encoding, R: Repr<'a>> fmt::Debug for RefMut<'_, 'a, E, R>
where
    E::Owned: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<'a, E: Encoding, R: Repr<'a>> Deref for RefMut<'_, 'a, E, R> {
    type Target = E::Owned;

    #[inline]
    fn deref(&self) -> &E::Owned {
        &self.owned
    }
}

impl<'a, E: Encoding, R: Repr<'a>> DerefMut for RefMut<'_, 'a, E, R> {
    #[inline]
    fn deref_mut(&mut self) -> &mut E::Owned {
        &mut self.owned
    }
}

// ----- traits, once -----

impl<'a, E: Encoding, R: Repr<'a>> Default for Hip<E, R> {
    #[inline]
    fn default() -> Self {
        // SAFETY: empty
        unsafe { Self::from_repr(R::from_slice(E::EMPTY)) }
    }
}

impl<'a, E: Encoding, R: Repr<'a>> Clone for Hip<E, R> {
    #[inline]
    fn clone(&self) -> Self {
        // SAFETY: same bytes
        unsafe { Self::from_repr(self.repr.clone()) }
    }
}

impl<'a, E: Encoding, R: Repr<'a>> Deref for Hip<E, R> {
    type Target = E::Slice;

    #[inline]
    fn deref(&self) -> &E::Slice {
        self.as_inner()
    }
}

impl<'a, E: Encoding, R: Repr<'a>> AsRef<E::Slice> for Hip<E, R> {
    #[inline]
    fn as_ref(&self) -> &E::Slice {
        self.as_inner()
    }
}

impl<'a, E: Encoding, R: Repr<'a>> Hash for Hip<E, R>
where
    E::Slice: Hash,
{
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_inner().hash(state);
    }
}

impl<'a, E: Encoding, R: Repr<'a>> fmt::Debug for Hip<E, R>
where
    E::Slice: fmt::Debug,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_inner().fmt(f)
    }
}

impl<'a, 'b, E: Encoding, R1: Repr<'a>, R2: Repr<'b>> PartialEq<Hip<E, R2>> for Hip<E, R1>
where
    E::Slice: PartialEq,
{
    #[inline]
    fn eq(&self, other: &Hip<E, R2>) -> bool {
        let (a, b) = (self.bytes(), other.bytes());
        // shared or borrowed from the same storage: equal without comparing
        // (identical bytes, so equal for every encoding, paths included)
        (a.len() == b.len() && core::ptr::eq(a.as_ptr(), b.as_ptr()))
            || self.as_inner() == other.as_inner()
    }
}

impl<'a, E: Encoding, R: Repr<'a>> Eq for Hip<E, R> where E::Slice: Eq {}

impl<'a, 'b, E: Encoding, R1: Repr<'a>, R2: Repr<'b>> PartialOrd<Hip<E, R2>> for Hip<E, R1>
where
    E::Slice: PartialOrd,
{
    #[inline]
    fn partial_cmp(&self, other: &Hip<E, R2>) -> Option<Ordering> {
        self.as_inner().partial_cmp(other.as_inner())
    }
}

impl<'a, E: Encoding, R: Repr<'a>> Ord for Hip<E, R>
where
    E::Slice: Ord,
{
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_inner().cmp(other.as_inner())
    }
}

impl<'a, E: Encoding, R: Repr<'a>> From<&E::Slice> for Hip<E, R> {
    /// Copies the value (inline when it fits); see `borrowed` to borrow it.
    #[inline]
    fn from(value: &E::Slice) -> Self {
        Self::from_inner(value)
    }
}

impl<'a, E: Encoding, R: Repr<'a>> From<Cow<'a, E::Slice>> for Hip<E, R>
where
    E::Slice: alloc::borrow::ToOwned<Owned = E::Owned>,
{
    /// Borrows `Cow::Borrowed` (copies if the representation cannot borrow),
    /// adopts `Cow::Owned`.
    #[inline]
    fn from(value: Cow<'a, E::Slice>) -> Self {
        match value {
            Cow::Borrowed(b) => Self::from_inner_borrowed(b),
            Cow::Owned(o) => Self::from_owned(o),
        }
    }
}

impl<'a, E: Encoding, R: Repr<'a>> From<Hip<E, R>> for Cow<'a, E::Slice>
where
    E::Slice: alloc::borrow::ToOwned<Owned = E::Owned>,
{
    /// Borrowed values stay borrowed; others convert to the owned form.
    #[inline]
    fn from(value: Hip<E, R>) -> Self {
        match value.borrowed_inner() {
            Some(b) => Cow::Borrowed(b),
            None => Cow::Owned(value.into_owned_std()),
        }
    }
}
