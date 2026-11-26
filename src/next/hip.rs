//! The generic type behind every public alias: [`Hip<E, R>`].
//!
//! `E` is the [encoding](super::enc) (bytes, UTF-8, OS string, path) and `R`
//! the concrete [representation](super::repr) (`Wide<'a, u8, B>`,
//! `Small<'a, u8, B>` or `Tiny<u8, B>`). Taking the concrete representation,
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

impl<'a, E: Encoding, B: Backend> Hip<E, Wide<'a, u8, B>> {
    /// Creates an empty value, without allocation.
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self::from_repr_const(Wide::new())
    }

    pub(crate) const fn from_repr_const(repr: Wide<'a, u8, B>) -> Self {
        Self {
            repr,
            enc: PhantomData,
        }
    }
}

impl<'a, E: Encoding, B: Backend> Hip<E, Small<'a, u8, B>> {
    /// Creates an empty value, without allocation.
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self::from_repr_const(Small::new())
    }

    pub(crate) const fn from_repr_const(repr: Small<'a, u8, B>) -> Self {
        Self {
            repr,
            enc: PhantomData,
        }
    }
}

impl<E: Encoding, B: Backend> Hip<E, Tiny<u8, B>> {
    /// Creates an empty value, without allocation.
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self::from_repr_const(Tiny::new())
    }

    pub(crate) const fn from_repr_const(repr: Tiny<u8, B>) -> Self {
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
            /// Length in bytes.
            #[inline]
            #[must_use]
            pub const fn len(&self) -> usize {
                self.repr.len()
            }

            /// Whether the length is zero.
            #[inline]
            #[must_use]
            pub const fn is_empty(&self) -> bool {
                self.repr.is_empty()
            }

            /// Whether the bytes are stored inline, without allocation.
            #[inline]
            #[must_use]
            pub const fn is_inline(&self) -> bool {
                self.repr.is_inline()
            }

            /// Whether the bytes are borrowed.
            #[inline]
            #[must_use]
            pub const fn is_borrowed(&self) -> bool {
                self.repr.is_borrowed()
            }

            /// Whether the bytes are stored on the heap.
            #[inline]
            #[must_use]
            pub const fn is_allocated(&self) -> bool {
                self.repr.is_heap()
            }
        }
    )*};
}

impl_const_accessors!(['a] Wide<'a, u8, B>, ['a] Small<'a, u8, B>, [] Tiny<u8, B>);

/// Implements the `const` typed accessors of an encoding whose byte
/// conversion is `const` (bytes and UTF-8), for every representation.
///
/// `$from` converts `&[u8]` to `&$slice` (unsafe, called on valid bytes);
/// `$to` converts `&$slice` to `&[u8]`.
macro_rules! impl_const_typed_accessors {
    ($enc:ty, $slice:ty, |$b:ident| $from:expr, |$v:ident| $to:expr) => {
        $crate::next::hip::impl_const_typed_accessors!(@one $enc, $slice, |$b| $from, |$v| $to, ['a] $crate::next::repr::Wide<'a, u8, B>, 'a);
        $crate::next::hip::impl_const_typed_accessors!(@one $enc, $slice, |$b| $from, |$v| $to, ['a] $crate::next::repr::Small<'a, u8, B>, 'a);
        $crate::next::hip::impl_const_typed_accessors!(@one $enc, $slice, |$b| $from, |$v| $to, ['a] $crate::next::repr::Tiny<u8, B>, 'a);
    };
    (@one $enc:ty, $slice:ty, |$b:ident| $from:expr, |$v:ident| $to:expr, [$($lt:lifetime)?] $repr:ty, $blt:lifetime) => {
        // the conversion is safe for bytes (identity), unsafe otherwise
        #[allow(unused_unsafe)]
        impl<$($lt,)? B: $crate::next::backend::Backend> $crate::next::hip::Hip<$enc, $repr> {
            /// Raw pointer to the first byte.
            #[inline]
            #[must_use]
            pub const fn as_ptr(&self) -> *const u8 {
                self.repr().as_slice().as_ptr()
            }

            /// The borrowed value, with its full lifetime, if borrowed.
            #[inline]
            #[must_use]
            pub const fn as_borrowed(&self) -> Option<&$blt $slice> {
                match self.repr().borrowed_slice() {
                    // SAFETY: type invariant
                    Some($b) => Some(unsafe { $from }),
                    None => None,
                }
            }

            /// Returns the borrowed value, with its full lifetime, or `Err(self)`.
            ///
            /// # Errors
            ///
            /// Returns `Err(self)` if the value is not borrowed.
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
                if bytes.len() <= <$repr as $crate::next::repr::Repr<'_, u8>>::INLINE_CAPACITY {
                    Some(Self::from_repr_const(<$repr>::inline_copy(bytes)))
                } else {
                    None
                }
            }

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

impl<'a, E: Encoding, R: Repr<'a, u8>> Hip<E, R> {
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

    /// Creates an empty value with at least the given capacity.
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        let mut repr = R::new();
        repr.reserve(capacity);
        // SAFETY: empty
        unsafe { Self::from_repr(repr) }
    }

    /// Maximal length stored inline.
    #[inline]
    #[must_use]
    pub const fn inline_capacity() -> usize {
        R::INLINE_CAPACITY
    }

    /// Capacity of the owned storage: the inline capacity, the heap capacity,
    /// or the length if borrowed or shared (writing then needs a copy).
    #[inline]
    #[must_use]
    pub fn capacity(&self) -> usize {
        if self.repr.is_unique() {
            self.repr.capacity()
        } else {
            self.repr.len()
        }
    }

    /// Makes the value independent of any borrow, copying borrowed data.
    #[inline]
    #[must_use]
    pub fn into_owned(self) -> Hip<E, R::Owned> {
        // SAFETY: same bytes
        unsafe { Hip::from_repr(self.repr.into_owned()) }
    }

    /// Mutable access through the std owned form.
    ///
    /// The value is moved into an owned `E::Owned` (in O(1) when it uniquely
    /// owns an adopted buffer) and moved back when the guard is dropped.
    #[inline]
    pub fn mutate(&mut self) -> RefMut<'_, 'a, E, R> {
        let repr = core::mem::replace(&mut self.repr, R::new());
        // SAFETY: type invariant
        let owned = unsafe { E::owned_from_bytes_unchecked(repr.into_vec()) };
        RefMut {
            target: self,
            owned: Some(owned),
            borrow: PhantomData,
        }
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

    /// Truncates to zero length.
    #[inline]
    pub fn clear(&mut self) {
        self.repr.clear();
    }

    /// Shrinks the capacity as much as possible.
    ///
    /// Moves inline when the bytes fit. No-op if borrowed or shared.
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.shrink_to(0);
    }

    /// Shrinks the capacity, keeping at least `min_capacity`.
    ///
    /// Moves inline when the bytes and `min_capacity` fit. No-op if borrowed
    /// or shared.
    pub fn shrink_to(&mut self, min_capacity: usize) {
        if !matches!(self.repr.kind(), Kind::Heap(_)) || !self.repr.is_unique() {
            return;
        }
        let target = min_capacity.max(self.repr.len());
        if self.repr.capacity() > target {
            let mut repr = R::new();
            repr.reserve(target);
            repr.extend_from_slice(self.bytes());
            self.repr = repr;
        }
    }
}

/// Mutation guard returned by [`Hip::mutate`].
///
/// Dereferences to the std owned form; writes back on drop.
pub struct RefMut<'h, 'a, E: Encoding, R: Repr<'a, u8>> {
    target: &'h mut Hip<E, R>,
    owned: Option<E::Owned>,
    borrow: PhantomData<&'a ()>,
}

impl<'a, E: Encoding, R: Repr<'a, u8>> Drop for RefMut<'_, 'a, E, R> {
    fn drop(&mut self) {
        if let Some(owned) = self.owned.take() {
            *self.target = Hip::from_owned(owned);
        }
    }
}

impl<'a, E: Encoding, R: Repr<'a, u8>> Deref for RefMut<'_, 'a, E, R> {
    type Target = E::Owned;

    #[inline]
    fn deref(&self) -> &E::Owned {
        self.owned.as_ref().unwrap()
    }
}

impl<'a, E: Encoding, R: Repr<'a, u8>> DerefMut for RefMut<'_, 'a, E, R> {
    #[inline]
    fn deref_mut(&mut self) -> &mut E::Owned {
        self.owned.as_mut().unwrap()
    }
}

// ----- traits, once -----

impl<'a, E: Encoding, R: Repr<'a, u8>> Default for Hip<E, R> {
    #[inline]
    fn default() -> Self {
        // SAFETY: empty
        unsafe { Self::from_repr(R::new()) }
    }
}

impl<'a, E: Encoding, R: Repr<'a, u8>> Clone for Hip<E, R> {
    #[inline]
    fn clone(&self) -> Self {
        // SAFETY: same bytes
        unsafe { Self::from_repr(self.repr.clone()) }
    }
}

impl<'a, E: Encoding, R: Repr<'a, u8>> Deref for Hip<E, R> {
    type Target = E::Slice;

    #[inline]
    fn deref(&self) -> &E::Slice {
        self.as_inner()
    }
}

impl<'a, E: Encoding, R: Repr<'a, u8>> AsRef<E::Slice> for Hip<E, R> {
    #[inline]
    fn as_ref(&self) -> &E::Slice {
        self.as_inner()
    }
}

impl<'a, E: Encoding, R: Repr<'a, u8>> Hash for Hip<E, R>
where
    E::Slice: Hash,
{
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_inner().hash(state);
    }
}

impl<'a, E: Encoding, R: Repr<'a, u8>> fmt::Debug for Hip<E, R>
where
    E::Slice: fmt::Debug,
{
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_inner().fmt(f)
    }
}

impl<'a, 'b, E: Encoding, R1: Repr<'a, u8>, R2: Repr<'b, u8>> PartialEq<Hip<E, R2>> for Hip<E, R1>
where
    E::Slice: PartialEq,
{
    #[inline]
    fn eq(&self, other: &Hip<E, R2>) -> bool {
        self.as_inner() == other.as_inner()
    }
}

impl<'a, E: Encoding, R: Repr<'a, u8>> Eq for Hip<E, R> where E::Slice: Eq {}

impl<'a, 'b, E: Encoding, R1: Repr<'a, u8>, R2: Repr<'b, u8>> PartialOrd<Hip<E, R2>> for Hip<E, R1>
where
    E::Slice: PartialOrd,
{
    #[inline]
    fn partial_cmp(&self, other: &Hip<E, R2>) -> Option<Ordering> {
        self.as_inner().partial_cmp(other.as_inner())
    }
}

impl<'a, E: Encoding, R: Repr<'a, u8>> Ord for Hip<E, R>
where
    E::Slice: Ord,
{
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_inner().cmp(other.as_inner())
    }
}

impl<'a, E: Encoding, R: Repr<'a, u8>> From<&E::Slice> for Hip<E, R> {
    /// Copies the value (inline when it fits); see `borrowed` to borrow it.
    #[inline]
    fn from(value: &E::Slice) -> Self {
        Self::from_inner(value)
    }
}

impl<'a, E: Encoding, R: Repr<'a, u8>> From<Cow<'a, E::Slice>> for Hip<E, R>
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

impl<'a, E: Encoding, R: Repr<'a, u8>> From<Hip<E, R>> for Cow<'a, E::Slice>
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
