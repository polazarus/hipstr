//! The three representations, behind one [`Repr`] trait.
//!
//! | Repr      | Size    | Inline (`u8`, 64-bit) | Borrowed | Heap       | Slicing |
//! |-----------|---------|-----------------------|----------|------------|---------|
//! | [`Wide`]  | 3 words | 23                    | yes      | thin + vec | yes     |
//! | [`Small`] | 2 words | 15                    | yes      | thin + vec | no      |
//! | [`Tiny`]  | 1 word  | 7                     | no       | thin + vec | no      |
//!
//! All three share the heap handle [`Owner`](owner::Owner) and the inline
//! vector machinery; they only differ by how they pack the cases into words.
//!
//! Conventions shared by every representation:
//!
//! - empty values are inline (no allocation, no borrowed empty slice);
//! - [`Repr::from_slice`] and [`Repr::from_vec`] go inline when the elements
//!   fit, otherwise a thin heap (slice) or an adopted vector (without copying);
//! - mutation goes through [`Repr::try_reserve`], which makes the value
//!   uniquely owned (copy-on-write) before handing out raw access.

use alloc::vec::Vec;

use crate::thin::TryReserveError;

#[cfg(feature = "hip")]
pub(crate) mod owner;
#[cfg(any(feature = "hip", feature = "small", feature = "tiny"))]
pub(crate) mod parts;
#[cfg(feature = "small")]
pub(crate) mod small;
#[cfg(any(feature = "small", feature = "tiny"))]
pub(crate) mod thin_owner;
#[cfg(feature = "tiny")]
pub(crate) mod tiny;
#[cfg(feature = "hip")]
pub(crate) mod wide;

#[cfg(test)]
mod tests;

#[cfg(feature = "small")]
pub use small::Small;
#[cfg(feature = "tiny")]
pub use tiny::Tiny;
#[cfg(feature = "hip")]
pub use wide::Wide;

/// Invokes `$m!` with every enabled representation, each as
/// `#[cfg(..)] [lifetime] type` (the lifetime parameter, if any, and the type
/// generic over a backend `B`).
macro_rules! for_each_repr {
    ($m:ident) => {
        $m! {
            #[cfg(feature = "hip")] ['a] $crate::repr::Wide<'a, B>,
            #[cfg(feature = "small")] ['a] $crate::repr::Small<'a, B>,
            #[cfg(feature = "tiny")] [] $crate::repr::Tiny<B>,
        }
    };
}
pub(crate) use for_each_repr;

/// Heap kind of a value: a thin buffer (header and bytes in one allocation)
/// or an adopted vector.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HeapKind {
    Thin,
    Vec,
}

/// Current case of a representation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    Inline,
    Borrowed,
    Heap(HeapKind),
}

mod sealed {
    /// Only the crate's representations implement [`Repr`](super::Repr).
    pub trait Sealed {}

    #[cfg(feature = "hip")]
    impl<B: crate::backend::Backend> Sealed for super::Wide<'_, B> {}
    #[cfg(feature = "small")]
    impl<B: crate::backend::Backend> Sealed for super::Small<'_, B> {}
    #[cfg(feature = "tiny")]
    impl<B: crate::backend::Backend> Sealed for super::Tiny<B> {}
}

/// A representation of a copy-on-write sequence of `u8`.
///
/// # Safety
///
/// Implementors guarantee that, after a successful [`try_reserve`], the value
/// is uniquely owned, [`as_mut_ptr`] points to [`capacity`] slots of which the
/// first [`len`] are initialized, and [`set_len`] updates the length seen by
/// [`as_slice`]. Those guarantees hold until the next call to a method taking
/// `&self` that may share the value (namely [`Clone::clone`]).
///
/// [`try_reserve`]: Repr::try_reserve
/// [`as_mut_ptr`]: Repr::as_mut_ptr
/// [`capacity`]: Repr::capacity
/// [`len`]: Repr::len
/// [`set_len`]: Repr::set_len
/// [`as_slice`]: Repr::as_slice
pub unsafe trait Repr<'a>: Clone + Sized + sealed::Sealed {
    /// Size in words.
    const WORDS: usize;

    /// The same representation, without the borrow lifetime.
    type Owned: Repr<'static, Owned = Self::Owned> + 'static;

    /// The backend of the heap buffers.
    type Backend: crate::backend::Backend;

    /// Maximal number of elements stored inline.
    const INLINE_CAPACITY: usize;

    /// Maximal number of elements.
    const MAX_LEN: usize;

    /// Whether borrowed slices are kept as is (otherwise they are copied).
    const BORROWS: bool;

    /// Whether vectors are adopted without copying (`from_vec`, and
    /// `into_vec` of a unique adopted vector); otherwise they are copied
    /// into a thin buffer.
    const ADOPTS_VEC: bool;

    fn new() -> Self;

    fn from_slice(slice: &[u8]) -> Self;

    /// Borrows `slice` if the representation supports it, copies it otherwise.
    fn from_borrowed(slice: &'a [u8]) -> Self;

    /// Adopts the vector's buffer if it does not fit inline.
    fn from_vec(vec: Vec<u8>) -> Self;

    fn kind(&self) -> Kind;

    /// Takes the value apart, without copying a heap buffer (see
    /// [`parts`]).
    #[doc(hidden)]
    #[cfg(any(feature = "hip", feature = "small", feature = "tiny"))]
    fn into_parts(self) -> parts::Parts<'a, Self::Backend>;

    /// Rebuilds a value from parts it can hold as they are (see
    /// [`parts`]).
    ///
    /// # Errors
    ///
    /// Gives the parts back if they need a copy.
    #[doc(hidden)]
    #[cfg(any(feature = "hip", feature = "small", feature = "tiny"))]
    fn try_from_parts(
        parts: parts::Parts<'a, Self::Backend>,
    ) -> Result<Self, parts::Parts<'a, Self::Backend>>;

    fn as_slice(&self) -> &[u8];

    fn len(&self) -> usize;

    #[inline]
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Makes the value independent of the borrow, copying borrowed data.
    fn into_owned(self) -> Self::Owned;

    /// The borrowed slice, with its full lifetime, if the value is borrowed.
    fn as_borrowed(&self) -> Option<&'a [u8]>;

    /// Converts into a vector, in O(1) for a unique adopted vector.
    fn into_vec(self) -> Vec<u8>;

    /// Whether the value can be mutated in place (inline or unique heap).
    fn is_unique(&self) -> bool;

    /// Makes the value uniquely owned with room for `additional` more
    /// elements; when growing, `exact` asks for no more than needed
    /// (otherwise the capacity may grow geometrically).
    ///
    /// # Errors
    ///
    /// On capacity overflow or allocation failure; the value is unchanged.
    fn try_reserve_with(&mut self, additional: usize, exact: bool) -> Result<(), TryReserveError>;

    /// Makes the value uniquely owned with room for `additional` more
    /// elements, growing geometrically.
    ///
    /// # Errors
    ///
    /// On capacity overflow or allocation failure; the value is unchanged.
    #[inline]
    fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.try_reserve_with(additional, false)
    }

    /// Makes the value uniquely owned with room for `additional` more
    /// elements, without deliberate over-allocation.
    ///
    /// # Errors
    ///
    /// On capacity overflow or allocation failure; the value is unchanged.
    #[inline]
    fn try_reserve_exact(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.try_reserve_with(additional, true)
    }

    /// Capacity of the owned storage.
    ///
    /// Only meaningful after a successful [`try_reserve`](Repr::try_reserve).
    fn capacity(&self) -> usize;

    /// Shrinks the visible length to `len` (`0 < len < self.len()`) in O(1)
    /// without copying or touching shared storage, if the representation
    /// can (borrowed or heap views). Returns `false` otherwise.
    fn shrink_view(&mut self, len: usize) -> bool;

    /// Shrinks the storage of a uniquely owned heap value to about `target`
    /// elements (`len <= target`), in place (`realloc`). Returns `Ok(false)`,
    /// doing nothing, if the value is not a unique heap value.
    ///
    /// # Errors
    ///
    /// If the allocator fails; the value is then unchanged.
    fn try_shrink_in_place(&mut self, target: usize) -> Result<bool, TryReserveError>;

    /// Whether a heap value shows only part of its buffer (so that a copy
    /// could let the rest be freed).
    fn is_partial_view(&self) -> bool;

    /// The elements from `at` on (`at <= len`), as a new value: a copy by
    /// default, an O(1) shared slice for representations that can.
    #[inline]
    #[must_use]
    fn split_tail(&self, at: usize) -> Self {
        Self::from_slice(&self.as_slice()[at..])
    }

    /// Raw pointer to the owned storage.
    ///
    /// # Safety
    ///
    /// Must follow a successful [`try_reserve`](Repr::try_reserve).
    unsafe fn as_mut_ptr(&mut self) -> *mut u8;

    /// Sets the length.
    ///
    /// # Safety
    ///
    /// Must follow a successful [`try_reserve`](Repr::try_reserve), with
    /// `len <= capacity` and the first `len` elements initialized.
    unsafe fn set_len(&mut self, len: usize);

    // ----- provided methods, written once for every representation -----

    #[inline]
    fn reserve(&mut self, additional: usize) {
        crate::thin::unwrap_or_oom(self.try_reserve(additional));
    }

    /// Mutable access, copying first if shared or borrowed.
    #[inline]
    fn to_mut_slice(&mut self) -> &mut [u8] {
        self.reserve(0);
        let len = self.len();
        // SAFETY: unique after `reserve`, `len` initialized elements
        unsafe { core::slice::from_raw_parts_mut(self.as_mut_ptr(), len) }
    }

    fn extend_from_slice(&mut self, slice: &[u8]) {
        if slice.is_empty() {
            // keep borrowed or shared values as they are
            return;
        }
        self.reserve(slice.len());
        let len = self.len();
        // SAFETY: unique with room for `slice.len()` more elements; `slice`
        // cannot alias the owned storage, which is uniquely borrowed by `self`
        unsafe {
            self.as_mut_ptr()
                .add(len)
                .copy_from_nonoverlapping(slice.as_ptr(), slice.len());
            self.set_len(len + slice.len());
        }
    }

    /// Resizes to `new_len`, filling with `value` when growing.
    fn resize(&mut self, new_len: usize, value: u8) {
        let len = self.len();
        if new_len <= len {
            self.truncate(new_len);
            return;
        }
        self.reserve(new_len - len);
        // SAFETY: unique with room for `new_len` elements; the new ones are
        // written before the length covers them
        unsafe {
            let tail = self.as_mut_ptr().add(len);
            for i in 0..new_len - len {
                tail.add(i).write(value);
            }
            self.set_len(new_len);
        }
    }

    #[inline]
    fn push(&mut self, value: u8) {
        self.extend_from_slice(core::slice::from_ref(&value));
    }

    fn pop(&mut self) -> Option<u8> {
        let last = *self.as_slice().last()?;
        self.truncate(self.len() - 1);
        Some(last)
    }

    /// Shortens to `len` elements, keeping the value normalized: a heap
    /// value that fits inline moves inline; otherwise borrowed and heap
    /// values shrink their view in O(1) when the representation allows it.
    fn truncate(&mut self, len: usize) {
        if len >= self.len() {
            return;
        }
        if len == 0 {
            *self = Self::new();
        } else if matches!(self.kind(), Kind::Heap(_)) && len <= Self::INLINE_CAPACITY {
            *self = Self::from_slice(&self.as_slice()[..len]);
        } else if !self.shrink_view(len) {
            self.reserve(0);
            // SAFETY: unique, shrinking keeps elements initialized
            unsafe { self.set_len(len) };
        }
    }

    #[inline]
    fn clear(&mut self) {
        self.truncate(0);
    }
}

/// Error for heap lengths beyond [`Repr::MAX_LEN`].
pub(crate) const fn capacity_overflow() -> TryReserveError {
    TryReserveError(crate::thin::TryReserveErrorKind::CapacityOverflow)
}

/// Reads the bits of a word that may hold a pointer, in a const context too.
///
/// The provenance is ignored: the result is only used to test tag bits. In a
/// const context, only values without provenance (inline or borrowed-marker
/// words) can reach this function.
#[inline]
pub(crate) const fn word_bits(word: &core::ptr::NonNull<()>) -> usize {
    // SAFETY: a `NonNull<()>` has the size and alignment of a `usize`
    unsafe { *core::ptr::from_ref(word).cast::<usize>() }
}
