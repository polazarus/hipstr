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

pub use owner::HeapKind;

use crate::next::thin::TryReserveError;

pub mod owner;
pub mod small;
pub mod tiny;
pub mod wide;

#[cfg(test)]
mod tests;

pub use small::Small;
pub use tiny::Tiny;
pub use wide::Wide;

/// Current case of a representation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    Inline,
    Borrowed,
    Heap(HeapKind),
}

/// A representation of a copy-on-write sequence of `T`.
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
pub unsafe trait Repr<'a, T: Copy + 'a>: Clone + Sized {
    /// Size in words.
    const WORDS: usize;

    /// Maximal number of elements stored inline.
    const INLINE_CAPACITY: usize;

    /// Maximal number of elements.
    const MAX_LEN: usize;

    /// Whether borrowed slices are kept as is (otherwise they are copied).
    const BORROWS: bool;

    fn new() -> Self;

    fn from_slice(slice: &[T]) -> Self;

    /// Borrows `slice` if the representation supports it, copies it otherwise.
    fn from_borrowed(slice: &'a [T]) -> Self;

    /// Adopts the vector's buffer if it does not fit inline.
    fn from_vec(vec: Vec<T>) -> Self;

    fn kind(&self) -> Kind;

    fn as_slice(&self) -> &[T];

    #[inline]
    fn len(&self) -> usize {
        self.as_slice().len()
    }

    #[inline]
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Converts into a vector, in O(1) for a unique adopted vector.
    fn into_vec(self) -> Vec<T>;

    /// Whether the value can be mutated in place (inline or unique heap).
    fn is_unique(&self) -> bool;

    /// Makes the value uniquely owned with room for `additional` more elements.
    fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError>;

    /// Capacity of the owned storage.
    ///
    /// Only meaningful after a successful [`try_reserve`](Repr::try_reserve).
    fn capacity(&self) -> usize;

    /// Raw pointer to the owned storage.
    ///
    /// # Safety
    ///
    /// Must follow a successful [`try_reserve`](Repr::try_reserve).
    unsafe fn as_mut_ptr(&mut self) -> *mut T;

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
        crate::next::thin::unwrap_or_oom(self.try_reserve(additional));
    }

    /// Mutable access, copying first if shared or borrowed.
    #[inline]
    fn to_mut_slice(&mut self) -> &mut [T] {
        self.reserve(0);
        let len = self.len();
        // SAFETY: unique after `reserve`, `len` initialized elements
        unsafe { core::slice::from_raw_parts_mut(self.as_mut_ptr(), len) }
    }

    fn extend_from_slice(&mut self, slice: &[T]) {
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

    #[inline]
    fn push(&mut self, value: T) {
        self.extend_from_slice(core::slice::from_ref(&value));
    }

    fn pop(&mut self) -> Option<T> {
        let last = *self.as_slice().last()?;
        self.truncate(self.len() - 1);
        Some(last)
    }

    fn truncate(&mut self, len: usize) {
        if len < self.len() {
            if len == 0 {
                *self = Self::new();
            } else {
                self.reserve(0);
                // SAFETY: unique, shrinking keeps elements initialized
                unsafe { self.set_len(len) };
            }
        }
    }

    #[inline]
    fn clear(&mut self) {
        self.truncate(0);
    }
}

/// Error for heap lengths beyond [`Repr::MAX_LEN`].
pub(crate) const fn capacity_overflow() -> TryReserveError {
    TryReserveError(crate::next::thin::TryReserveErrorKind::CapacityOverflow)
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
