//! Raw shared sequence of bytes, direct backing of [`HipByt`][super::HipByt].
//!
//! Provides only the core features for the sequence of bytes.

use core::mem::{forget, replace, size_of, ManuallyDrop};
use core::ops::Range;

use allocated::Allocated;
use borrowed::Borrowed;

use crate::alloc::vec::Vec;
use crate::Backend;

mod allocated;
mod borrowed;
mod inline;

type Inline = inline::Inline<INLINE_CAPACITY>;

/// Maximal byte capacity of an inline [`HipStr`](super::HipStr) or [`HipByt`](super::HipByt).
const INLINE_CAPACITY: usize = size_of::<Borrowed>() - 1;

/// Raw immutable byte sequence.
#[repr(C)]
pub union Raw<'borrow, B: Backend> {
    inline: Inline,
    allocated: Allocated<B>,
    borrowed: Borrowed<'borrow>,
}

enum RawSplit<'a, 'borrow, B: Backend> {
    Inline(&'a Inline),
    Allocated(&'a Allocated<B>),
    Borrowed(&'a Borrowed<'borrow>),
}

impl<'borrow, B: Backend> Raw<'borrow, B> {
    /// Creates a new empty `Raw`.
    #[inline]
    pub const fn empty() -> Self {
        Self {
            inline: Inline::empty(),
        }
    }

    /// Creates a new `Raw` from a static slice.
    #[inline]
    pub const fn borrowed(bytes: &'borrow [u8]) -> Self {
        // XXX for now, borrowed do not normalize, Inline::new is not `const`
        Self {
            borrowed: Borrowed::new(bytes),
        }
    }

    /// Creates a new `Raw` from a vector.
    #[inline]
    pub fn from_vec(vec: Vec<u8>) -> Self {
        let len = vec.len();
        if len <= INLINE_CAPACITY {
            Self {
                inline: Inline::new(&vec),
            }
        } else {
            Self {
                allocated: Allocated::new(vec),
            }
        }
    }

    /// Creates a new `Raw` from a slice.
    pub fn from_slice(bytes: &[u8]) -> Self {
        let len = bytes.len();
        if len <= INLINE_CAPACITY {
            unsafe { Self::inline_unchecked(bytes) }
        } else {
            Self::allocate(bytes)
        }
    }

    /// Creates a new `Raw` from a short slice
    ///
    /// # Safety
    ///
    /// The input slice's length MUST be at most `INLINE_CAPACITY`.
    #[inline(never)]
    pub unsafe fn inline_unchecked(bytes: &[u8]) -> Self {
        // SAFETY: see function precondition
        Self {
            inline: unsafe { Inline::new_unchecked(bytes) },
        }
    }

    /// Creates a new allocated `Raw`.
    // For whatever reason the actual allocation is not efficient when inlined
    #[inline(never)]
    fn allocate(bytes: &[u8]) -> Self {
        Self {
            allocated: Allocated::new(bytes.to_vec()),
        }
    }

    /// Splits this raw into its possible representation.
    #[inline]
    const fn split(&self) -> RawSplit<'_, 'borrow, B> {
        if self.is_inline() {
            // SAFETY: representation checked, see is_inline
            RawSplit::Inline(unsafe { &self.inline })
        } else if self.is_borrowed() {
            // SAFETY: representation checked, see is_borrowed
            RawSplit::Borrowed(unsafe { &self.borrowed })
        } else {
            debug_assert!(self.is_allocated());
            // SAFETY: representation checked, see is_borrowed, is_inline and is_allocated
            RawSplit::Allocated(unsafe { &self.allocated })
        }
    }

    /// Returns `true` if the actual representation is an inline string.
    #[inline]
    pub const fn is_inline(&self) -> bool {
        // SAFETY: if self is not inline, shifted_len corresponds to the
        // lower byte of the owner and must have an alignment > 1
        unsafe { self.inline.is_valid() }
    }

    /// Returns `true` if the actual representation is a borrowed reference.
    #[inline]
    pub const fn is_borrowed(&self) -> bool {
        // SAFETY:
        // * If self is inline, the shifted length plus one is in reserved and will be non null.
        // * If self is allocated, the reinterpretation of the owner will be non null too.
        unsafe {
            !self.inline.is_valid() // required for miri, compiled away!
            && self.borrowed.is_valid()
        }
    }

    /// Returns `true` if the actual representation is a heap-allocated string.
    #[inline]
    pub const fn is_allocated(&self) -> bool {
        !self.is_inline() && !self.is_borrowed()
    }

    #[inline]
    pub fn into_borrowed(self) -> Result<&'borrow [u8], Self> {
        if self.is_borrowed() {
            // NO LEAK: no drop needed for borrow repr
            let this = ManuallyDrop::new(self);
            // SAFETY: representation is checked before
            Ok(unsafe { &this.borrowed }.as_slice())
        } else {
            Err(self)
        }
    }

    #[inline]
    pub const fn len(&self) -> usize {
        match self.split() {
            RawSplit::Inline(inline) => inline.len(),
            RawSplit::Allocated(heap) => heap.len(),
            RawSplit::Borrowed(borrowed) => borrowed.len(),
        }
    }

    #[inline]
    pub const fn as_slice(&self) -> &[u8] {
        match self.split() {
            RawSplit::Inline(inline) => inline.as_slice(),
            RawSplit::Allocated(heap) => heap.as_slice(),
            RawSplit::Borrowed(borrowed) => borrowed.as_slice(),
        }
    }

    /// Slices the raw byte string.
    ///
    /// # Safety
    ///
    /// `range` must be a range `a..b` with `a <= b <= len`.
    /// Panics in debug build, UB in release.
    #[inline]
    pub unsafe fn slice_unchecked(&self, range: Range<usize>) -> Self {
        debug_assert!(range.start <= range.end);

        // if range.is_empty() {
        //     return Self::empty();
        // }
        let result = match self.split() {
            RawSplit::Inline(inline) => {
                debug_assert!(range.len() <= inline.len());

                let inline = Inline::new(&inline.as_slice()[range]);
                Self { inline }
            }
            RawSplit::Borrowed(borrowed) => {
                let sl = &borrowed.as_slice()[range];
                Self {
                    borrowed: Borrowed::new(sl),
                }
            }
            RawSplit::Allocated(allocated) => {
                // normalize to inline if possible
                if range.len() <= INLINE_CAPACITY {
                    let inline = Inline::new(&allocated.as_slice()[range]);
                    Self { inline }
                } else {
                    let allocated = unsafe { allocated.slice_unchecked(range) };
                    Self { allocated }
                }
            }
        };

        debug_assert!(self.is_normalized());
        result
    }

    #[inline]
    pub fn as_mut_slice(&mut self) -> Option<&mut [u8]> {
        if self.is_inline() {
            // SAFETY: representation is checked
            Some(unsafe { &mut self.inline }.as_mut_slice())
        } else if self.is_allocated() {
            // SAFETY: representation is checked
            unsafe { self.allocated.as_mut_slice() }
        } else {
            None
        }
    }

    #[inline]
    pub fn push_slice(&mut self, addition: &[u8]) {
        let new_len = self.len() + addition.len();
        if new_len <= INLINE_CAPACITY {
            if !self.is_inline() {
                // make it inline first
                // SAFETY: new_len is checked before, so current len <= INLINE_CAPACITY
                *self = unsafe { Self::inline_unchecked(self.as_slice()) };
            }
            unsafe { self.inline.push_slice_unchecked(addition) };
        } else if self.is_allocated() && unsafe { self.allocated.is_unique() } {
            // current allocation can be pushed into
            unsafe { self.allocated.push_slice_unchecked(addition) };
        } else {
            let mut vec = Vec::with_capacity(new_len);
            vec.extend_from_slice(self.as_slice());
            vec.extend_from_slice(addition);
            let allocated = Allocated::new(vec);
            *self = Self { allocated };
            return;
        }
    }

    #[inline]
    pub fn take_vec(&mut self) -> Vec<u8> {
        if self.is_allocated() {
            // SAFETY: representation is checked, copy without ownership
            let allocated = unsafe { self.allocated };
            if let Ok(owned) = allocated.try_into_vec() {
                // SAFETY: ownership is taken, replace with empty
                // and forget old value (otherwise double drop!!)
                forget(replace(self, Self::empty()));
                return owned;
            }
        }
        let owned = Vec::from(self.as_slice());
        *self = Self::empty();
        owned
    }

    #[inline]
    pub const fn inline_capacity() -> usize {
        Inline::capacity()
    }

    #[inline]
    pub fn capacity(&self) -> usize {
        match self.split() {
            RawSplit::Inline(_) => Self::inline_capacity(),
            RawSplit::Borrowed(borrowed) => borrowed.len(), // provide something to simplify the API
            RawSplit::Allocated(allocated) => allocated.capacity(),
        }
    }

    #[inline]
    pub fn into_vec(mut self) -> Result<Vec<u8>, Self> {
        if let Some(allocated) = self.take_allocated() {
            allocated
                .try_into_vec()
                .map_err(|allocated| Self { allocated })
        } else {
            Err(self)
        }
    }

    #[inline]
    fn take_allocated(&mut self) -> Option<Allocated<B>> {
        if self.is_allocated() {
            // SAFETY: take ownership of the allocated
            // the old value should not be dropped
            let old = ManuallyDrop::new(replace(self, Self::empty()));
            // SAFETY: representation is checked above
            Some(unsafe { old.allocated })
        } else {
            None
        }
    }

    /// Makes the data owned, copying it if it's not already owned.
    #[inline]
    pub fn into_owned(self) -> Raw<'static, B> {
        // SAFETY: take ownership of the allocated
        // the old value do not need to be dropped
        let old = ManuallyDrop::new(self);
        if old.is_borrowed() {
            Raw::from_slice(old.as_slice())
        } else if old.is_inline() {
            // SAFETY: representation is checked above
            Raw {
                inline: unsafe { old.inline },
            }
        } else {
            // => old.is_allocated()

            // SAFETY: take ownership of the allocated
            // the old value should not be dropped
            let old = ManuallyDrop::new(old);
            // SAFETY: representation is checked above
            Raw {
                allocated: unsafe { old.allocated },
            }
        }
    }

    /// Makes the data owned and unique, copying it if necessary.
    ///
    /// # Safety
    ///
    /// Must be non-unique, i.e. `is_unique()` must return `true` **beforehand**.
    #[inline]
    pub unsafe fn into_unique_unchecked(self) -> Self {
        debug_assert!(!self.is_unique());

        // SAFETY: take ownership of the allocated
        // the old value do not need to be dropped
        let old = ManuallyDrop::new(self);
        if old.is_borrowed() {
            Raw::from_slice(old.as_slice())
        } else {
            debug_assert!(old.is_allocated());

            // SAFETY: take ownership of the allocated
            // the old value should not be dropped
            let old = ManuallyDrop::new(old);

            // SAFETY: representation is checked above
            let allocated = unsafe { old.allocated };

            debug_assert!(allocated.len() > INLINE_CAPACITY);

            let new = Self::allocate(allocated.as_slice());
            allocated.decr_ref_count();
            new
        }
    }

    /// Makes the underlying data uniquely owned, copying if needed.
    #[inline]
    pub fn make_unique(&mut self) {
        if !self.is_unique() {
            let old = replace(self, Self::empty());
            // SAFETY: non uniqueness checked above
            *self = unsafe { old.into_unique_unchecked() };
        }
    }

    /// Returns `true` if the data is uniquely owned.
    #[inline]
    pub fn is_unique(&self) -> bool {
        self.is_inline() || (self.is_allocated() && unsafe { self.allocated.is_unique() })
    }

    #[inline]
    pub const fn is_normalized(&self) -> bool {
        self.is_inline() || self.is_borrowed() || self.len() > Self::inline_capacity()
    }
}

impl<'borrow, B: Backend> Drop for Raw<'borrow, B> {
    #[inline]
    fn drop(&mut self) {
        // Formally drops this `Raw` decreasing the ref count if needed
        if let Some(allocated) = self.take_allocated() {
            allocated.decr_ref_count();
        }
    }
}

impl<'borrow, B: Backend> Clone for Raw<'borrow, B> {
    fn clone(&self) -> Self {
        // Duplicates this `Raw` increasing the ref count if needed.
        match self.split() {
            RawSplit::Inline(&inline) => Self { inline },
            RawSplit::Borrowed(&borrowed) => Self { borrowed },
            RawSplit::Allocated(&allocated) => {
                allocated.incr_ref_count();
                Self { allocated }
            }
        }
    }
}
