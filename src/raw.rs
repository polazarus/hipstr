//! Raw shared sequence of bytes, direct backing of [`HipByt`][super::HipByt].
//!
//! Provides only the core features for the sequence of bytes.

use std::mem::{forget, replace, size_of, ManuallyDrop};
use std::ops::Range;

use allocated::Allocated;
use borrowed::Borrowed;

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
    const _ASSERTS: () = {
        assert!(size_of::<Inline>() == size_of::<Allocated<B>>());
        assert!(size_of::<Inline>() == size_of::<Borrowed<'borrow>>());
        assert!(size_of::<B::RawPointer>() == size_of::<usize>());
    };

    /// Creates a new empty `Raw`.
    #[inline]
    pub const fn empty() -> Self {
        Self {
            borrowed: Borrowed::empty(),
        }
    }

    /// Creates a new `Raw` from a static slice.
    #[inline]
    pub const fn borrowed(bytes: &'borrow [u8]) -> Self {
        Self {
            borrowed: Borrowed::new(bytes),
        }
    }

    /// Creates a new `Raw` from a vector.
    #[inline]
    pub fn from_vec(vec: Vec<u8>) -> Self {
        Self {
            allocated: Allocated::new(vec),
        }
    }

    /// Creates a new `Raw` from a slice.
    #[inline]
    pub fn from_slice(bytes: &[u8]) -> Self {
        let len = bytes.len();
        if len == 0 {
            Self::empty()
        } else if len <= INLINE_CAPACITY {
            Self {
                inline: Inline::new(bytes),
            }
        } else {
            Self {
                allocated: Allocated::new(bytes.to_vec()),
            }
        }
    }

    /// Splits this raw into its possible representation.
    #[inline]
    const fn split(&self) -> RawSplit<'_, 'borrow, B> {
        if self.is_inline() {
            // SAFETY: representation checked, see is_inline
            RawSplit::Inline(unsafe { &self.inline })
        } else if self.is_static() {
            // SAFETY: representation checked, see is_static
            RawSplit::Borrowed(unsafe { &self.borrowed })
        } else {
            // SAFETY: representation checked, see is_static, is_inline and is_allocated
            debug_assert!(self.is_allocated());
            RawSplit::Allocated(unsafe { &self.allocated })
        }
    }

    #[inline]
    pub const fn is_inline(&self) -> bool {
        // SAFETY: if self is not inline, shifted_len corresponds to the
        // lower byte of the owner and must have an alignment > 1
        unsafe { self.inline.is_valid() }
    }

    #[inline]
    pub const fn is_static(&self) -> bool {
        // SAFETY:
        // * If self is inline, the shifted length plus one is in reserved and will be non null.
        // * If self is allocated, the reinterpretation of the owner will be non null too.
        unsafe {
            !self.inline.is_valid() // required for miri, compiled away!
            && self.borrowed.is_valid()
        }
    }

    #[inline]
    pub const fn is_allocated(&self) -> bool {
        !self.is_inline() && !self.is_static()
    }

    #[inline]
    pub fn into_borrowed(self) -> Result<&'borrow [u8], Self> {
        if self.is_static() {
            // NO LEAK: no drop needed for static repr
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

    #[inline]
    pub fn slice(&self, range: Range<usize>) -> Self {
        if range.is_empty() {
            return Self::empty();
        }

        match self.split() {
            RawSplit::Inline(inline) => {
                debug_assert!(range.len() <= inline.len());
                let inline = Inline::new(&inline.as_slice()[range]);
                Self { inline }
            }
            RawSplit::Borrowed(static_) => {
                let sl = &static_.as_slice()[range];
                Self {
                    borrowed: Borrowed::new(sl),
                }
            }
            RawSplit::Allocated(allocated) => {
                let allocated = allocated.slice(range);
                Self { allocated }
            }
        }
    }

    #[inline]
    pub fn as_mut_slice(&mut self) -> Option<&mut [u8]> {
        if self.is_inline() {
            // SAFETY: representation is checked
            Some(unsafe { &mut self.inline }.as_mut_slice())
        } else if self.is_allocated() {
            // SAFETY: representation is checked
            unsafe { self.allocated.mut_slice() }
        } else {
            None
        }
    }

    #[inline]
    pub fn to_mut_slice(&mut self) -> &mut [u8] {
        let copy = if self.is_inline() {
            // SAFETY: representation is checked
            return unsafe { &mut self.inline }.as_mut_slice();
        } else if self.is_allocated() {
            // SAFETY: representation is checked and data stay allocated for the lifetime of self
            if let Some(slice) = unsafe { self.allocated.mut_slice() } {
                return slice;
            }
            // SAFETY: representation is checked
            let allocated = unsafe { self.allocated };
            Self::from_slice(allocated.as_slice())
        } else {
            // SAFETY: representation is checked
            let static_ = unsafe { self.borrowed };
            Self::from_slice(static_.as_slice())
        };
        *self = copy;
        self.as_mut_slice().unwrap()
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
            RawSplit::Allocated(allocated) => allocated.owner_vec().capacity(),
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

    #[inline]
    pub fn inline(self) -> Result<Self, Self> {
        if self.is_inline() {
            Ok(self)
        } else if self.len() <= Self::inline_capacity() {
            let new = Self {
                inline: Inline::new(self.as_slice()),
            };
            Ok(new)
        } else {
            Err(self)
        }
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
