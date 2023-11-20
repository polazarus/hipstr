//! Raw shared sequence of bytes, direct backing of [`HipByt`][super::HipByt].
//!
//! Provides only the core features for the sequence of bytes.

use core::mem::{forget, replace, size_of, ManuallyDrop};
use core::ops::Range;
use core::ptr;

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
    /// Inline representation
    inline: Inline,
    /// Allocated and shared representation
    allocated: Allocated<B>,
    /// Borrowed slice representation
    borrowed: Borrowed<'borrow>,
}

/// Helper enum to split this raw byte string into its possible representation.
enum RawSplit<'a, 'borrow, B: Backend> {
    /// Inline representation
    Inline(&'a Inline),
    /// Allocated and shared representation
    Allocated(&'a Allocated<B>),
    /// Borrowed slice representation
    Borrowed(&'a Borrowed<'borrow>),
}

impl<'borrow, B: Backend> Raw<'borrow, B> {
    // basic constructors

    /// Creates a new Raw from an allocated internal representation.
    ///
    /// # Safety
    ///
    /// The allocated's length MUST be strictly greater than `INLINE_CAPACITY`.
    #[inline]
    const unsafe fn from_allocated_unchecked(allocated: Allocated<B>) -> Self {
        Self { allocated }
    }

    /// Creates a new Raw from an inline representation.
    #[inline]
    const fn from_inline(inline: Inline) -> Self {
        Self { inline }
    }

    /// Creates a new `Raw` from a vector.
    ///
    /// # Safety
    ///
    /// The vector's length MUST be strictly greater than `INLINE_CAPACITY`.
    #[inline]
    pub unsafe fn from_vec_unchecked(vec: Vec<u8>) -> Self {
        debug_assert!(vec.len() > INLINE_CAPACITY);
        let allocated = Allocated::new(vec);
        // SAFETY: see function precondition
        unsafe { Self::from_allocated_unchecked(allocated) }
    }

    /// Creates a new `Raw` from a short slice.
    ///
    /// # Safety
    ///
    /// The input slice's length MUST be at most `INLINE_CAPACITY`.
    #[inline(never)]
    pub unsafe fn inline_unchecked(bytes: &[u8]) -> Self {
        // SAFETY: see function precondition
        let inline = unsafe { Inline::new_unchecked(bytes) };
        Self::from_inline(inline)
    }

    /// Creates a new empty `Raw`.
    #[inline]
    pub const fn empty() -> Self {
        Self {
            inline: Inline::empty(),
        }
    }

    /// Creates a new `Raw` from a static slice.
    ///
    /// # Representation
    ///
    /// For now, `borrowed` does not inline strings, i.e. switch to inline string if
    /// possible: it cannot do it because [`Inline::new`] is not const.
    #[inline]
    pub const fn borrowed(bytes: &'borrow [u8]) -> Self {
        Self {
            borrowed: Borrowed::new(bytes),
        }
    }

    // derived constructors

    /// Creates a new `Raw` from a vector.
    ///
    /// Will normalize the representation depending on the size of the vector.
    #[inline]
    pub fn from_vec(vec: Vec<u8>) -> Self {
        let len = vec.len();
        if len <= INLINE_CAPACITY {
            // SAFETY: length checked above
            unsafe { Self::inline_unchecked(&vec) }
        } else {
            // SAFETY: length checked above
            unsafe { Self::from_vec_unchecked(vec) }
        }
    }

    /// Creates a new `Raw` from a slice.
    ///
    /// Will normalize the representation depending on the size of the slice.
    pub fn from_slice(bytes: &[u8]) -> Self {
        let len = bytes.len();
        if len <= INLINE_CAPACITY {
            // SAFETY: length checked above
            unsafe { Self::inline_unchecked(bytes) }
        } else {
            // SAFETY: length checked above
            unsafe { Self::from_vec_unchecked(bytes.to_vec()) }
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

    /// Returns the borrowed bytes if it was actually borrowed.
    ///
    /// # Errors
    ///
    /// Return the raw byte string if the actual representation is not a borrow.
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

    /// Returns the length of the raw byte string.
    #[inline]
    pub const fn len(&self) -> usize {
        match self.split() {
            RawSplit::Inline(inline) => inline.len(),
            RawSplit::Allocated(heap) => heap.len(),
            RawSplit::Borrowed(borrowed) => borrowed.len(),
        }
    }

    /// Returns the raw byte string as a byte slice.
    #[inline]
    pub const fn as_slice(&self) -> &[u8] {
        match self.split() {
            RawSplit::Inline(inline) => inline.as_slice(),
            RawSplit::Allocated(heap) => heap.as_slice(),
            RawSplit::Borrowed(borrowed) => borrowed.as_slice(),
        }
    }

    /// Returns a pointer to the start of the raw byte string.
    #[inline]
    pub const fn as_ptr(&self) -> *const u8 {
        match self.split() {
            RawSplit::Inline(inline) => inline.as_ptr(),
            RawSplit::Allocated(heap) => heap.as_ptr(),
            RawSplit::Borrowed(borrowed) => borrowed.as_ptr(),
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
        #[cfg(debug_assertions)]
        {
            assert!(range.start <= range.end);
            assert!(range.end <= self.len());
        }

        let result = match self.split() {
            RawSplit::Inline(inline) => {
                // SAFETY: by slice_unchecked's own safety precondition and `split`
                // range must be of a length <= self.len() <= `INLINE_CAPACITY`
                unsafe { Self::inline_unchecked(&inline.as_slice()[range]) }
            }
            RawSplit::Borrowed(borrowed) => Self::borrowed(&borrowed.as_slice()[range]),
            RawSplit::Allocated(allocated) => {
                // normalize to inline if possible
                if range.len() <= INLINE_CAPACITY {
                    // SAFETY: length is checked above
                    unsafe { Self::inline_unchecked(&allocated.as_slice()[range]) }
                } else {
                    // SAFETY: length is checked above
                    unsafe {
                        let allocated = allocated.slice_unchecked(range);
                        Self::from_allocated_unchecked(allocated)
                    }
                }
            }
        };

        debug_assert!(self.is_normalized());
        result
    }

    /// Slices the raw byte string given a Rust slice.
    ///
    /// # Safety
    ///
    /// `slice` MUST be a part of the raw byte string.
    pub unsafe fn slice_ref_unchecked(&self, slice: &[u8]) -> Self {
        #[cfg(debug_assertions)]
        {
            let range = self.as_slice().as_ptr_range();
            let slice_range = slice.as_ptr_range();
            assert!(range.contains(&slice_range.start) || range.end == slice_range.start);
            assert!(range.contains(&slice_range.end) || range.end == slice_range.end);
        }

        let result = match self.split() {
            RawSplit::Inline(_) => {
                // SAFETY: by the function precondition and the test above
                // slice.len() <= self.len() <= INLINE_CAPACITY
                unsafe { Self::inline_unchecked(slice) }
            }
            RawSplit::Borrowed(_) => {
                // SAFETY: by the function precondition and the type invariant
                // slice must have at least the same dynamic lifetime
                let sl: &'borrow [u8] = unsafe { core::mem::transmute(slice) };
                Self::borrowed(sl)
            }
            RawSplit::Allocated(allocated) => {
                // normalize to inline if possible
                if slice.len() <= INLINE_CAPACITY {
                    // SAFETY: length checked above
                    unsafe { Self::inline_unchecked(slice) }
                } else {
                    // SAFETY: by the function precondition
                    let range = unsafe { range_of_unchecked(self.as_slice(), slice) };
                    // SAFETY: length checked above
                    unsafe {
                        let allocated = allocated.slice_unchecked(range);
                        Self::from_allocated_unchecked(allocated)
                    }
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

    /// Push a slice at the end of this raw byte string.
    #[inline]
    pub fn push_slice(&mut self, addition: &[u8]) {
        let new_len = self.len() + addition.len();
        if new_len <= INLINE_CAPACITY {
            // can be inlined

            if !self.is_inline() {
                // make it inline first
                // SAFETY: new_len is checked before, so current len <= INLINE_CAPACITY
                *self = unsafe { Self::inline_unchecked(self.as_slice()) };
            }
            // SAFETY: new_len is checked above
            unsafe { self.inline.push_slice_unchecked(addition) };
        } else if self.is_allocated_and_unique() {
            // current allocation can be pushed into it directly

            // SAFETY: uniqueness is checked above
            unsafe { self.allocated.push_slice_unchecked(addition) };
        } else {
            // new vector needed

            let mut vec = Vec::with_capacity(new_len);
            vec.extend_from_slice(self.as_slice());
            vec.extend_from_slice(addition);

            // SAFETY: vec's len (new_len) is checked above to be > INLINE_CAPACITY
            *self = unsafe { Self::from_vec_unchecked(vec) };

            return;
        }
    }

    /// Takes a vector representation of this raw byte string.
    ///
    /// Will only allocate if needed.
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

    /// Returns the inline capacity for this particular backend.
    #[inline]
    pub const fn inline_capacity() -> usize {
        Inline::capacity()
    }

    /// Returns the capacity.
    ///
    /// For simplicity's sake, if it's a borrowed byte string, it returns the length.
    #[inline]
    pub fn capacity(&self) -> usize {
        match self.split() {
            RawSplit::Inline(_) => Self::inline_capacity(),
            RawSplit::Borrowed(borrowed) => borrowed.len(), // provide something to simplify the API
            RawSplit::Allocated(allocated) => allocated.capacity(),
        }
    }

    /// Returns the underlying vector if any.
    ///
    /// # Errors
    ///
    /// Returns the byte string as-is if it is not allocated.
    #[inline]
    #[allow(clippy::option_if_let_else)]
    pub fn into_vec(self) -> Result<Vec<u8>, Self> {
        let mut this = ManuallyDrop::new(self);
        if let Some(allocated) = this.take_allocated() {
            allocated
                .try_into_vec()
                .map_err(|allocated| Self { allocated })
        } else {
            Err(ManuallyDrop::into_inner(this))
        }
    }

    /// Takes the allocated representation if any,
    /// replacing it with an empty byte string.
    ///
    /// # Errors
    ///
    /// Returns `None` if this raw byte string is not allocated.
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
    /// Must be non-unique, i.e. [`is_unique()`](Self::is_unique) must return
    /// `true` **beforehand**. In particular, `self` cannot be inlined.
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

            // SAFETY: representation is allocated by the function precondition
            // and the previous check
            let allocated = unsafe { old.allocated };

            // SAFETY: by the type invariant
            // allocated len must be > INLINE_CAPACITY
            let new = unsafe { Self::from_vec_unchecked(allocated.as_slice().to_vec()) };

            // manual decrement of the reference count
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
        self.is_inline() || self.is_allocated_and_unique()
    }

    /// Returns `true` if the data is uniquely owned.
    #[inline]
    pub fn is_allocated_and_unique(&self) -> bool {
        self.is_allocated() && {
            // SAFETY: representation checked above
            unsafe { self.allocated.is_unique() }
        }
    }

    /// Returns `true` if the representation is normalized.
    ///
    /// For now, borrowed representation are not inlined.
    #[inline]
    pub const fn is_normalized(&self) -> bool {
        self.is_inline() || self.is_borrowed() || self.len() > Self::inline_capacity()
    }

    /// Returns `true` it `self` is equal byte for byte to `other`.
    #[inline(never)]
    pub fn eq<B2: Backend>(&self, other: &Raw<B2>) -> bool {
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
        let size = len * core::mem::size_of::<u8>();

        // SAFETY: size checked above
        unsafe { memcmp(self_ptr, other_ptr, size) == 0 }
    }

    /// Creates a new raw byte string by repeating this one `n` times.
    ///
    /// # Panics
    ///
    /// Panics if the capacity would overflow.
    pub fn repeat(&self, n: usize) -> Self {
        if self.len() == 0 || n == 1 {
            self.clone()
        } else {
            let src_len = self.len();
            let new_len = src_len.checked_mul(n).expect("capacity overflow");
            if new_len <= INLINE_CAPACITY {
                let mut inline = Inline::zeroed(new_len);
                let src = self.as_slice().as_ptr();
                let mut dst = inline.as_mut_slice().as_mut_ptr();

                // SAFETY: copy only new_len bytes with an
                // upper bound of INLINE_CAPACITY checked above
                unsafe {
                    // could be better from an algorithmic standpoint
                    // but no expected gain for at most 23 bytes on 64 bit platform
                    for _ in 0..n {
                        ptr::copy_nonoverlapping(src, dst, src_len);
                        dst = dst.add(src_len);
                    }
                }

                Self::from_inline(inline)
            } else {
                let vec = self.as_slice().repeat(n);

                // SAFETY: new len is checked above
                unsafe { Self::from_vec_unchecked(vec) }
            }
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

/// Computes the range in `whole` corresponding to the given `slice`.
///
/// # Safety
///
/// `slice` must be part of `whole`.
unsafe fn range_of_unchecked(whole: &[u8], slice: &[u8]) -> Range<usize> {
    unsafe {
        let offset = slice.as_ptr().offset_from(whole.as_ptr());
        let offset: usize = offset.try_into().unwrap_unchecked();
        offset..offset + slice.len()
    }
}

pub fn try_range_of(whole: &[u8], slice: &[u8]) -> Option<Range<usize>> {
    let len = whole.len();
    let Range { start, end } = whole.as_ptr_range();
    let slice_len = slice.len();
    let slice_start = slice.as_ptr();

    // checks that slice_start in whole
    if slice_start < start || slice_start > end {
        return None;
    }

    // SAFETY: `offset_from` requires both pointers to be in the same allocated object (+1).
    // that is checked above: slice_ptr is in self
    let offset = unsafe { slice_start.offset_from(start) };
    // SAFETY: offset is between 0 and slice_len included
    let offset: usize = unsafe { offset.try_into().unwrap_unchecked() };
    if offset + slice_len > len {
        None
    } else {
        Some(offset..offset + slice_len)
    }
}
