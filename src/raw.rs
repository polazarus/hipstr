//! Raw shared sequence of bytes, direct backing of [`HipByt`][super::HipByt].
//!
//! Provides only the core features for the sequence of bytes.

use core::hint::unreachable_unchecked;
use core::marker::PhantomData;
use core::mem::{align_of, forget, replace, size_of, transmute, ManuallyDrop, MaybeUninit};
use core::num::NonZeroU8;
use core::ops::Range;
use core::ptr;

use allocated::Allocated;
use borrowed::Borrowed;

use crate::alloc::vec::Vec;
use crate::Backend;

mod allocated;
mod borrowed;
mod inline;
#[cfg(test)]
mod tests;

/// Width (in bits) of the tag
const TAG_BITS: u8 = 2;

/// Mask to extract the tag bits
const MASK: u8 = (1 << TAG_BITS) - 1;

/// Tag for the inline repr
const TAG_INLINE: u8 = 1;

/// Tag for the borrowed repr
const TAG_BORROWED: u8 = 2;

/// Tag for the allocated repr
const TAG_ALLOCATED: u8 = 3;

/// Maximal byte capacity of an inline [`HipStr`](super::HipStr) or [`HipByt`](super::HipByt).
const INLINE_CAPACITY: usize = size_of::<Borrowed>() - 1;

/// Alias type for `Inline` with set inline capacity
type Inline = inline::Inline<INLINE_CAPACITY>;

/// Raw byte sequence.
#[cfg(target_endian = "little")]
#[repr(C)]
pub struct Raw<'borrow, B: Backend> {
    tag_byte: NonZeroU8,
    _word_remainder: MaybeUninit<[u8; size_of::<usize>() - 1]>,
    _word1: MaybeUninit<*mut ()>,
    _word2: MaybeUninit<*mut ()>,

    _marker: PhantomData<&'borrow B>,
}

#[cfg(target_endian = "big")]
#[repr(C)]
pub struct Raw<'borrow, B: Backend> {
    _word2: MaybeUninit<*mut ()>,
    _word1: MaybeUninit<*mut ()>,
    _word_remainder: MaybeUninit<[u8; size_of::<usize>() - 1]>,
    tag_byte: NonZeroU8,

    _marker: PhantomData<&'borrow B>,
}

unsafe impl<'borrow, B: Backend + Sync> Sync for Raw<'borrow, B> {}
unsafe impl<'borrow, B: Backend + Send> Send for Raw<'borrow, B> {}

/// Equivalent union representation.
///
/// NOTE: Cannot be used directly to keep the niche for Option<Raw<_,_>>
#[repr(C)]
union Union<'borrow, B: Backend> {
    /// Inline representation
    inline: Inline,
    /// Allocated and shared representation
    allocated: Allocated<B>,
    /// Borrowed slice representation
    borrowed: Borrowed<'borrow>,
}

impl<'borrow, B: Backend> Union<'borrow, B> {
    const ASSERTS: () = {
        assert!(size_of::<Self>() == size_of::<Raw<'borrow, B>>());
        assert!(align_of::<Self>() == align_of::<Raw<'borrow, B>>());
    };

    #[inline]
    const fn into_raw(self) -> Raw<'borrow, B> {
        // statically checks the layout
        let () = Self::ASSERTS;

        // SAFETY: same layout and same niche hopefully
        unsafe { transmute(self) }
    }
}

/// Repr tag.
///
/// Cannot be used directly to keep the niche.
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Tag {
    Inline = TAG_INLINE,
    Borrowed = TAG_BORROWED,
    Allocated = TAG_ALLOCATED,
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

/// Helper enum to split this raw byte string into its possible representation mutably.
enum RawSplitMut<'a, 'borrow, B: Backend> {
    /// Inline representation
    Inline(&'a mut Inline),
    /// Allocated and shared representation
    Allocated(&'a mut Allocated<B>),
    /// Borrowed slice representation
    Borrowed(&'a mut Borrowed<'borrow>),
}

impl<'borrow, B: Backend> Raw<'borrow, B> {
    /// Retrieves a reference on the union.
    #[inline]
    const fn union(&self) -> &Union<'borrow, B> {
        let raw_ptr: *const _ = self;
        let union_ptr: *const Union<'borrow, B> = raw_ptr.cast();
        // SAFETY: same layout and same niche hopefully, same immutability
        unsafe { &*union_ptr }
    }

    /// Retrieves a mutable reference on the union.
    #[inline]
    fn union_mut(&mut self) -> &mut Union<'borrow, B> {
        let raw_ptr: *mut _ = self;
        let union_ptr: *mut Union<'borrow, B> = raw_ptr.cast();
        // SAFETY: same layout and same niche hopefully, same mutability
        unsafe { &mut *union_ptr }
    }

    /// Extracts the union without dropping the `Raw`.
    fn union_move(self) -> Union<'borrow, B> {
        // SAFETY: same layout and same niche hopefully, same mutability
        let union = unsafe { transmute(self) };
        union
    }

    // basic constructors

    /// Creates a new raw byte sequence from an allocated internal representation.
    ///
    /// The allocated length should be strictly greater than `INLINE_CAPACITY`.
    #[inline]
    const fn from_allocated(allocated: Allocated<B>) -> Self {
        Union { allocated }.into_raw()
    }

    /// Creates a new Raw from an inline representation.
    #[inline]
    const fn from_inline(inline: Inline) -> Self {
        Union { inline }.into_raw()
    }

    /// Creates a new Raw from a borrowed representation.
    #[inline]
    const fn from_borrowed(borrowed: Borrowed<'borrow>) -> Self {
        Union { borrowed }.into_raw()
    }

    /// Retrieves the tag.
    const fn tag(&self) -> Tag {
        match self.tag_byte.get() & MASK {
            TAG_INLINE => Tag::Inline,
            TAG_BORROWED => Tag::Borrowed,
            TAG_ALLOCATED => Tag::Allocated,
            // SAFETY: type invariant
            _ => unsafe { unreachable_unchecked() },
        }
    }

    /// Splits this raw into its possible representation.
    #[inline]
    const fn split(&self) -> RawSplit<'_, 'borrow, B> {
        let tag = self.tag();
        let union = self.union();
        match tag {
            Tag::Inline => {
                // SAFETY: representation checked
                RawSplit::Inline(unsafe { &union.inline })
            }
            Tag::Borrowed => {
                // SAFETY: representation checked
                RawSplit::Borrowed(unsafe { &union.borrowed })
            }
            Tag::Allocated => {
                // SAFETY: representation checked
                RawSplit::Allocated(unsafe { &union.allocated })
            }
        }
    }

    /// Splits this raw into its possible representation.
    #[inline]
    fn split_mut(&mut self) -> RawSplitMut<'_, 'borrow, B> {
        let tag = self.tag();
        let union = self.union_mut();
        match tag {
            Tag::Inline => {
                // SAFETY: representation checked
                RawSplitMut::Inline(unsafe { &mut union.inline })
            }
            Tag::Borrowed => {
                // SAFETY: representation checked
                RawSplitMut::Borrowed(unsafe { &mut union.borrowed })
            }
            Tag::Allocated => {
                // SAFETY: representation checked
                RawSplitMut::Allocated(unsafe { &mut union.allocated })
            }
        }
    }

    /// Creates a new `Raw` from a vector.
    ///
    /// The vector's length should be strictly greater than `INLINE_CAPACITY`.
    #[inline]
    pub fn from_vec(vec: Vec<u8>) -> Self {
        let allocated = Allocated::new(vec);
        Self::from_allocated(allocated)
    }

    /// Creates a new `Raw` from a short slice.
    ///
    /// # Safety
    ///
    /// The input slice's length MUST be at most `INLINE_CAPACITY`.
    #[inline(never)]
    pub unsafe fn inline_unchecked(bytes: &[u8]) -> Self {
        debug_assert!(bytes.len() <= INLINE_CAPACITY);

        // SAFETY: see function precondition
        let inline = unsafe { Inline::new_unchecked(bytes) };

        Self::from_inline(inline)
    }

    /// Creates a new `Raw` from a static slice.
    ///
    /// # Representation
    ///
    /// For now, `borrowed` does not inline strings, i.e. switch to inline string if
    /// possible: it cannot do it because [`Inline::new`] is not const.
    #[inline]
    pub const fn borrowed(bytes: &'borrow [u8]) -> Self {
        Union {
            borrowed: Borrowed::new(bytes),
        }
        .into_raw()
    }

    // derived constructors

    /// Creates a new empty `Raw`.
    #[inline]
    pub const fn empty() -> Self {
        Self::from_inline(Inline::empty())
    }

    /// Creates a new `Raw` from a vector.
    ///
    /// Will normalize the representation depending on the size of the vector.
    #[inline]
    pub fn normalized_from_vec(vec: Vec<u8>) -> Self {
        let len = vec.len();
        if len <= INLINE_CAPACITY {
            // SAFETY: length checked above
            unsafe { Self::inline_unchecked(&vec) }
        } else {
            Self::from_vec(vec)
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
            Self::from_vec(bytes.to_vec())
        }
    }

    /// Creates a new `Raw` with the given capacity.
    ///
    /// **This representation may not be normalized.**
    pub fn with_capacity(capacity: usize) -> Self {
        if capacity <= INLINE_CAPACITY {
            Self::from_inline(Inline::empty())
        } else {
            Self::from_vec(Vec::with_capacity(capacity))
        }
    }

    /// Returns `true` if the actual representation is an inline string.
    #[inline]
    pub const fn is_inline(&self) -> bool {
        matches!(self.tag(), Tag::Inline)
    }

    /// Returns `true` if the actual representation is a borrowed reference.
    #[inline]
    pub const fn is_borrowed(&self) -> bool {
        matches!(self.tag(), Tag::Borrowed)
    }

    /// Returns `true` if the actual representation is a heap-allocated string.
    #[inline]
    pub const fn is_allocated(&self) -> bool {
        matches!(self.tag(), Tag::Allocated)
    }

    /// Returns the borrowed bytes if it was actually borrowed.
    ///
    /// # Errors
    ///
    /// Return the raw byte string if the actual representation is not a borrow.
    #[inline]
    pub fn into_borrowed(self) -> Result<&'borrow [u8], Self> {
        match self.split() {
            RawSplit::Allocated(_) | RawSplit::Inline(_) => Err(self),
            RawSplit::Borrowed(borrowed) => {
                let result = borrowed.as_slice();
                forget(self);
                Ok(result)
            }
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
        debug_assert!(range.start <= range.end);
        debug_assert!(range.end <= self.len());

        let result = match self.split() {
            RawSplit::Inline(inline) => {
                // SAFETY: by `slice_unchecked` safety precondition and `split`
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
                        Self::from_allocated(allocated)
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
                let sl: &'borrow [u8] = unsafe { transmute(slice) };
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
                        Self::from_allocated(allocated)
                    }
                }
            }
        };

        debug_assert!(self.is_normalized());
        result
    }

    #[inline]
    pub fn as_mut_slice(&mut self) -> Option<&mut [u8]> {
        match self.split_mut() {
            RawSplitMut::Inline(inline) => Some(inline.as_mut_slice()),
            RawSplitMut::Allocated(allocated) => allocated.as_mut_slice(),
            RawSplitMut::Borrowed(_) => None,
        }
    }

    /// Push a slice at the end of this raw byte string.
    #[inline]
    pub fn push_slice(&mut self, addition: &[u8]) {
        let new_len = self.len() + addition.len();

        if self.is_allocated() {
            // current allocation may be pushed into it directly?

            // SAFETY: repr checked above
            let allocated = unsafe { &mut self.union_mut().allocated };

            if allocated.is_unique() {
                // SAFETY: uniqueness is checked above
                unsafe {
                    allocated.push_slice_unchecked(addition);
                }
                return;
            }
        }

        if new_len <= INLINE_CAPACITY {
            if !self.is_inline() {
                // make it inline first
                // SAFETY: `new_len` is checked before, so current len <= INLINE_CAPACITY
                *self = unsafe { Self::inline_unchecked(self.as_slice()) };
            }

            // SAFETY: `new_len` is checked above
            unsafe {
                self.union_mut().inline.push_slice_unchecked(addition);
            }
            return;
        }

        // requires a new vector
        let mut vec = Vec::with_capacity(new_len);
        vec.extend_from_slice(self.as_slice());
        vec.extend_from_slice(addition);

        // SAFETY: vec's len (new_len) is checked above to be > INLINE_CAPACITY
        *self = Self::from_vec(vec);

        return;
    }

    /// Takes a vector representation of this raw byte string.
    ///
    /// Will only allocate if needed.
    #[inline]
    pub fn take_vec(&mut self) -> Vec<u8> {
        if self.is_allocated() {
            // SAFETY: representation is checked, copy without ownership
            let allocated = unsafe { self.union_mut().allocated };
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
                .map_err(|allocated| Union { allocated }.into_raw())
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
        match self.split() {
            RawSplit::Allocated(&allocated) => {
                // Takes a copy of allocated

                // replace `self` one by an empty raw
                // forget the old value, we have `allocated` as a valid handle
                forget(replace(self, Self::empty()));

                Some(allocated)
            }
            _ => None,
        }
    }

    /// Makes the data owned, copying it if it's not already owned.
    #[inline]
    pub fn into_owned(self) -> Raw<'static, B> {
        let tag = self.tag();
        let old = self.union_move(); // self is not dropped!

        // SAFETY: tag representation
        unsafe {
            match tag {
                Tag::Allocated => Raw::from_allocated(old.allocated),
                Tag::Borrowed => Raw::from_slice(old.borrowed.as_slice()),
                Tag::Inline => Raw::from_inline(old.inline),
            }
        }
    }

    /// Makes the underlying data uniquely owned, copying if needed.
    #[inline]
    pub fn make_unique(&mut self) {
        if !self.is_unique() {
            let old = replace(self, Self::empty());
            let tag = old.tag();
            let old = old.union_move(); // self is not dropped!

            *self = match tag {
                // Inline is always unique
                Tag::Inline => unsafe { unreachable_unchecked() },

                Tag::Allocated => {
                    // SAFETY: representation is allocated by the function precondition
                    // and the previous check
                    let allocated = unsafe { old.allocated };

                    // SAFETY: by the type invariant
                    // allocated len must be > INLINE_CAPACITY
                    let new = Self::from_vec(allocated.as_slice().to_vec());

                    // manual decrement of the reference count
                    let _dropped = allocated.decr_ref_count();

                    new
                }

                Tag::Borrowed => {
                    // SAFETY: representation is checked above
                    let borrowed = unsafe { old.borrowed };

                    Self::from_slice(borrowed.as_slice())
                }
            };
        }
    }

    /// Returns `true` if the data is uniquely owned.
    #[inline]
    pub fn is_unique(&self) -> bool {
        match self.split() {
            RawSplit::Inline(_) => true,
            RawSplit::Allocated(allocated) => allocated.is_unique(),
            RawSplit::Borrowed(_) => false,
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
        let size = len * size_of::<u8>();

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
            return self.clone();
        }

        let src_len = self.len();
        let new_len = src_len.checked_mul(n).expect("capacity overflow");
        if new_len <= INLINE_CAPACITY {
            let mut inline = Inline::zeroed(new_len);
            let src = self.as_slice().as_ptr();
            let mut dst = inline.as_mut_slice().as_mut_ptr();

            // SAFETY: copy only `new_len` bytes with an
            // upper bound of `INLINE_CAPACITY` checked above
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
            Self::from_vec(vec)
        }
    }

    /// Returns the remaining spare capacity of the vector as a slice of
    /// `MaybeUninit<T>`.
    ///
    /// The returned slice can be used to fill the vector with data (e.g. by
    /// reading from a file) before marking the data as initialized using the
    /// [`set_len`] method.
    ///
    /// [`set_len`]: Raw::set_len
    pub fn spare_capacity_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        match self.split_mut() {
            RawSplitMut::Borrowed(_) => &mut [],
            RawSplitMut::Inline(inline) => inline.spare_capacity_mut(),
            RawSplitMut::Allocated(allocated) => allocated.spare_capacity_mut(),
        }
    }

    /// Forces the length of the vector to `new_len`.
    ///
    /// # Safety
    ///
    /// * `new_len` should be must be less than or equal to `INLINE_CAPACITY`.
    /// * The elements at `old_len..new_len` must be initialized.
    /// * The vector should not be shared (if `new_len != old_len`).
    pub unsafe fn set_len(&mut self, new_len: usize) {
        match self.split_mut() {
            RawSplitMut::Borrowed(borrowed) => {
                debug_assert_ne!(borrowed.len(), new_len);
                if borrowed.len() != new_len {
                    unsafe {
                        unreachable_unchecked();
                    }
                }
            }
            RawSplitMut::Inline(inline) => unsafe { inline.set_len(new_len) },
            RawSplitMut::Allocated(allocated) => unsafe { allocated.set_len(new_len) },
        }
    }
}

impl<'borrow, B: Backend> Drop for Raw<'borrow, B> {
    #[inline]
    fn drop(&mut self) {
        // Formally drops this `Raw` decreasing the ref count if needed
        if let Some(allocated) = self.take_allocated() {
            let _dropped = allocated.decr_ref_count();
        }
    }
}

impl<'borrow, B: Backend> Clone for Raw<'borrow, B> {
    fn clone(&self) -> Self {
        // Duplicates this `Raw` increasing the ref count if needed.
        match self.split() {
            RawSplit::Inline(&inline) => Self::from_inline(inline),
            RawSplit::Borrowed(&borrowed) => Self::from_borrowed(borrowed),
            RawSplit::Allocated(&allocated) => {
                allocated.incr_ref_count();
                Self::from_allocated(allocated)
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
