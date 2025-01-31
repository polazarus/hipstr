//! Raw representations of [`HipByt`].
//!
//! Provides only the core features for the sequence of bytes.

use alloc::vec::Vec;
use core::hint::unreachable_unchecked;
use core::marker::PhantomData;
use core::mem::{align_of, forget, replace, size_of, transmute, ManuallyDrop, MaybeUninit};
use core::num::NonZeroU8;
use core::ops::Range;

use allocated::Allocated;
use borrowed::Borrowed;

use crate::Backend;

pub mod allocated;
pub mod borrowed;
pub mod inline;
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

/// Maximal byte capacity of an inline [`HipByt`].
const INLINE_CAPACITY: usize = size_of::<Borrowed>() - 1;

/// Size of word minus a tagged byte.
const WORD_SIZE_M1: usize = size_of::<usize>() - 1;

/// Alias type for `Inline` with set inline capacity
pub type Inline = inline::Inline<INLINE_CAPACITY>;

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
#[repr(C)]
pub struct HipByt<'borrow, B: Backend> {
    pivot: Pivot,
    _marker: PhantomData<&'borrow B>,
}

#[derive(Clone, Copy)]
#[repr(C)]
pub(super) struct Pivot {
    #[cfg(target_endian = "little")]
    tag_byte: NonZeroU8,
    #[cfg(target_endian = "little")]
    _word_remainder: MaybeUninit<[u8; WORD_SIZE_M1]>,
    #[cfg(target_endian = "little")]
    _word1: MaybeUninit<*mut ()>,

    _word2: MaybeUninit<*mut ()>,

    #[cfg(target_endian = "big")]
    _word1: MaybeUninit<*mut ()>,
    #[cfg(target_endian = "big")]
    _word_remainder: MaybeUninit<[u8; WORD_SIZE_M1]>,
    #[cfg(target_endian = "big")]
    tag_byte: NonZeroU8,
}

unsafe impl<B: Backend + Sync> Sync for HipByt<'_, B> {}
unsafe impl<B: Backend + Send> Send for HipByt<'_, B> {}

/// Equivalent union representation.
///
/// NOTE: Cannot be used directly to keep the niche for `Option<HipByt<_,_>>`
#[repr(C)]
pub union Union<'borrow, B: Backend> {
    /// Inline representation
    pub inline: Inline,

    /// Allocated and shared representation
    pub allocated: Allocated<B>,

    /// Borrowed slice representation
    pub borrowed: Borrowed<'borrow>,

    /// Pivot representation with niche
    pivot: Pivot,
}

impl<'borrow, B: Backend> Union<'borrow, B> {
    const ASSERTS: () = {
        assert!(size_of::<Self>() == size_of::<HipByt<'borrow, B>>());
        assert!(align_of::<Self>() == align_of::<HipByt<'borrow, B>>());
    };

    #[inline]
    pub const fn into_raw(self) -> HipByt<'borrow, B> {
        // statically checks the layout
        let () = Self::ASSERTS;

        // SAFETY: same layout and same niche hopefully
        let pivot = unsafe { self.pivot };
        HipByt {
            pivot,
            _marker: PhantomData,
        }
    }
}

/// Repr tag.
///
/// Cannot be used directly to keep the niche.
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Tag {
    Inline = TAG_INLINE,
    Borrowed = TAG_BORROWED,
    Allocated = TAG_ALLOCATED,
}

/// Helper enum to split this raw byte string into its possible representation.
pub enum Split<'a, 'borrow, B: Backend> {
    /// Inline representation
    Inline(&'a Inline),
    /// Allocated and shared representation
    Allocated(&'a Allocated<B>),
    /// Borrowed slice representation
    Borrowed(&'a Borrowed<'borrow>),
}

/// Helper enum to split this raw byte string into its possible representation mutably.
pub enum SplitMut<'a, 'borrow, B: Backend> {
    /// Inline representation
    Inline(&'a mut Inline),
    /// Allocated and shared representation
    Allocated(&'a mut Allocated<B>),
    /// Borrowed slice representation
    Borrowed(&'a mut Borrowed<'borrow>),
}

impl<'borrow, B: Backend> HipByt<'borrow, B> {
    /// Retrieves a reference on the union.
    #[inline]
    pub(super) const fn union(&self) -> &Union<'borrow, B> {
        let raw_ptr: *const _ = &self.pivot;
        let union_ptr: *const Union<'borrow, B> = raw_ptr.cast();
        // SAFETY: same layout and same niche hopefully, same immutability
        unsafe { &*union_ptr }
    }

    /// Retrieves a mutable reference on the union.
    #[inline]
    pub(super) const fn union_mut(&mut self) -> &mut Union<'borrow, B> {
        let raw_ptr: *mut _ = &mut self.pivot;
        let union_ptr: *mut Union<'borrow, B> = raw_ptr.cast();
        // SAFETY: same layout and same niche hopefully, same mutability
        unsafe { &mut *union_ptr }
    }

    /// Extracts the union without dropping the `HipByt`.
    pub(super) fn union_move(self) -> Union<'borrow, B> {
        // Do not drop free!
        let this = ManuallyDrop::new(self);
        Union { pivot: this.pivot }
    }

    // basic constructors

    /// Creates a new `HipByt` from an allocated internal representation.
    ///
    /// To be normalized, the allocated length should be strictly greater than
    /// `INLINE_CAPACITY`.
    #[inline]
    pub(super) const fn from_allocated(allocated: Allocated<B>) -> Self {
        Union { allocated }.into_raw()
    }

    /// Creates a new `HipByt` from an inline representation.
    #[inline]
    pub(super) const fn from_inline(inline: Inline) -> Self {
        Union { inline }.into_raw()
    }

    /// Creates a new `HipByt` from a borrowed representation.
    #[inline]
    pub(super) const fn from_borrowed(borrowed: Borrowed<'borrow>) -> Self {
        Union { borrowed }.into_raw()
    }

    /// Retrieves the tag.
    pub(super) const fn tag(&self) -> Tag {
        match self.pivot.tag_byte.get() & MASK {
            TAG_INLINE => Tag::Inline,
            TAG_BORROWED => Tag::Borrowed,
            TAG_ALLOCATED => Tag::Allocated,
            // SAFETY: type invariant
            _ => unsafe { unreachable_unchecked() },
        }
    }

    /// Splits this raw into its possible representation.
    #[inline]
    pub(super) const fn split(&self) -> Split<'_, 'borrow, B> {
        let tag = self.tag();
        let union = self.union();
        match tag {
            Tag::Inline => {
                // SAFETY: representation checked
                Split::Inline(unsafe { &union.inline })
            }
            Tag::Borrowed => {
                // SAFETY: representation checked
                Split::Borrowed(unsafe { &union.borrowed })
            }
            Tag::Allocated => {
                // SAFETY: representation checked
                Split::Allocated(unsafe { &union.allocated })
            }
        }
    }

    /// Splits this raw into its possible representation.
    #[inline]
    pub(super) const fn split_mut(&mut self) -> SplitMut<'_, 'borrow, B> {
        let tag = self.tag();
        let union = self.union_mut();
        match tag {
            Tag::Inline => {
                // SAFETY: representation checked
                SplitMut::Inline(unsafe { &mut union.inline })
            }
            Tag::Borrowed => {
                // SAFETY: representation checked
                SplitMut::Borrowed(unsafe { &mut union.borrowed })
            }
            Tag::Allocated => {
                // SAFETY: representation checked
                SplitMut::Allocated(unsafe { &mut union.allocated })
            }
        }
    }

    /// Creates a new `HipByt` from a vector.
    pub(super) fn from_vec(vec: Vec<u8>) -> Self {
        let allocated = Allocated::new(vec);
        Self::from_allocated(allocated)
    }

    /// Creates a new empty inline `HipByt`.
    #[inline]
    pub(super) const fn inline_empty() -> Self {
        const { Self::from_inline(Inline::empty()) }
    }

    /// Creates a new `HipByt` from a short slice.
    ///
    /// # Safety
    ///
    /// The input slice's length MUST be at most `INLINE_CAPACITY`.
    pub(super) const unsafe fn inline_unchecked(bytes: &[u8]) -> Self {
        // SAFETY: see function precondition
        let inline = unsafe { Inline::new_unchecked(bytes) };
        Self::from_inline(inline)
    }

    // derived constructors

    /// Creates a new `HipByt` from a vector.
    ///
    /// Will normalize the representation depending on the size of the vector.
    #[inline]
    pub(crate) fn normalized_from_vec(vec: Vec<u8>) -> Self {
        let len = vec.len();
        if len <= INLINE_CAPACITY {
            // SAFETY: length checked above
            unsafe { Self::inline_unchecked(&vec) }
        } else {
            Self::from_vec(vec)
        }
    }

    /// Creates a new `HipByt` from a slice.
    ///
    /// Will normalize the representation depending on the size of the slice.
    pub(crate) fn from_slice(bytes: &[u8]) -> Self {
        let len = bytes.len();
        if len == 0 {
            Self::inline_empty()
        } else if len <= INLINE_CAPACITY {
            // SAFETY: length checked above
            unsafe { Self::inline_unchecked(bytes) }
        } else {
            Self::from_allocated(Allocated::from_slice(bytes))
        }
    }

    /// Slices the raw byte sequence.
    ///
    /// # Safety
    ///
    /// `range` must be a range `a..b` with `a <= b <= len`.
    ///
    /// Panics in debug build, UB in release.
    #[inline]
    pub(super) unsafe fn range_unchecked(&self, range: Range<usize>) -> Self {
        debug_assert!(range.start <= range.end);
        debug_assert!(range.end <= self.len());

        let result = match self.split() {
            Split::Inline(inline) => {
                // SAFETY: by `slice_unchecked` safety precondition and `split`
                // range must be of a length <= self.len() <= `INLINE_CAPACITY`
                unsafe { Self::inline_unchecked(&inline.as_slice()[range]) }
            }
            Split::Borrowed(borrowed) => Self::borrowed(&borrowed.as_slice()[range]),
            Split::Allocated(allocated) => {
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
        #[cfg(debug_assertions)]
        {
            let range = self.as_slice().as_ptr_range();
            let slice_range = slice.as_ptr_range();
            assert!(range.contains(&slice_range.start) || range.end == slice_range.start);
            assert!(range.contains(&slice_range.end) || range.end == slice_range.end);
        }

        let result = match self.split() {
            Split::Inline(_) => {
                // SAFETY: by the function precondition and the test above
                // slice.len() <= self.len() <= INLINE_CAPACITY
                unsafe { Self::inline_unchecked(slice) }
            }
            Split::Borrowed(_) => {
                // SAFETY: by the function precondition and the type invariant
                // slice must have at least the same dynamic lifetime
                let sl: &'borrow [u8] = unsafe { transmute(slice) };
                Self::borrowed(sl)
            }
            Split::Allocated(allocated) => {
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

    /// Takes a vector representation of this raw byte string.
    ///
    /// Will only allocate if needed.
    #[inline]
    pub(crate) fn take_vec(&mut self) -> Vec<u8> {
        if self.is_allocated() {
            // SAFETY: representation is checked, copy without ownership
            let allocated = unsafe { self.union_mut().allocated };
            if let Ok(owned) = allocated.try_into_vec() {
                // SAFETY: ownership is taken, replace with empty
                // and forget old value (otherwise double drop!!)
                forget(replace(self, Self::new()));
                return owned;
            }
        }
        let owned = Vec::from(self.as_slice());
        *self = Self::new();
        owned
    }

    /// Takes the allocated representation if any, replacing it with an empty
    /// byte string.
    ///
    /// # Errors
    ///
    /// Returns `None` if this byte string is not allocated.
    #[inline]
    pub(super) fn take_allocated(&mut self) -> Option<Allocated<B>> {
        match self.split() {
            Split::Allocated(&allocated) => {
                // Takes a copy of allocated

                // replace `self` one by an empty raw
                // forget the old value, we have `allocated` as a valid handle
                forget(replace(self, Self::new()));

                Some(allocated)
            }
            _ => None,
        }
    }

    /// Makes the underlying data uniquely owned, copying if needed.
    #[inline]
    pub(super) fn make_unique(&mut self) {
        let tag = self.tag();
        match tag {
            Tag::Inline => {}
            Tag::Borrowed => {
                let old = replace(self, Self::new()).union_move();

                // SAFETY: representation is checked above
                let borrowed = unsafe { old.borrowed };

                *self = Self::from_slice(borrowed.as_slice());
            }
            Tag::Allocated => {
                // SAFETY: representation checked above
                if unsafe { self.union().allocated }.is_unique() {
                    return;
                }

                let old = replace(self, Self::new());

                // SAFETY: representation checked above
                let allocated = unsafe { old.union_move().allocated };

                // SAFETY: by the type invariant
                // allocated len must be > INLINE_CAPACITY
                let new = Self::from_vec(allocated.as_slice().to_vec());

                // manual decrement of the reference count
                allocated.explicit_drop();

                *self = new;
            }
        }
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
}

impl<B: Backend> Drop for HipByt<'_, B> {
    #[inline]
    fn drop(&mut self) {
        // formally drops the allocated decreasing the ref count if needed
        if let Some(allocated) = self.take_allocated() {
            allocated.explicit_drop();
        }
    }
}

impl<B: Backend> Clone for HipByt<'_, B> {
    fn clone(&self) -> Self {
        match self.split() {
            Split::Inline(&inline) => Self::from_inline(inline),
            Split::Borrowed(&borrowed) => Self::from_borrowed(borrowed),
            Split::Allocated(allocated) => {
                // increase the ref count or clone if overflow
                let clone = allocated.explicit_clone();
                Self::from_allocated(clone)
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
