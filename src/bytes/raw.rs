//! Raw representations of [`HipByt`].
//!
//! Provides only the core features for the sequence of bytes.

use alloc::vec::Vec;
use core::hint::unreachable_unchecked;
use core::marker::PhantomData;
use core::mem::{self, align_of, forget, replace, size_of, transmute, ManuallyDrop, MaybeUninit};
use core::num::NonZeroU8;
use core::ops::Range;

use allocated::Allocated;
use borrowed::Borrowed;

use crate::backend::Backend;
use crate::common::{manually_drop_as_mut, manually_drop_as_ref};
use crate::vecs::hip::HipVec;
use crate::vecs::inline::InlineVec;

pub mod allocated;
pub mod borrowed;
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
pub(crate) const INLINE_CAPACITY: usize = Inline::CAPACITY;

/// Size of word minus a tagged byte.
const WORD_SIZE_M1: usize = size_of::<usize>() - 1;

/// Alias type for `Inline` with set inline capacity
pub type Inline = InlineVec<u8, typenum::U<{ size_of::<Borrowed>() }>>;

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

impl<'borrow, B: Backend> HipByt<'borrow, B> {
    pub(crate) const fn into_hipvec(self) -> HipVec<'borrow, u8, B> {
        unsafe { mem::transmute(self) }
    }

    /// Creates a new `HipByt` from a short slice.
    ///
    /// # Safety
    ///
    /// The input slice's length MUST be at most `INLINE_CAPACITY`.
    pub(super) const unsafe fn inline_unchecked(bytes: &[u8]) -> Self {
        // SAFETY: see function precondition
        let inline = unsafe { Inline::from_slice_copy_unchecked(bytes) };
        Self(HipVec::from_inline(inline))
    }

    // derived constructors

    /// Creates a new `HipByt` from a vector.
    ///
    /// Will normalize the representation depending on the size of the vector.
    #[inline]
    pub(crate) fn from_vec_normalized(vec: Vec<u8>) -> Self {
        Self(HipVec::from_vec_normalized(vec))
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
    pub(super) fn detach(&mut self) {
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
