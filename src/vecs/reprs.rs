//! Definitions of various vector representations: thin, fat, and fat-or-thin.
//!
//! This module defines the data structures and associated functions for handling
//! different vector representations:
//! - thin: `ThinRepr`, `ThinHeader`
//! - fat: `FatRepr`, `FatInner`
//! - fat-or-thin: `FatOrThinRepr`, `FatOrThinView

//#![allow(unused)]

use core::alloc::Layout;
use core::marker::PhantomData;
use core::mem::{self, offset_of, transmute};
use core::ptr::{self, NonNull};

use crate::common::ZeroUsize;
use const_default::ConstDefault;

pub const MAX_TAG_SIZE: usize = 2; // 2 bits

/// Minimal alignment to store the tag
pub const MIN_ALIGN: usize = 1 << MAX_TAG_SIZE; // minimal alignment is 4 bytes

/// Mask to extract the inline tag
pub const INLINE_MASK: usize = 1;

/// Tag for sliced representation (borrowed or allocated)
pub const SLICED: usize = 0b10;

/// Tag for inline representation
pub const INLINE: usize = 1; // 0b01

/// A thin vector header with prefix.
#[derive(Clone, Copy, Debug)]
#[repr(C)]
pub struct ThinHeader<T, P> {
    pub prefix: P,
    _ptr: ZeroUsize,
    pub cap: usize,
    pub len: usize,
    _phantom: PhantomData<T>,
}

impl<T, P> ThinHeader<T, P> {
    const DATA_OFFSET: usize = Self::layout(0).unwrap().1;

    /// Given a capacity, computes a `ThinVec` layout, the offset (in bytes) of
    /// the payload, and the rounded up capacity.
    #[inline]
    pub const fn layout(payload: usize) -> Option<(Layout, usize, usize)> {
        let layout = Layout::new::<Self>();
        let Ok(arr) = Layout::array::<T>(payload) else {
            return None;
        };
        let Ok((layout, offset)) = layout.extend(arr) else {
            return None;
        };
        let layout = layout.pad_to_align();

        // get the payload possibly rounded up to maximize possible occupancy in
        // closely in the computed layout
        let round_up_payload = if size_of::<T>() == 0 {
            usize::MAX
        } else {
            (layout.size() - offset) / mem::size_of::<T>()
        };

        #[cfg(not(coverage))]
        debug_assert!(payload <= round_up_payload, "invalid roundup");

        Some((layout, offset, round_up_payload))
    }

    pub const fn data(header: NonNull<Self>) -> NonNull<T> {
        unsafe { header.byte_add(Self::DATA_OFFSET).cast() }
    }
}

impl<T, P> ConstDefault for ThinHeader<T, P>
where
    P: ConstDefault,
{
    const DEFAULT: Self = Self {
        prefix: P::DEFAULT,
        _ptr: ZeroUsize::Zero,
        cap: 0,
        len: 0,
        _phantom: PhantomData,
    };
}

/// A fat vector representation with prefix.
#[repr(C)]
pub struct FatInner<T, P> {
    pub prefix: P,
    pub ptr: NonNull<T>,
    pub cap: usize,
    pub len: usize,
}

/// A tagged pointer, guaranted to have a niche at zero, but can be null.
#[repr(transparent)]
pub struct MagicPointer<T, const TAG: usize = SLICED> {
    inner: NonNull<T>,
}

impl<T, const TAG: usize> Copy for MagicPointer<T, TAG> {}

impl<T, const TAG: usize> Clone for MagicPointer<T, TAG> {
    #[cfg_attr(coverage_nightly, coverage(off))]
    fn clone(&self) -> Self {
        *self
    }
}

/// A thin vector representation.
pub type ThinRepr<T, P> = MagicPointer<ThinHeader<T, P>>;

impl<T, P> ThinRepr<T, P> {
    pub const fn data(self) -> NonNull<T> {
        if let Some(header) = self.get() {
            ThinHeader::data(header)
        } else {
            NonNull::dangling()
        }
    }
}

/// An indirect fat vector representation.
pub type FatRepr<T, P> = MagicPointer<FatInner<T, P>>;

/// A representation that can be either fat or thin.
///
/// It can be safely transmuted to either `FatRepr` or `ThinRepr` based on the
/// the result of `is_fat` or `is_thin`.
pub type FatOrThinRepr<T, P> = MagicPointer<FatOrThinView<T, P>>;

impl<T, const TAG: usize> MagicPointer<T, TAG> {
    /// Checks if the pointer is null.
    ///
    /// The underlying representation is a tagged null.
    const fn is_null(self) -> bool {
        let addr: usize = unsafe { transmute(self.inner) };
        addr == SLICED
    }

    /// A null magic pointer.
    pub const NULL: Self = Self {
        inner: NonNull::new(ptr::without_provenance_mut(TAG)).unwrap(),
    };

    /// Creates a new magic pointer from a non null pointer.
    pub const fn new(header: NonNull<T>) -> Self {
        Self {
            inner: unsafe { header.byte_add(TAG) },
        }
    }

    /// Gets the underlying pointer, or `None` if null.
    pub const fn get(self) -> Option<NonNull<T>> {
        if self.is_null() {
            None
        } else {
            let ptr = unsafe { self.inner.as_ptr().byte_sub(SLICED) };
            NonNull::new(ptr)
        }
    }

    /// Gets a reference to the underlying data, or `None` if null.
    pub const fn as_ref(&self) -> Option<&T> {
        match self.get() {
            Some(ptr) => unsafe { Some(ptr.as_ref()) },
            None => None,
        }
    }

    /// Gets a mutable reference to the underlying data, or `None` if null.
    #[allow(clippy::needless_pass_by_ref_mut)]
    pub const fn as_mut(&mut self) -> Option<&mut T> {
        match self.get() {
            Some(mut ptr) => unsafe { Some(ptr.as_mut()) },
            None => None,
        }
    }
}

impl<T, P> FatOrThinRepr<T, P> {
    /// Checks if the representation is fat and not null.
    #[inline]
    pub const fn is_fat(self) -> bool {
        let Some(r) = self.as_ref() else {
            return true;
        };
        r.ptr.is_some()
    }

    /// Checks if the representation is thin and not null.
    #[inline]
    pub const fn is_thin(self) -> bool {
        let Some(r) = self.as_ref() else {
            return true;
        };
        r.ptr.is_none()
    }

    /// Splits the representation into either a thin or fat variant.
    pub const fn into_split(self) -> Variant<ThinRepr<T, P>, FatRepr<T, P>> {
        if self.is_fat() {
            Variant::Fat(unsafe { mem::transmute::<Self, FatRepr<T, P>>(self) })
        } else {
            Variant::Thin(unsafe { mem::transmute::<Self, ThinRepr<T, P>>(self) })
            // NB: if the magic pointer contains null, we consider it as thin too
            //
            // because both fat and thin have the same layout when null, the choice does not matter
        }
    }
}

/// A variant that can be either thin or fat.
pub enum Variant<T, F> {
    Thin(T),
    Fat(F),
}

/// A view of a vector (indirect fat or direct thin).
#[repr(C)]
pub struct FatOrThinView<T, P> {
    pub prefix: P,
    pub ptr: Option<NonNull<T>>,
    pub cap: usize,
    pub len: usize,
}

/// Checks that the sizes, alignments and offsets of the fields
/// of the various representations are compatible.
#[cfg(debug_assertions)]
pub const fn check_fat_and_thin_compatibility<T, P>() {
    // Ensures that ThinHeader, FatInner and AllocatedView have the same size.
    assert!(size_of::<ThinHeader<T, P>>() == size_of::<FatOrThinView<T, P>>());
    assert!(size_of::<FatInner<T, P>>() == size_of::<FatOrThinView<T, P>>());

    // Ensures that the alignments of ThinHeader and FatInner are at least the alignment of FatOrThinView.
    assert!(align_of::<ThinHeader<T, P>>() >= align_of::<FatOrThinView<T, P>>());
    assert!(align_of::<FatInner<T, P>>() >= align_of::<FatOrThinView<T, P>>());

    // Ensures that this alignment is sufficient for the tag.
    assert!(align_of::<FatOrThinView<T, P>>() >= MIN_ALIGN);
    assert!(align_of::<ThinHeader<T, P>>() >= MIN_ALIGN);
    assert!(align_of::<FatInner<T, P>>() >= MIN_ALIGN);

    // Ensures that the field prefix is at the same offset in all three structs.
    assert!(offset_of!(ThinHeader<T, P>, prefix) == offset_of!(FatOrThinView<T, P>, prefix));
    assert!(offset_of!(FatInner<T, P>, prefix) == offset_of!(FatOrThinView<T, P>, prefix));

    // Ensures that the field len is at the same offset in all three structs
    assert!(offset_of!(ThinHeader<T, P>, len) == offset_of!(FatOrThinView<T, P>, len));
    assert!(offset_of!(FatInner<T, P>, len) == offset_of!(FatOrThinView<T, P>, len));

    // Ensures that the field cap is at the same offset in all three structs
    assert!(offset_of!(ThinHeader<T, P>, cap) == offset_of!(FatOrThinView<T, P>, cap));
    assert!(offset_of!(FatInner<T, P>, cap) == offset_of!(FatOrThinView<T, P>, cap));
}
