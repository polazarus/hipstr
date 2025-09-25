#![allow(unused)]

use core::alloc::Layout;
use core::marker::PhantomData;
use core::mem::{self, offset_of, transmute, transmute_copy, MaybeUninit};
#[cfg(target_endian = "little")]
use core::num::NonZeroU8;
use core::num::NonZeroUsize;
use core::ptr::{self, NonNull};

use const_default::ConstDefault;
use rules_derive::rules_derive;

use crate::common::derives::ConstDefault;
use crate::common::ZeroUsize;

pub const TAG_SIZE: usize = 2; // 2 bits
pub const MIN_ALIGN: usize = 1 << TAG_SIZE; // minimal alignment is 4 bytes
pub const INLINE_MASK: usize = 1;
pub const MASK: usize = (1 << TAG_SIZE) - 1; // 0b11
pub const SLICED: usize = 0b10;
pub const SLICED_PTR_MASK: usize = !MASK;
pub const THIN: usize = SLICED;
pub const FAT: usize = 3; // 0b11
pub const INLINE: usize = 1; // 0b01

pub type Null = ZeroUsize;

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

#[repr(C)]
pub struct MagicPointer<T> {
    inner: NonNull<T>,
}

impl<T> Copy for MagicPointer<T> {}

impl<T> Clone for MagicPointer<T> {
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

impl<T> MagicPointer<T> {
    const fn is_not_allocated(self) -> bool {
        let addr: usize = unsafe { transmute(self.inner) };
        addr == THIN
    }

    pub const EMPTY: Self = Self {
        inner: NonNull::new(ptr::without_provenance_mut(THIN)).unwrap(),
    };

    pub const fn new(header: NonNull<T>) -> Self {
        Self {
            inner: unsafe { header.byte_add(THIN) },
        }
    }

    pub const fn get(self) -> Option<NonNull<T>> {
        if self.is_not_allocated() {
            None
        } else {
            let ptr = unsafe { self.inner.as_ptr().byte_sub(THIN) };
            NonNull::new(ptr)
        }
    }

    pub const fn as_ref(&self) -> Option<&T> {
        match self.get() {
            Some(ptr) => unsafe { Some(ptr.as_ref()) },
            None => None,
        }
    }

    #[allow(clippy::needless_pass_by_ref_mut)]
    pub const fn as_mut(&mut self) -> Option<&mut T> {
        match self.get() {
            Some(mut ptr) => unsafe { Some(ptr.as_mut()) },
            None => None,
        }
    }
}

impl<T, P> FatOrThinRepr<T, P> {
    #[inline]
    pub const fn is_fat(self) -> bool {
        let Some(r) = self.as_ref() else {
            return true;
        };
        r.ptr.is_some()
    }

    #[inline]
    pub const fn is_thin(self) -> bool {
        let Some(r) = self.as_ref() else {
            return true;
        };
        r.ptr.is_none()
    }

    #[allow(clippy::transmute_ptr_to_ptr)]
    pub fn split(&self) -> Variant<&ThinRepr<T, P>, &FatRepr<T, P>> {
        if self.is_thin() {
            Variant::Thin(unsafe { mem::transmute::<&Self, &ThinRepr<T, P>>(self) })
        } else {
            Variant::Fat(unsafe { mem::transmute::<&Self, &FatRepr<T, P>>(self) })
        }
    }

    #[allow(clippy::transmute_ptr_to_ptr)]
    pub fn split_mut(&mut self) -> Variant<&mut ThinRepr<T, P>, &mut FatRepr<T, P>> {
        if self.is_thin() {
            Variant::Thin(unsafe { mem::transmute::<&mut Self, &mut ThinRepr<T, P>>(self) })
        } else {
            Variant::Fat(unsafe { mem::transmute::<&mut Self, &mut FatRepr<T, P>>(self) })
        }
    }

    pub fn into_split(self) -> Variant<ThinRepr<T, P>, FatRepr<T, P>> {
        if self.is_thin() {
            Variant::Thin(unsafe { mem::transmute::<Self, ThinRepr<T, P>>(self) })
        } else {
            Variant::Fat(unsafe { mem::transmute::<Self, FatRepr<T, P>>(self) })
        }
    }
}

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

pub const fn check_size_align_and_offsets<T, P>() {
    // Ensures that ThinHeader, FatInner and AllocatedView have the same size.
    assert!(size_of::<ThinHeader<T, P>>() == size_of::<FatOrThinView<T, P>>());
    assert!(size_of::<FatInner<T, P>>() == size_of::<FatOrThinView<T, P>>());

    // Ensures that the alignments of ThinHeader and FatInner are at least the alignment of FatOrThinView.
    assert!(align_of::<ThinHeader<T, P>>() >= align_of::<FatOrThinView<T, P>>());
    assert!(align_of::<FatInner<T, P>>() >= align_of::<FatOrThinView<T, P>>());

    // Ensures that this alignment is sufficient for the tag.
    assert!(align_of::<FatOrThinView<T, P>>() >= TAG_SIZE);

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
