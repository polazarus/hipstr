#![allow(unused)]

use core::marker::PhantomData;
use core::mem::{self, offset_of, MaybeUninit};
#[cfg(target_endian = "little")]
use core::num::NonZeroU8;
use core::ptr::{self, NonNull};

use rules_derive::rules_derive;

use crate::common::derives::ConstDefault;
use crate::common::ZeroUsize;

pub const TAG_SIZE: usize = 2; // 2 bits
pub const MIN_ALIGN: usize = 1 << TAG_SIZE; // minimal alignment is 4 bytes
pub const MASK: usize = (1 << TAG_SIZE) - 1; // 0b11
pub const THIN: usize = 2; // 0b10
pub const FAT: usize = 3; // 0b11
pub const INLINE: usize = 1; // 0b01

pub(super) type Null = ZeroUsize;

/// A thin vector header with prefix.
#[derive(Clone, Copy, Debug)]
#[repr(C)]
pub(super) struct ThinHeader<T, P> {
    pub(super) prefix: P,
    pub(super) _ptr: ZeroUsize,
    pub(super) cap: usize,
    pub(super) len: usize,
    pub(super) _phantom: PhantomData<T>,
}

/// A fat vector representation with prefix.
#[repr(C)]
pub(super) struct FatInner<T, P> {
    pub(super) prefix: P,
    pub(super) ptr: NonNull<T>,
    pub(super) cap: usize,
    pub(super) len: usize,
}

/// A thin vector representation.
#[repr(C)]
pub(super) struct ThinRepr<T, P> {
    inner: NonNull<ThinHeader<T, P>>,
}

impl<T, P> Copy for ThinRepr<T, P> {}

impl<T, P> Clone for ThinRepr<T, P> {
    fn clone(&self) -> Self {
        *self
    }
}

/// An indirect fat vector representation.
#[repr(C)]
pub(super) struct FatRepr<T, P> {
    inner: NonNull<FatInner<T, P>>,
}

impl<T, P> Copy for FatRepr<T, P> {}

impl<T, P> Clone for FatRepr<T, P> {
    fn clone(&self) -> Self {
        *self
    }
}

/// A representation that can be either fat or thin.
///
/// It can be safely transmuted to either `FatRepr` or `ThinRepr` based on the
/// the result of `is_fat` or `is_thin`.
pub(super) struct FatOrThinRepr<T, P> {
    ptr: NonNull<FatOrThinView<P>>,
    _phantom: PhantomData<T>,
}

impl<T, P> Copy for FatOrThinRepr<T, P> {}

impl<T, P> Clone for FatOrThinRepr<T, P> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T, P> ThinRepr<T, P> {
    pub(crate) const EMPTY: Self = {
        // SAFETY: just shifting a null pointer is safe as long as we don't dereference it
        let ptr = unsafe { ptr::without_provenance_mut::<ThinHeader<_, _>>(THIN) };
        Self {
            inner: NonNull::new(ptr).unwrap(),
        }
    };

    pub(crate) const fn new(header: NonNull<ThinHeader<T, P>>) -> Self {
        Self {
            inner: unsafe { header.byte_add(THIN) },
        }
    }

    pub(crate) const fn get(&self) -> Option<NonNull<ThinHeader<T, P>>> {
        let ptr = unsafe { self.inner.as_ptr().byte_sub(THIN) };
        NonNull::new(ptr)
    }
}

impl<T, P> FatRepr<T, P> {
    pub(crate) const EMPTY: Self = {
        // SAFETY: just shifting a null pointer is safe as long as we don't dereference it
        let ptr = unsafe { ptr::without_provenance_mut::<FatInner<T, P>>(FAT) };
        Self {
            inner: NonNull::new(ptr).unwrap(),
        }
    };

    pub(crate) const fn new(inner: NonNull<FatInner<T, P>>) -> Self {
        Self {
            inner: unsafe { inner.byte_add(FAT) },
        }
    }

    pub(crate) const fn get(&self) -> Option<NonNull<FatInner<T, P>>> {
        let ptr = unsafe { self.inner.as_ptr().byte_sub(FAT) };
        NonNull::new(ptr)
    }
}

impl<T, P> FatOrThinRepr<T, P> {
    pub(super) const EMPTY: Self = Self::from_thin(ThinRepr::EMPTY);

    pub(super) const fn from_thin(thin: ThinRepr<T, P>) -> Self {
        check_size_align_and_offsets::<T, P>();

        Self {
            ptr: thin.inner.cast(),
            _phantom: PhantomData,
        }
    }
    pub(super) const fn from_fat(fat: FatRepr<T, P>) -> Self {
        check_size_align_and_offsets::<T, P>();

        Self {
            ptr: fat.inner.cast(),
            _phantom: PhantomData,
        }
    }

    pub(super) fn is_fat(self) -> bool {
        self.ptr.addr().get() & MASK == FAT
    }

    pub(super) fn is_thin(self) -> bool {
        self.ptr.addr().get() & MASK == THIN
    }

    #[allow(clippy::transmute_ptr_to_ptr)]
    pub(super) fn split(&self) -> Variant<&ThinRepr<T, P>, &FatRepr<T, P>> {
        if self.is_thin() {
            Variant::Thin(unsafe { mem::transmute::<&Self, &ThinRepr<T, P>>(self) })
        } else {
            Variant::Fat(unsafe { mem::transmute::<&Self, &FatRepr<T, P>>(self) })
        }
    }

    #[allow(clippy::transmute_ptr_to_ptr)]
    pub(super) fn split_mut(&mut self) -> Variant<&mut ThinRepr<T, P>, &mut FatRepr<T, P>> {
        if self.is_thin() {
            Variant::Thin(unsafe { mem::transmute::<&mut Self, &mut ThinRepr<T, P>>(self) })
        } else {
            Variant::Fat(unsafe { mem::transmute::<&mut Self, &mut FatRepr<T, P>>(self) })
        }
    }

    #[allow(clippy::transmute_ptr_to_ptr)]
    pub(super) fn into_split(self) -> Variant<ThinRepr<T, P>, FatRepr<T, P>> {
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
pub(super) struct FatOrThinView<P> {
    pub(super) prefix: P,
    pub(super) _ptr: MaybeUninit<*mut ()>,
    pub(super) cap: usize,
    pub(super) len: usize,
}

pub(super) const fn check_size_align_and_offsets<T, P>() {
    // Ensures that ThinHeader, FatInner and AllocatedView have the same size.
    assert!(size_of::<ThinHeader<T, P>>() == size_of::<FatOrThinView<P>>());
    assert!(size_of::<FatInner<T, P>>() == size_of::<FatOrThinView<P>>());

    // Ensures that the alignments of ThinHeader and FatInner are at least the alignment of FatOrThinView.
    assert!(align_of::<ThinHeader<T, P>>() >= align_of::<FatOrThinView<P>>());
    assert!(align_of::<FatInner<T, P>>() >= align_of::<FatOrThinView<P>>());

    // Ensures that this alignment is sufficient for the tag.
    assert!(align_of::<FatOrThinView<P>>() >= TAG_SIZE);

    // Ensures that the field prefix is at the same offset in all three structs.
    assert!(offset_of!(ThinHeader<T, P>, prefix) == offset_of!(FatOrThinView<P>, prefix));
    assert!(offset_of!(FatInner<T, P>, prefix) == offset_of!(FatOrThinView<P>, prefix));

    // Ensures that the field len is at the same offset in all three structs
    assert!(offset_of!(ThinHeader<T, P>, len) == offset_of!(FatOrThinView<P>, len));
    assert!(offset_of!(FatInner<T, P>, len) == offset_of!(FatOrThinView<P>, len));

    // Ensures that the field cap is at the same offset in all three structs
    assert!(offset_of!(ThinHeader<T, P>, cap) == offset_of!(FatOrThinView<P>, cap));
    assert!(offset_of!(FatInner<T, P>, cap) == offset_of!(FatOrThinView<P>, cap));
}

/// Size of word minus a tagged byte.
const WORD_SIZE_M1: usize = size_of::<usize>() - 1;

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

impl Pivot {
    #[inline]
    pub const fn is_inline(&self) -> bool {
        (self.tag_byte.get() & INLINE as u8) == 0
    }
}

pub(super) type Borrowed<'borrow, T> = Sliced<T, BorrowedTag<'borrow>>;

impl<'borrow, T> Borrowed<'borrow, T> {
    pub const fn new(slice: &'borrow [T]) -> Self {
        Self {
            owner: BorrowedTag {
                _reserved: BorrowedReserved::Value,
                _marker: PhantomData,
            },
            ptr: slice.as_ptr(),
            len: slice.len(),
        }
    }
}

#[derive(Clone, Copy)]
pub struct BorrowedTag<'borrow> {
    _reserved: BorrowedReserved,
    _marker: PhantomData<&'borrow ()>,
}

#[derive(Clone, Copy)]
#[rules_derive(ConstDefault(Self::Value))]
#[repr(usize)]
pub(super) enum BorrowedReserved {
    Value = THIN,
}

pub(super) type Owned<T, B> = Sliced<T, FatOrThinRepr<T, B>>;

#[derive(Clone, Copy)]
#[repr(C)]
pub(super) struct Sliced<T, O> {
    #[cfg(target_endian = "little")]
    pub(super) owner: O,

    pub(super) ptr: *const T,
    pub(super) len: usize,

    #[cfg(target_endian = "big")]
    pub(super) owner: O,
}

pub(super) type UnknownSliced<T> = Sliced<T, *mut ()>;
