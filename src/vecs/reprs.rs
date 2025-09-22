#![allow(unused)]

use core::marker::PhantomData;
use core::mem::{self, offset_of, transmute, transmute_copy, MaybeUninit};
#[cfg(target_endian = "little")]
use core::num::NonZeroU8;
use core::num::NonZeroUsize;
use core::ptr::{self, NonNull};

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
    pub _ptr: ZeroUsize,
    pub cap: usize,
    pub len: usize,
    pub _phantom: PhantomData<T>,
}

/// A fat vector representation with prefix.
#[repr(C)]
pub struct FatInner<T, P> {
    pub prefix: P,
    pub ptr: NonNull<T>,
    pub cap: usize,
    pub len: usize,
}

/// A thin vector representation.
pub type ThinRepr<T, P> = MagicPointer<ThinHeader<T, P>>;
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

    pub const fn get(&self) -> Option<NonNull<T>> {
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
    pub fn as_mut(&mut self) -> Option<&mut T> {
        match self.get() {
            Some(ptr) => {
                debug_assert!(ptr.addr().get() & MASK == 0, "invalid pointer");
                unsafe { Some(&mut *ptr.as_ptr()) }
            }
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

/// Size of word minus a tagged byte.
const WORD_SIZE_M1: usize = size_of::<usize>() - 1;

#[derive(Clone, Copy)]
#[repr(C)]
pub struct Pivot {
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
        (self.tag_byte.get() as usize) & INLINE_MASK == INLINE
    }
}

pub type Borrowed<'borrow, T> = Sliced<T, BorrowedTag<'borrow>>;

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
pub enum BorrowedReserved {
    Value = THIN,
}

#[repr(C)]
pub struct Sliced<T, O> {
    #[cfg(target_endian = "little")]
    pub owner: O,

    pub ptr: *const T,
    pub len: usize,

    #[cfg(target_endian = "big")]
    pub owner: O,
}

impl<T, O> Sliced<T, O> {
    pub const fn as_ptr(&self) -> *const T {
        self.ptr
    }

    pub const fn len(&self) -> usize {
        self.len
    }

    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub const fn as_slice(&self) -> &[T] {
        unsafe { core::slice::from_raw_parts(self.ptr, self.len) }
    }
}

pub type UnknownSliced<T> = Sliced<T, NonZeroUsize>;

impl<T> UnknownSliced<T> {
    #[inline]
    pub const fn is_allocated(&self) -> bool {
        !self.is_borrowed()
    }

    #[inline]
    pub const fn is_borrowed(&self) -> bool {
        self.owner.get() & SLICED_PTR_MASK == 0
    }
}

pub struct ExposedNonNull<T> {
    addr: NonZeroUsize,
    phantom: PhantomData<NonNull<T>>,
}

impl<T> ExposedNonNull<T> {
    pub fn new(ptr: NonNull<T>) -> Self {
        Self {
            addr: ptr.addr(),
            phantom: PhantomData,
        }
    }
    pub const fn addr(&self) -> NonZeroUsize {
        self.addr
    }

    pub fn as_ptr(&self) -> *const T {
        ptr::with_exposed_provenance(self.addr.get())
    }

    pub fn as_mut_ptr(&self) -> *mut T {
        ptr::with_exposed_provenance_mut(self.addr.get())
    }
}
