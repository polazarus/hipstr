//! Internal representation of hip vectors.

use core::marker::PhantomData;
use core::mem::{offset_of, transmute, MaybeUninit};
use core::ptr::{self, NonNull};

use const_default::ConstDefault;

use crate::vecs::fat::repr::FatRepr;
use crate::vecs::fat::SmartFatVec;
use crate::vecs::reprs::{MagicPointer, INLINE, INLINE_MASK, SLICED};
use crate::vecs::thin::repr::ThinRepr;
use crate::vecs::thin::SmartThinVec;
use crate::Backend;

pub type Allocated<T, B> = Sliced<T, Owner<T, B>>;

/// Owner of a owned hip vector.
#[repr(transparent)]
pub struct Owner<T, B>(FatOrThinRepr<T, B>);

impl<T, B: Backend> Owner<T, B> {
    /// Drops the owner now.
    ///
    /// # Safety
    ///
    /// The owner must not be used after drop.
    pub unsafe fn drop(&mut self) {
        match self.0.into_split() {
            Variant::Thin(repr) => {
                // SAFETY: should not be used after drop
                let _ = SmartThinVec(repr);
            }
            Variant::Fat(repr) => {
                // SAFETY: should not be used after drop
                let _ = SmartFatVec(repr);
            }
        }
    }

    pub fn is_unique(&self) -> bool {
        self.0.as_ref().unwrap().prefix.is_unique()
    }

    pub const fn is_fat(&self) -> bool {
        self.0.is_fat()
    }

    pub const fn is_thin(&self) -> bool {
        self.0.is_thin()
    }

    pub const fn counter(&self) -> &B {
        &self.0.as_ref().unwrap().prefix
    }

    pub const fn data(&self) -> NonNull<T> {
        if let Some(r) = self.0.as_ref() {
            if let Some(p) = r.ptr {
                p
            } else {
                let repr: &ThinRepr<T, B> = unsafe { &*ptr::from_ref(self).cast() };
                repr.data()
            }
        } else {
            NonNull::dangling()
        }
    }

    /// Sets the length of the owner.
    pub unsafe fn set_len(&mut self, len: usize) {
        if let Some(r) = self.0.as_mut() {
            debug_assert!(len < r.cap);
            r.len = len;
        }
    }

    /// Gets the length of the owner.
    pub const fn len(&self) -> usize {
        if let Some(r) = self.0.as_ref() {
            r.len
        } else {
            0
        }
    }
}

/// Pivot representation.
#[derive(Clone, Copy)]
#[repr(C)]
pub struct Pivot {
    #[cfg(target_endian = "little")]
    tagged_word: NonNull<()>,

    _rest: MaybeUninit<[*mut (); 2]>,

    #[cfg(target_endian = "big")]
    tagged_word: NonNull<()>,
}

impl Pivot {
    /// Checks if the hip vector is inline.
    #[inline]
    pub const fn is_inline(&self) -> bool {
        let word = unsafe { transmute::<NonNull<()>, usize>(self.tagged_word) };
        word & INLINE_MASK == INLINE
    }

    /// Checks if the hip vector is borrowed.
    #[inline]
    pub const fn is_borrowed(&self) -> bool {
        let word = unsafe { transmute::<NonNull<()>, usize>(self.tagged_word) };
        word == SLICED
    }

    /// Checks if the hip vector is allocated (fat or thin).
    #[inline]
    pub const fn is_allocated(&self) -> bool {
        !(self.is_inline() || self.is_borrowed())
    }
}

/// Representation of a borrowed hip vector.
pub type Borrowed<'borrow, T> = Sliced<T, BorrowedTag<'borrow>>;

impl<'borrow, T> Borrowed<'borrow, T> {
    pub const fn new(slice: &'borrow [T]) -> Self {
        Self {
            owner: BorrowedTag::DEFAULT,
            ptr: slice.as_ptr(),
            len: slice.len(),
        }
    }
}

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct BorrowedTag<'borrow> {
    _reserved: BorrowedReserved,
    _marker: PhantomData<&'borrow ()>,
}

impl ConstDefault for BorrowedTag<'_> {
    const DEFAULT: Self = Self {
        _reserved: BorrowedReserved::Value,
        _marker: PhantomData,
    };
}

#[derive(Clone, Copy)]
#[repr(usize)]
pub enum BorrowedReserved {
    Value = SLICED,
}

/// Representation of a sliced hip vector, that is, a non inline hip vector.
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

    pub const fn as_slice(&self) -> &[T] {
        unsafe { core::slice::from_raw_parts(self.ptr, self.len) }
    }
}

pub type UnknownSliced<T> = Sliced<T, NonNull<()>>;

/// A representation that can be either fat or thin.
///
/// It can be safely transmuted to either `FatRepr` or `ThinRepr` based on the
/// the result of `is_fat` or `is_thin`.
pub type FatOrThinRepr<T, P> = MagicPointer<FatOrThinView<T, P>>;

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
            Variant::Fat(unsafe { transmute::<Self, FatRepr<T, P>>(self) })
        } else {
            Variant::Thin(unsafe { transmute::<Self, ThinRepr<T, P>>(self) })
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

    use crate::vecs::fat::repr::FatInner;
    use crate::vecs::reprs::MIN_ALIGN;
    use crate::vecs::thin::repr::ThinHeader;

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
