//! Internal representation of hip vectors.

use core::marker::PhantomData;
use core::mem::{offset_of, transmute, MaybeUninit};
use core::ptr::{self, NonNull};

use const_default::ConstDefault;

use crate::vecs::reprs::{MagicPointer, INLINE, INLINE_MASK, SLICED};
use crate::vecs::thin::repr::ThinRepr;
use crate::vecs::thin::{SmartThinVec, ThinVec};
use crate::vecs::wide::repr::WideRepr;
use crate::vecs::wide::SmartWideVec;
use crate::Backend;

pub type Allocated<T, B> = Sliced<T, Owner<T, B>>;

/// Owner of a owned hip vector.
#[repr(transparent)]
pub struct Owner<T, B>(WideOrThinRepr<T, B>);

impl<T, B: Backend> Clone for Owner<T, B> {
    #[cfg_attr(coverage_nightly, coverage(off))] // trivial clone
    fn clone(&self) -> Self {
        *self
    }
}

impl<T, B: Backend> Copy for Owner<T, B> {}

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
                drop(SmartThinVec(repr));
            }
            Variant::Wide(repr) => {
                // SAFETY: should not be used after drop
                drop(SmartWideVec(repr));
            }
        }
    }

    pub fn is_unique(self) -> bool {
        self.0.as_ref().unwrap().prefix.is_unique()
    }

    pub const fn is_wide(self) -> bool {
        self.0.is_wide()
    }

    pub const fn is_thin(self) -> bool {
        self.0.is_thin()
    }

    pub const fn counter(&self) -> &B {
        &self.0.as_ref().unwrap().prefix
    }

    pub const fn as_mut_ptr(&mut self) -> *mut T {
        if let Some(r) = self.0.as_mut() {
            if let Some(p) = r.ptr {
                p.as_ptr()
            } else {
                let repr: &ThinRepr<T, B> = unsafe { &*ptr::from_mut(self).cast() };
                repr.data().as_ptr()
            }
        } else {
            ptr::dangling_mut()
        }
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

    pub const fn data_mut(&mut self) -> NonNull<T> {
        if let Some(r) = self.0.as_mut() {
            if let Some(p) = r.ptr {
                p
            } else {
                let repr: &ThinRepr<T, B> = unsafe { &*ptr::from_mut(self).cast() };
                repr.data()
            }
        } else {
            NonNull::dangling()
        }
    }

    /// Sets the length of the owner.
    #[inline]
    pub const unsafe fn set_len(&mut self, len: usize) {
        if let Some(r) = self.0.as_mut() {
            debug_assert!(len <= r.cap);
            r.len = len;
        }
    }

    /// Gets the length of the owner.
    #[inline]
    pub const fn len(self) -> usize {
        if let Some(r) = self.0.as_ref() {
            r.len
        } else {
            0
        }
    }

    /// Gets the capacity of the owner.
    #[inline]
    pub const fn capacity(self) -> usize {
        if let Some(r) = self.0.as_ref() {
            r.cap
        } else {
            0
        }
    }

    pub(crate) unsafe fn as_mut_thin_vec(&mut self) -> &mut ThinVec<T, B> {
        debug_assert!(self.is_thin());
        debug_assert!(self.is_unique());

        let ptr = ptr::from_mut(self).cast();
        // SAFETY: the caller ensures that the repr is thin and unique
        unsafe { &mut *ptr }
    }

    /// Converts the owner into a smart wide vector without checking.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the representation is wide.
    pub unsafe fn into_smart_wide_unchecked(self) -> SmartWideVec<T, B> {
        debug_assert!(self.is_wide());
        // SAFETY: the caller ensures that the repr is wide
        unsafe { transmute(self) }
    }
}

impl<T, B: Backend> From<SmartThinVec<T, B>> for Owner<T, B> {
    fn from(smart: SmartThinVec<T, B>) -> Self {
        unsafe { transmute(smart) }
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

    /// Checks if the hip vector is allocated (wide or thin).
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

/// A representation that can be either wide or thin.
///
/// It can be safely transmuted to either `WideRepr` or `ThinRepr` based on the
/// the result of `is_wide` or `is_thin`.
pub type WideOrThinRepr<T, P> = MagicPointer<WideOrThinView<T, P>>;

impl<T, P> WideOrThinRepr<T, P> {
    /// Checks if the representation is wide and not null.
    #[inline]
    pub const fn is_wide(self) -> bool {
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

    /// Splits the representation into either a thin or wide variant.
    pub const fn into_split(self) -> Variant<ThinRepr<T, P>, WideRepr<T, P>> {
        if self.is_wide() {
            Variant::Wide(unsafe { transmute::<Self, WideRepr<T, P>>(self) })
        } else {
            Variant::Thin(unsafe { transmute::<Self, ThinRepr<T, P>>(self) })
            // NB: if the magic pointer contains null, we consider it as thin too
            //
            // because both wide and thin have the same layout when null, the choice does not matter
        }
    }
}

/// A variant that can be either thin or wide.
pub enum Variant<T, F> {
    Thin(T),
    Wide(F),
}

/// A view of a vector (indirect wide or direct thin).
#[repr(C)]
pub struct WideOrThinView<T, P> {
    pub prefix: P,
    pub ptr: Option<NonNull<T>>,
    pub cap: usize,
    pub len: usize,
}

/// Checks that the sizes, alignments and offsets of the fields
/// of the various representations are compatible.
#[cfg(debug_assertions)]
pub const fn check_wide_and_thin_compatibility<T, P>() {
    // Ensures that ThinHeader, WideInner and WideOrThinView have the same size.

    use crate::vecs::reprs::MIN_ALIGN;
    use crate::vecs::thin::repr::ThinHeader;
    use crate::vecs::wide::repr::WideInner;

    assert!(size_of::<ThinHeader<T, P>>() == size_of::<WideOrThinView<T, P>>());
    assert!(size_of::<WideInner<T, P>>() == size_of::<WideOrThinView<T, P>>());

    // Ensures that the alignments of ThinHeader and WideInner are at least the alignment of FatOrThinView.
    assert!(align_of::<ThinHeader<T, P>>() >= align_of::<WideOrThinView<T, P>>());
    assert!(align_of::<WideInner<T, P>>() >= align_of::<WideOrThinView<T, P>>());

    // Ensures that this alignment is sufficient for the tag.
    assert!(align_of::<WideOrThinView<T, P>>() >= MIN_ALIGN);
    assert!(align_of::<ThinHeader<T, P>>() >= MIN_ALIGN);
    assert!(align_of::<WideInner<T, P>>() >= MIN_ALIGN);

    // Ensures that the field prefix is at the same offset in all three structs.
    assert!(offset_of!(ThinHeader<T, P>, prefix) == offset_of!(WideOrThinView<T, P>, prefix));
    assert!(offset_of!(WideInner<T, P>, prefix) == offset_of!(WideOrThinView<T, P>, prefix));

    // Ensures that the field len is at the same offset in all three structs
    assert!(offset_of!(ThinHeader<T, P>, len) == offset_of!(WideOrThinView<T, P>, len));
    assert!(offset_of!(WideInner<T, P>, len) == offset_of!(WideOrThinView<T, P>, len));

    // Ensures that the field cap is at the same offset in all three structs
    assert!(offset_of!(ThinHeader<T, P>, cap) == offset_of!(WideOrThinView<T, P>, cap));
    assert!(offset_of!(WideInner<T, P>, cap) == offset_of!(WideOrThinView<T, P>, cap));
}
