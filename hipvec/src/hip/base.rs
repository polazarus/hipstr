#![allow(dead_code)]

use core::marker::PhantomData;
use core::mem::{offset_of, transmute};
use core::num::NonZeroUsize;
use core::ptr::NonNull;

use crate::common::header::Header;
use crate::common::tagged_pointer::TaggedPointer;
use crate::thin::base::Base as ThinBase;

pub type InlineBase<T> = crate::inline::base::Base<T, crate::inline::layouts::BasicLayout>;

pub const SLICE_TAG: usize = 0b10;
pub const SLICE_TAG_MASK: usize = 0b11;

union NzOrNn<T> {
    word: NonZeroUsize,
    ptr: NonNull<T>,
}

impl<T> Copy for NzOrNn<T> {}
impl<T> Clone for NzOrNn<T> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
struct Pivot {
    #[cfg(target_endian = "little")]
    lsw: NzOrNn<()>,
    rest: [*mut (); 2],
    #[cfg(target_endian = "big")]
    lsw: NzOrNn<()>,
}

pub type Owner<T, P> = TaggedPointer<Header<T, P, Option<NonNull<T>>>, SLICE_TAG>;

#[repr(C)]
pub struct Sliced<T, Prefix> {
    #[cfg(target_endian = "little")]
    owner: Owner<T, Prefix>,

    slice: *mut [T],

    #[cfg(target_endian = "big")]
    owner: Owner<T, Prefix>,
}

enum Either<T, F> {
    Thin(T),
    Wide(F),
}

impl<T, Prefix> Sliced<T, Prefix> {
    const fn from_slice(slice: *mut [T]) -> Self {
        Self {
            owner: TaggedPointer::null(),
            slice,
        }
    }

    const fn from_thin<P>(mut thin: ThinBase<T, P>) -> Self {
        let slice: *mut [T] = thin.as_mut_slice();
        Self {
            owner: unsafe { transmute(thin) },
            slice: slice,
        }
    }

    fn owner(&self) -> Option<Either<ThinBase<T, Prefix>, ()>> {
        let owner = self.owner.as_non_null()?;
        let owner = unsafe { owner.as_ref() };
        if owner.ptr.is_some() {
            todo!("wide")
        } else {
            Some(Either::Thin(unsafe { transmute(self.owner) }))
        }
    }
}

const _: () = {
    assert!(size_of::<Pivot>() == size_of::<Sliced<(), usize>>());
    assert!(align_of::<Pivot>() == align_of::<Sliced<(), usize>>());
    assert!(offset_of!(Pivot, lsw) == offset_of!(Sliced<(), usize>, owner));
};

impl<T> Copy for Sliced<T, usize> {}
impl<T> Clone for Sliced<T, usize> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(transparent)]
pub struct Base<T, Prefix> {
    inner: Pivot,
    marker: PhantomData<(*mut T, *const Prefix)>,
}

impl<T, Prefix> Base<T, Prefix> {
    pub const fn is_inline(&self) -> bool {
        // SAFETY: Type invariant
        // Const-soundness: in the const context the base can only be created from a borrowed slice or an inline
        // Both of those guarantee that the lsw is initialized with a valid NonZeroUsize, and not a const pointer.
        unsafe { self.inner.lsw.word.get() & 1 == 1 }
    }

    pub const fn is_sliced(&self) -> bool {
        // SAFETY: Type invariant
        // Const-soundness: in the const context the base can only be created from a borrowed slice or an inline
        // Both of those guarantee that the lsw is initialized with a valid NonZeroUsize, and not a const pointer.
        unsafe { self.inner.lsw.word.get() & SLICE_TAG_MASK == SLICE_TAG }
    }

    pub const fn is_alloced(&self) -> bool {
        // SAFETY: Type invariant
        // Const-soundness: in the const context the base can only be created from a borrowed slice or an inline
        // Both of those guarantee that the lsw is initialized with a valid NonZeroUsize, and not a const pointer.
        unsafe {
            self.inner.lsw.word.get() & SLICE_TAG_MASK == SLICE_TAG
                && self.inner.lsw.word.get() & !SLICE_TAG_MASK != 0
        }
    }

    pub const fn is_borrowed(&self) -> bool {
        // SAFETY: Type invariant
        // Const-soundness: in the const context the base can only be created from a borrowed slice or an inline
        // Both of those guarantee that the lsw is initialized with a valid NonZeroUsize, and not a const pointer.
        unsafe {
            self.inner.lsw.word.get() & SLICE_TAG_MASK == SLICE_TAG
                && self.inner.lsw.word.get() & !SLICE_TAG_MASK == 0
        }
    }

    pub const fn from_borrowed_slice(slice: *mut [T]) -> Self {
        Self::from_sliced(Sliced::from_slice(slice))
    }

    const fn from_sliced(sliced: Sliced<T, Prefix>) -> Self {
        Self {
            inner: unsafe { core::mem::transmute(sliced) },
            marker: PhantomData,
        }
    }

    pub const fn from_thin(thin: ThinBase<T, Prefix>) -> Self {
        Self::from_sliced(Sliced::from_thin(thin))
    }

    pub const unsafe fn inline_unchecked(&self) -> &InlineBase<T> {
        debug_assert!(self.is_inline());

        // SAFETY: Type invariant
        unsafe { transmute(self) }
    }

    /// Retuns a mutable reference to the inline base.
    ///
    /// # Safety
    ///
    /// The caller must guarantee that the base is actually an inline base, and not a sliced one.
    ///
    /// See [`is_inline`](Self::is_inline) to check if the representation is inline.
    pub const unsafe fn inline_unchecked_mut(&mut self) -> &mut InlineBase<T> {
        debug_assert!(self.is_inline());

        // SAFETY: Type invariant
        unsafe { transmute(self) }
    }

    /// Retuns a mutable reference to the sliced base.
    ///
    /// # Safety
    ///
    /// The caller must guarantee that the base is actually a sliced base, and not an inline one.
    ///
    /// See [`is_sliced`](Self::is_sliced) to check if the representation is sliced.
    pub const unsafe fn sliced_unchecked(&self) -> &Sliced<T, Prefix> {
        debug_assert!(self.is_sliced());

        // SAFETY: Type invariant
        // Const-soundness: in the const context the base can only be created from a borrowed slice or an inline
        // Both of those guarantee that the lsw is initialized with a valid NonZeroUsize, and not a const pointer.
        unsafe { transmute(self) }
    }

    /// Retuns a mutable reference to the sliced base.
    ///
    /// # Safety
    ///
    /// The caller must guarantee that the base is actually a sliced base, and not an inline one.
    /// Additionally, the caller must guarantee that they have unique access to the base, as this returns a mutable reference.
    ///
    /// See [`is_sliced`](Self::is_sliced) to check if the representation is sliced.
    pub const unsafe fn sliced_unchecked_mut(&mut self) -> &mut Sliced<T, Prefix> {
        debug_assert!(self.is_sliced());

        // SAFETY: Type invariant
        // Const-soundness: in the const context the base can only be created from a borrowed slice or an inline
        // Both of those guarantee that the lsw is initialized with a valid NonZeroUsize, and not a const pointer.
        unsafe { transmute(self) }
    }
}

const _A: () = {
    assert!(core::mem::size_of::<Base<(), ()>>() == 24);
    assert!(32 == core::mem::size_of::<Option<Base<(), ()>>>());
};
