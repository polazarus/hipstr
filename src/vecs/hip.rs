use core::marker::PhantomData;
use core::mem::needs_drop;

use rules_derive::rules_derive;

use crate::common::derives::*;
use crate::common::{transmute2, transmute_mut, transmute_ref};
use crate::vecs::reprs::{Borrowed, FatOrThinRepr, Pivot, Sliced, UnknownSliced, Variant};
use crate::vecs::smart_fat::SmartFatVec;
use crate::vecs::{InlineVec, SmartThinVec};
use crate::Backend;

#[cfg(test)]
mod tests;

#[rules_derive(ConstDefault(Self::EMPTY))]
pub struct HipVec<'a, T, B: Backend>(Pivot, PhantomData<(B, &'a [T])>);
pub const INLINE_BYTES: usize = size_of::<Borrowed<()>>() - size_of::<u8>();

impl<'a, T, B: Backend> HipVec<'a, T, B> {
    const EMPTY: Self = Self::borrowed(&[]);

    #[must_use]
    pub const fn new() -> Self {
        Self::EMPTY
    }

    #[must_use]
    #[inline]
    pub const fn is_inline(&self) -> bool {
        self.0.is_inline()
    }

    #[must_use]
    #[inline]
    pub const fn is_allocated(&self) -> bool {
        !self.is_inline() && unsafe { self.as_sliced_unchecked() }.is_allocated()
    }

    #[must_use]
    #[inline]
    pub const fn is_borrowed(&self) -> bool {
        !self.is_inline() && unsafe { self.as_sliced_unchecked() }.is_borrowed()
    }

    #[must_use]
    #[inline]
    pub fn is_unique(&self) -> bool {
        self.is_inline()
            || (self.is_allocated() && unsafe { self.as_allocated_unchecked() }.owner.is_unique())
    }

    #[must_use]
    #[inline]
    pub const fn is_fat(&self) -> bool {
        self.is_allocated() && unsafe { self.as_allocated_unchecked() }.owner.is_fat()
    }

    #[must_use]
    pub const fn is_thin(&self) -> bool {
        self.is_allocated() && unsafe { self.as_allocated_unchecked() }.owner.is_thin()
    }

    #[must_use]
    pub const fn as_ptr(&self) -> *const T {
        if self.is_inline() {
            unsafe { self.as_inline_unchecked() }.as_ptr()
        } else {
            unsafe { self.as_sliced_unchecked() }.as_ptr()
        }
    }

    #[must_use]
    pub const fn len(&self) -> usize {
        if self.is_inline() {
            unsafe { self.as_inline_unchecked() }.len()
        } else {
            unsafe { self.as_sliced_unchecked() }.len()
        }
    }

    #[must_use]
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[must_use]
    pub const fn as_slice(&self) -> &[T] {
        if self.is_inline() {
            unsafe { self.as_inline_unchecked() }.as_slice()
        } else {
            unsafe { self.as_sliced_unchecked() }.as_slice()
        }
    }

    const unsafe fn as_inline_unchecked(&self) -> &InlineVec<T, INLINE_BYTES> {
        debug_assert!(self.is_inline());
        // SAFETY: precondition
        unsafe { transmute_ref::<Self, InlineVec<T, INLINE_BYTES>>(self) }
    }

    const unsafe fn as_inline_mut_unchecked(&mut self) -> &mut InlineVec<T, INLINE_BYTES> {
        debug_assert!(self.is_inline());
        // SAFETY: precondition
        unsafe { transmute_mut::<Self, InlineVec<T, INLINE_BYTES>>(self) }
    }

    const unsafe fn as_sliced_unchecked(&self) -> &UnknownSliced<T> {
        debug_assert!(!self.is_inline());
        // SAFETY: precondition
        unsafe { transmute_ref::<Self, UnknownSliced<T>>(self) }
    }

    const unsafe fn as_allocated_unchecked(&self) -> &Allocated<T, B> {
        debug_assert!(self.is_allocated());
        // SAFETY: precondition
        unsafe { transmute_ref::<Self, Allocated<T, B>>(self) }
    }

    const unsafe fn as_allocated_mut_unchecked(&mut self) -> &mut Allocated<T, B> {
        debug_assert!(self.is_allocated());
        // SAFETY: precondition
        unsafe { transmute_mut::<Self, Allocated<T, B>>(self) }
    }

    #[must_use]
    pub const fn borrowed(slice: &'a [T]) -> Self {
        let borrowed = Borrowed::<'a, T>::new(slice);
        unsafe { Self::from_sliced(borrowed) }
    }

    #[must_use]
    pub const fn from_inline(inline: InlineVec<T, INLINE_BYTES>) -> Self {
        unsafe { transmute2(inline) }
    }

    #[must_use]
    pub(super) const unsafe fn from_sliced<O>(owned: Sliced<T, O>) -> Self {
        const {
            assert!(size_of::<O>() == size_of::<usize>());
        }
        unsafe { transmute2(owned) }
    }

    #[must_use]
    pub const fn from_smart_thin(v: SmartThinVec<T, B>) -> Self {
        let len = v.len();
        let ptr = v.as_ptr();

        #[cfg(debug_assertions)]
        let is_null = v.capacity() == 0;

        let this = unsafe {
            Self::from_sliced(Sliced {
                owner: v.into_repr(),
                ptr,
                len,
            })
        };

        #[cfg(debug_assertions)]
        if is_null {
            debug_assert!(this.is_borrowed());
        } else {
            debug_assert!(this.is_allocated());
        }

        this
    }

    const unsafe fn owner_mut_unchecked(&mut self) -> &mut Owner<T, B> {
        unsafe { &mut self.as_allocated_mut_unchecked().owner }
    }
}

impl<T, B: Backend> Drop for HipVec<'_, T, B> {
    fn drop(&mut self) {
        if self.is_inline() {
            if needs_drop::<T>() {
                // SAFETY: repr checked above
                let inline = unsafe { self.as_inline_mut_unchecked() };
                // SAFETY: will no be used after drop
                unsafe {
                    inline.drop_contents();
                }
            }
        } else if self.is_allocated() {
            // SAFETY: repr checked above
            let owner = unsafe { self.owner_mut_unchecked() };
            // SAFETY: will no be used after drop
            unsafe {
                owner.drop();
            }
        }
    }
}

type Allocated<T, B> = Sliced<T, Owner<T, B>>;

#[repr(transparent)]
struct Owner<T, B>(FatOrThinRepr<T, B>);

impl<T, B: Backend> Owner<T, B> {
    /// Drops the owner now.
    ///
    /// # Safety
    ///
    /// The owner must not be used after drop.
    unsafe fn drop(&mut self) {
        match self.0.into_split() {
            Variant::Thin(repr) => {
                // SAFETY: should not be used after drop
                let _ = unsafe { SmartThinVec::from_repr(repr) };
            }
            Variant::Fat(repr) => {
                // SAFETY: should not be used after drop
                let _ = unsafe { SmartFatVec::from_repr(repr) };
            }
        }
    }

    fn is_unique(&self) -> bool {
        self.0.as_ref().prefix.is_unique()
    }

    const fn is_fat(&self) -> bool {
        self.0.is_fat()
    }

    const fn is_thin(&self) -> bool {
        self.0.is_thin()
    }
}
