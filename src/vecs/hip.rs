use core::marker::PhantomData;

use const_default::ConstDefault;
use rules_derive::rules_derive;

use crate::common::derives::*;
use crate::common::transmute2;
use crate::vecs::reprs::{Borrowed, FatOrThinRepr, Owned, Pivot, Sliced, UnknownSliced};
use crate::vecs::{InlineVec, SmartThinVec};
use crate::Backend;

#[rules_derive(ConstDefault(Self::EMPTY))]
pub struct HipVec<T, B: Backend>(Pivot, PhantomData<(B, [T])>);
pub const INLINE_BYTES: usize = size_of::<Borrowed<()>>() - size_of::<u8>();

impl<T, B: Backend> HipVec<T, B> {
    const EMPTY: Self = Self::from_inline(InlineVec::DEFAULT);

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
    pub const fn is_owned(&self) -> bool {
        !self.is_inline() && unsafe { self.as_sliced_unchecked() }.is_owned()
    }

    #[must_use]
    #[inline]
    pub const fn is_borrowed(&self) -> bool {
        !self.is_inline() && unsafe { self.as_sliced_unchecked() }.is_borrowed()
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

    pub const unsafe fn as_inline_unchecked(&self) -> &InlineVec<T, INLINE_BYTES> {
        debug_assert!(self.is_inline());
        // SAFETY: precondition
        unsafe { transmute2::<&Self, &InlineVec<T, INLINE_BYTES>>(self) }
    }

    pub(super) const unsafe fn as_sliced_unchecked(&self) -> &UnknownSliced<T> {
        debug_assert!(!self.is_inline());
        // SAFETY: precondition
        unsafe { transmute2::<&Self, &UnknownSliced<T>>(self) }
    }

    pub(super) const unsafe fn as_owned_unchecked(&self) -> &Owned<T, B> {
        debug_assert!(self.is_owned());
        // SAFETY: precondition
        unsafe { transmute2::<&Self, &Owned<T, B>>(self) }
    }

    #[must_use]
    pub const fn borrowed(slice: &[T]) -> Self {
        Self::from_sliced(Borrowed::new(slice))
    }

    #[must_use]
    pub const fn from_inline(inline: InlineVec<T, INLINE_BYTES>) -> Self {
        unsafe { transmute2(inline) }
    }

    #[must_use]
    pub(super) const fn from_sliced<O>(owned: Sliced<T, O>) -> Self {
        const {
            assert!(size_of::<O>() == size_of::<usize>());
        }
        unsafe { transmute2(owned) }
    }

    #[must_use]
    pub const fn from_smart_thin(v: SmartThinVec<T, B>) -> Self {
        let ptr = v.as_ptr();
        let len = v.len();
        Self::from_sliced(Owned {
            owner: FatOrThinRepr::from_thin(v.into_repr()),
            ptr,
            len,
        })
    }
}
