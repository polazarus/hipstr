use core::marker::PhantomData;

use const_default::ConstDefault;
use rules_derive::rules_derive;

use crate::common::derives::*;
use crate::common::transmute2;
use crate::vecs::reprs::{Borrowed, FatOrThinRepr, Owned, Pivot, Sliced, UnknownSliced};
use crate::vecs::{InlineVec, SmartThinVec};
use crate::Backend;

#[rules_derive(ConstDefault(Self::EMPTY))]
pub struct HipVec<'a, T, B: Backend>(Pivot, PhantomData<(B, &'a [T])>);
pub const INLINE_BYTES: usize = size_of::<Borrowed<()>>() - size_of::<u8>();

impl<'a, T, B: Backend> HipVec<'a, T, B> {
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
    #[inline]
    pub fn is_unique(&self) -> bool {
        self.is_inline()
            || (self.is_owned()
                && unsafe { self.as_owned_unchecked() }
                    .owner
                    .as_ref()
                    .prefix
                    .is_unique())
    }

    #[must_use]
    #[inline]
    pub const fn is_fat(&self) -> bool {
        self.is_owned() && unsafe { self.as_owned_unchecked() }.owner.is_fat()
    }

    #[must_use]
    pub const fn is_thin(&self) -> bool {
        self.is_owned() && unsafe { self.as_owned_unchecked() }.owner.is_thin()
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
        unsafe { transmute2::<&Self, &InlineVec<T, INLINE_BYTES>>(self) }
    }

    const unsafe fn as_sliced_unchecked(&self) -> &UnknownSliced<T> {
        debug_assert!(!self.is_inline());
        // SAFETY: precondition
        unsafe { transmute2::<&Self, &UnknownSliced<T>>(self) }
    }

    const unsafe fn as_owned_unchecked(&self) -> &Owned<T, B> {
        debug_assert!(self.is_owned());
        // SAFETY: precondition
        unsafe { transmute2::<&Self, &Owned<T, B>>(self) }
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
    const fn from_owned(v: Owned<T, B>) -> Self {
        unsafe { Self::from_sliced(v) }
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
            debug_assert!(this.is_owned());
        }

        this
    }
}
