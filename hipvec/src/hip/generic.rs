#![doc(hidden)]

use alloc::vec::Vec;
use core::marker::PhantomData;

use const_default::ConstDefault;

use super::Repr;
use super::base::{Base, Mut};
use crate::backend::Backend;
use crate::common::markers::{self, Copyness};
use crate::thin;

#[repr(transparent)]
pub struct HipVec<'a, T, B: Backend, M: Copyness = markers::NonCopy> {
    base: Base<'a, T, B>,
    marker: PhantomData<M>,
}

impl<'a, T, B: Backend, M: Copyness> HipVec<'a, T, B, M> {
    pub const fn new() -> Self {
        Self {
            base: Base::new(),
            marker: PhantomData,
        }
    }

    pub const fn borrowed(slice: &'a [T]) -> Self {
        Self {
            base: Base::from_borrowed_slice(slice),
            marker: PhantomData,
        }
    }

    #[inline]
    pub const fn as_ptr(&self) -> *const T {
        self.base.as_ptr()
    }

    #[inline]
    pub const fn len(&self) -> usize {
        self.base.len()
    }

    #[inline]
    pub const fn as_slice(&self) -> &[T] {
        self.base.as_slice()
    }

    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.base.is_empty()
    }

    #[inline]
    pub fn as_mut_slice(&mut self) -> Option<&mut [T]> {
        self.base.as_mut_slice()
    }

    #[inline]
    pub const fn repr(&self) -> Repr {
        self.base.repr()
    }
}

impl<'a, T: Clone, B: Backend> HipVec<'a, T, B, markers::NonCopy> {
    #[inline]
    pub fn mutate(&mut self) -> RefMut<'_, 'a, T, B> {
        self.base.make_unique_clone();
        RefMut {
            base: self.base.mutate_unchecked(),
        }
    }

    #[inline]
    pub fn to_mut_slice(&mut self) -> &mut [T] {
        self.base.to_mut_slice()
    }
}

impl<'a, T: Copy, B: Backend> HipVec<'a, T, B, markers::Copy> {
    #[inline]
    pub fn mutate(&mut self) -> RefMut<'_, 'a, T, B> {
        self.base.make_unique_copy();
        RefMut {
            base: self.base.mutate_unchecked(),
        }
    }

    #[inline]
    pub fn to_mut_slice(&mut self) -> &mut [T] {
        self.base.to_mut_slice_copy()
    }
}

impl<'a, T, B: Backend> HipVec<'a, T, B, markers::NonCopy> {
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            base: Base::with_capacity(capacity),
            marker: PhantomData,
        }
    }
}

impl<'a, T, B: Backend, M: Copyness> Default for HipVec<'a, T, B, M> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, T, B: Backend, M: Copyness> ConstDefault for HipVec<'a, T, B, M> {
    const DEFAULT: Self = Self::new();
}

impl<'a, T, B: Backend, M: Copyness> Drop for HipVec<'a, T, B, M> {
    fn drop(&mut self) {
        unsafe {
            // no real need to switch on the copyness, drop is already lazy with needs_drop
            self.base.drop();
        }
    }
}

impl<'a, T, B: Backend, M: Copyness> From<thin::GenericThinVec<T, M>> for HipVec<'a, T, B, M> {
    fn from(thin_vec: thin::GenericThinVec<T, M>) -> Self {
        Self {
            base: Base::from_any_thin_base(thin_vec.into_base()),
            marker: PhantomData,
        }
    }
}

pub struct RefMut<'a, 'b, T, B: Backend> {
    base: Mut<'a, 'b, T, B>,
}

impl<'a, 'b, T, B: Backend> RefMut<'a, 'b, T, B> {
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        self.base.as_mut_slice()
    }

    #[inline]
    pub fn push(&mut self, value: T) {
        let _ = self.base.push_mut(value);
    }
}

impl<'a, T, B: Backend, M: Copyness> From<Vec<T>> for HipVec<'a, T, B, M> {
    fn from(value: Vec<T>) -> Self {
        Self {
            base: Base::from_wide(value),
            marker: PhantomData,
        }
    }
}
