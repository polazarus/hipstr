use const_default::ConstDefault;

use super::base::{Base, Mut};
use crate::backend::Backend;
use crate::thin;

#[cfg(test)]
mod tests;

#[repr(transparent)]
pub struct HipVec<'a, T: Copy, B: Backend> {
    base: Base<'a, T, B>,
}

impl<'a, T: Copy, B: Backend> HipVec<'a, T, B> {
    pub const fn new() -> Self {
        Self { base: Base::new() }
    }

    pub const fn borrowed(slice: &'a [T]) -> Self {
        Self {
            base: Base::from_borrowed_slice(slice),
        }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            base: Base::with_capacity(capacity),
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
    pub fn mutate(&mut self) -> RefMut<'_, 'a, T, B> {
        self.base.make_unique_copy();

        RefMut {
            base: self.base.mutate_unchecked(),
        }
    }
}

impl<'a, T: Copy, B: Backend> HipVec<'a, T, B> {
    #[inline]
    pub fn to_mut_slice(&mut self) -> &mut [T] {
        self.base.to_mut_slice_copy()
    }
}

impl<'a, T: Copy, B: Backend> Default for HipVec<'a, T, B> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, T: Copy, B: Backend> ConstDefault for HipVec<'a, T, B> {
    const DEFAULT: Self = Self::new();
}

impl<'a, T: Copy, B: Backend> Drop for HipVec<'a, T, B> {
    fn drop(&mut self) {
        unsafe {
            self.base.drop_copy();
        }
    }
}

impl<'a, T: Copy, B: Backend> From<thin::copy::ThinVec<T>> for HipVec<'a, T, B> {
    fn from(thin_vec: thin::copy::ThinVec<T>) -> Self {
        Self {
            base: Base::from_any_thin_base(thin_vec.into_base()),
        }
    }
}

pub struct RefMut<'a, 'b, T: Copy, B: Backend> {
    base: Mut<'a, 'b, T, B>,
}

impl<'a, 'b, T: Copy, B: Backend> RefMut<'a, 'b, T, B> {
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        self.base.as_mut_slice()
    }

    #[inline]
    pub fn push(&mut self, value: T) {
        let _ = self.base.push_mut(value);
    }
}
