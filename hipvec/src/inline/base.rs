//! Base implementation for inline vectors.
//!
//! Beware this module should not be publicly accessible as is:
//!
//! The `Base` struct is copyable, even if the elements are not copyable.
use alloc::slice;
use core::marker::PhantomData;

use super::layouts::{self, Layout};
use crate::common::methods;

pub(super) struct Base<T, L: Layout<T>> {
    repr: L,
    phantom: PhantomData<T>,
}

impl<T, L: Layout<T>> Base<T, L> {
    #[inline]
    pub const fn new() -> Self {
        Self {
            repr: L::EMPTY,
            phantom: PhantomData,
        }
    }

    #[inline]
    pub const fn len(&self) -> usize {
        layouts::len(&self.repr)
    }

    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    pub const fn from_array<const N: usize>(array: [T; N]) -> Self {
        assert!(N <= L::CAPACITY, "array length exceeds capacity");

        let mut base = Self::new();
        unsafe {
            base.set_len(N);
            let dst = base.as_mut_ptr();
            let src = array.as_ptr();
            dst.copy_from_nonoverlapping(src, N);
        }
        core::mem::forget(array);
        base
    }

    #[inline]
    pub const unsafe fn set_len(&mut self, new_len: usize) {
        unsafe {
            layouts::set_len(&mut self.repr, new_len);
        }
    }

    #[inline]
    pub const fn as_mut_slice(&mut self) -> &mut [T] {
        let len = self.len();
        let ptr = self.as_mut_ptr();
        unsafe { slice::from_raw_parts_mut(ptr, len) }
    }

    #[inline]
    pub const fn as_slice(&self) -> &[T] {
        let len = self.len();
        let ptr = self.as_ptr();
        unsafe { slice::from_raw_parts(ptr, len) }
    }

    #[inline]
    pub const fn as_mut_ptr(&mut self) -> *mut T {
        layouts::data_mut_ptr(&mut self.repr)
    }

    #[inline]
    pub const fn as_ptr(&self) -> *const T {
        layouts::data_ptr(&self.repr)
    }

    #[inline]
    pub const fn capacity(&self) -> usize {
        L::CAPACITY
    }

    pub const fn reserve(&mut self, additional: usize) {
        let len = self.len();
        let new_len = len + additional;
        assert!(new_len <= L::CAPACITY, "new length exceeds capacity");
    }

    #[inline]
    pub const fn reserve_exact(&mut self, additional: usize) {
        self.reserve(additional);
    }

    pub const fn push(&mut self, value: T) {
        methods::push!(self, value)
    }

    pub const fn pop(&mut self) -> Option<T> {
        methods::pop!(self)
    }

    pub const fn insert(&mut self, index: usize, value: T) {
        methods::insert!(self, index, value)
    }

    pub const fn spare_capacity_mut(&mut self) -> &mut [core::mem::MaybeUninit<T>] {
        methods::spare_capacity_mut!(self)
    }

    pub fn truncate(&mut self, new_len: usize) {
        methods::truncate!(self, new_len)
    }

    pub const fn truncate_copy(&mut self, new_len: usize)
    where
        T: Copy,
    {
        let len = self.len();
        if new_len < len {
            unsafe {
                self.set_len(new_len);
            }
        }
    }

    pub fn extend_from_slice(&mut self, slice: &[T])
    where
        T: Clone,
    {
        methods::extend_from_slice!(self, slice);
    }

    pub const fn extend_from_slice_copy(&mut self, slice: &[T])
    where
        T: Copy,
    {
        methods::extend_from_slice_copy!(self, slice);
    }
}

impl<T, L: Layout<T>> Copy for Base<T, L> where L: Copy {}

impl<T, L: Layout<T>> Clone for Base<T, L>
where
    L: Copy,
{
    fn clone(&self) -> Self {
        *self
    }
}
