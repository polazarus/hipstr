//! Base implementation for inline vectors.
//!
//! Beware this module should not be publicly accessible as is:
//!
//! The `Base` struct is copyable, even if the elements are not copyable.
use alloc::slice;
use core::marker::PhantomData;
use core::ptr::NonNull;

use super::layouts::{self, Layout};
use crate::common::methods;
use crate::traits::MutableVector;

pub(crate) struct Base<T, L: Layout<T>> {
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
    pub const fn as_non_null(&mut self) -> NonNull<T> {
        layouts::data_non_null(&mut self.repr)
    }

    #[inline]
    pub const fn as_ptr(&self) -> *const T {
        layouts::data_ptr(&self.repr)
    }

    #[inline]
    pub const fn capacity(&self) -> usize {
        L::CAPACITY
    }

    #[track_caller]
    pub const fn reserve(&mut self, additional: usize) {
        let len = self.len();
        let new_len = len + additional;
        assert!(new_len <= L::CAPACITY, "new length exceeds capacity");
    }

    #[inline]
    #[track_caller]
    pub const fn reserve_exact(&mut self, additional: usize) {
        self.reserve(additional);
    }

    #[inline]
    #[track_caller]
    pub const fn push(&mut self, value: T) {
        let _ = self.push_mut(value);
    }

    #[track_caller]
    pub const fn push_mut(&mut self, value: T) -> &mut T {
        methods::push_mut!(self, value)
    }

    pub const fn push_within_capacity(&mut self, value: T) -> Result<&mut T, T> {
        methods::push_within_capacity!(self, value)
    }

    pub const fn pop(&mut self) -> Option<T> {
        methods::pop!(self)
    }

    pub fn pop_if(&mut self, f: impl FnOnce(&mut T) -> bool) -> Option<T> {
        methods::pop_if!(self, f)
    }

    #[track_caller]
    pub const fn remove(&mut self, index: usize) -> T {
        methods::remove!(self, index)
    }

    #[track_caller]
    pub const fn swap_remove(&mut self, index: usize) -> T {
        methods::swap_remove!(self, index)
    }

    #[inline]
    #[track_caller]
    pub const fn insert(&mut self, index: usize, value: T) {
        let _ = self.insert_mut(index, value);
    }

    #[track_caller]
    pub const fn insert_mut(&mut self, index: usize, value: T) -> &mut T {
        methods::insert_mut!(self, index, value)
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

    #[track_caller]
    pub fn extend_from_slice(&mut self, slice: &[T])
    where
        T: Clone,
    {
        methods::extend_from_slice!(self, slice);
    }

    #[track_caller]
    pub const fn extend_from_slice_copy(&mut self, slice: &[T])
    where
        T: Copy,
    {
        methods::extend_from_slice_copy!(self, slice);
    }

    #[track_caller]
    pub const fn extend_from_array<const N: usize>(&mut self, array: [T; N]) {
        methods::extend_from_array!(self, array)
    }

    #[track_caller]
    pub const fn const_append(&mut self, other: &mut Self) {
        methods::append!(self, other);
    }

    #[track_caller]
    pub fn append(&mut self, other: &mut dyn MutableVector<Item = T>) {
        methods::append!(self, other);
    }

    #[track_caller]
    pub fn resize(&mut self, new_len: usize, value: T)
    where
        T: Clone,
    {
        methods::resize!(self, new_len, value);
    }

    #[track_caller]
    pub const fn resize_copy(&mut self, new_len: usize, value: T)
    where
        T: Copy,
    {
        methods::resize_copy!(self, new_len, value);
    }

    #[track_caller]
    pub fn resize_with(&mut self, new_len: usize, f: impl FnMut() -> T) {
        methods::resize_with!(self, new_len, f);
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
