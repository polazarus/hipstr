//! Inline buffers: a bit-packed length and the elements, within the value.
//!
//! Only what the representations need: construction, length and raw access.
use core::marker::PhantomData;
use core::slice;

use super::layouts::{self, Layout};

#[repr(transparent)]
pub struct Base<T, L: Layout<T>> {
    repr: L,
    phantom: PhantomData<T>,
}

impl<T, L: Layout<T>> Base<T, L> {
    pub const CAPACITY: usize = L::CAPACITY;

    #[inline]
    pub const fn new() -> Self {
        Self {
            repr: L::EMPTY,
            phantom: PhantomData,
        }
    }

    /// Copies `slice` inline, in a `const` context too.
    ///
    /// # Panics
    ///
    /// Panics if `slice` is longer than [`CAPACITY`](Self::CAPACITY).
    #[inline]
    #[track_caller]
    pub const fn from_slice_copy(slice: &[T]) -> Self
    where
        T: Copy,
    {
        assert!(slice.len() <= L::CAPACITY, "too long to be inlined");
        let mut this = Self::new();
        if slice.is_empty() {
            // skip the copy: a `memcpy` call even for nothing
            return this;
        }
        // SAFETY: room for `slice.len()` elements (checked), copyable
        // elements, and `this` is fresh so the buffers do not overlap
        unsafe {
            this.as_mut_ptr()
                .copy_from_nonoverlapping(slice.as_ptr(), slice.len());
            this.set_len(slice.len());
        }
        this
    }

    #[inline]
    pub const fn len(&self) -> usize {
        layouts::len(&self.repr)
    }

    /// # Safety
    ///
    /// `new_len <= CAPACITY`, and the first `new_len` elements must be
    /// initialized.
    #[inline]
    pub const unsafe fn set_len(&mut self, new_len: usize) {
        // SAFETY: precondition
        unsafe {
            layouts::set_len(&mut self.repr, new_len);
        }
    }

    #[inline]
    pub const fn as_slice(&self) -> &[T] {
        let len = self.len();
        let ptr = self.as_ptr();
        // SAFETY: `len` initialized elements
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
}

impl<T, L: Layout<T>> Copy for Base<T, L> {}

impl<T, L: Layout<T>> Clone for Base<T, L> {
    fn clone(&self) -> Self {
        *self
    }
}
