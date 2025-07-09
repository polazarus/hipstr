use core::mem::{ManuallyDrop, MaybeUninit};
use core::num::NonZeroU8;
use core::ptr::NonNull;

use super::borrowed::Borrowed;
use super::inline::InlineVec;
use super::{Allocated, INLINE_BYTES, WORD_SIZE_M1};
use crate::backend::Backend;

#[derive(Clone, Copy)]
#[repr(C)]
pub(crate) struct Pivot {
    _align: [usize; 0],

    #[cfg(target_endian = "little")]
    pub(crate) tag_byte: NonZeroU8,
    #[cfg(target_endian = "little")]
    pub(crate) _word_remainder: MaybeUninit<[u8; WORD_SIZE_M1]>,
    #[cfg(target_endian = "little")]
    pub(crate) _word1: MaybeUninit<*mut ()>,

    pub(crate) _word2: MaybeUninit<*mut ()>,

    #[cfg(target_endian = "big")]
    pub(crate) _word1: MaybeUninit<*mut ()>,
    #[cfg(target_endian = "big")]
    pub(crate) _word_remainder: MaybeUninit<[u8; WORD_SIZE_M1]>,
    #[cfg(target_endian = "big")]
    pub(crate) tag_byte: NonZeroU8,
}

#[derive(Clone, Copy)]
#[repr(C)]
pub(crate) struct WordView {
    #[cfg(target_endian = "little")]
    pub(crate) tag: usize,

    pub(crate) _others: [MaybeUninit<*mut ()>; 2],

    #[cfg(target_endian = "big")]
    pub(crate) tag: usize,
}

#[repr(C)]
pub(crate) struct SliceView<T> {
    #[cfg(target_endian = "little")]
    pub(crate) tag: usize,

    /// Pointer to the slice data
    pub(crate) ptr: NonNull<T>,

    /// Length of the slice
    pub(crate) len: usize,

    #[cfg(target_endian = "big")]
    pub(crate) tag: usize,
}

impl<T> Copy for SliceView<T> {}

impl<T> Clone for SliceView<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> SliceView<T> {
    pub(crate) fn as_slice(&self) -> &[T] {
        unsafe {
            // SAFETY: The pointer is guaranteed to be valid and the length is non-negative.
            core::slice::from_raw_parts(self.ptr.as_ptr(), self.len)
        }
    }
}

#[repr(C)]
pub(crate) union Union<'borrow, T, B: Backend> {
    /// Heap-allocated
    pub(crate) allocated: ManuallyDrop<Allocated<T, B>>,

    /// Borrowed slice
    pub(crate) borrowed: Borrowed<'borrow, T>,

    /// Pivot representation with niche
    pub(crate) pivot: Pivot,

    /// View to access the tagged word
    pub(crate) words: WordView,

    /// View to access the slice
    pub(crate) slice: SliceView<T>,
}

pub enum Tag {
    Inline = 0b01,
    Thin = 0b10,
    Fat = 0b11,
    Borrowed = 0b00,
}
