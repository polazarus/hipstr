use core::hint::unreachable_unchecked;
use core::mem::{transmute, ManuallyDrop, MaybeUninit};
use core::num::NonZeroU8;
use core::ptr::NonNull;

use super::borrowed::Borrowed;
use crate::backend::Backend;
use crate::vecs::hip::allocated::{Fat, SharedCountView, Thin};
use crate::vecs::hip::Inline;
use crate::vecs::{TAG_BORROWED_MASKED, TAG_FAT, TAG_INLINE, TAG_MASK, TAG_THIN};

const WORD_SIZE_M1: usize = size_of::<*mut ()>() - 1;

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

impl Pivot {
    pub const fn repr(&self) -> Repr {
        let byte = self.tag_byte.get() ;
        match byte & TAG_MASK {
            TAG_BORROWED_MASKED => Repr::Borrowed,
            TAG_INLINE => Repr::Inline,
            TAG_THIN => Repr::Thin,
            TAG_FAT => Repr::Fat,
            _ => unsafe { unreachable_unchecked() },
        }
    }

    pub const unsafe fn as_union<'borrow, T, B: Backend>(&self) -> &Union<'borrow, T, B> {
        unsafe {
            // SAFETY: The layout of `Pivot` matches the union layout.
            transmute::<&Pivot, &Union<'borrow, T, B>>(self)
        }
    }

    pub const unsafe fn as_inline<T>(&self) -> &Inline<T> {
        debug_assert!(
            matches!(self.repr(), Repr::Inline),
            "invalid repr (inline expected)"
        );
        unsafe {
            // SAFETY: The layout of `Pivot` matches the layout of `Inline<T>`.
            transmute::<&Pivot, &Inline<T>>(self)
        }
    }

    pub const unsafe fn as_slice_view<T>(&self) -> &SliceView<T> {
        debug_assert!(
            matches!(self.repr(), Repr::Thin | Repr::Fat | Repr::Borrowed),
            "invalid repr (thin, fat or borrowed expected)"
        );
        unsafe {
            // SAFETY: The layout of `Pivot` matches the layout of `SliceView<T>`.
            transmute::<&Pivot, &SliceView<T>>(self)
        }
    }

    pub const unsafe fn as_borrowed<'borrow, T>(&self) -> &Borrowed<'borrow, T> {
        debug_assert!(
            matches!(self.repr(), Repr::Borrowed),
            "invalid repr (borrowed expected)"
        );
        unsafe {
            // SAFETY: The layout of `Pivot` matches the layout of `Borrowed<'borrow, T>`.
            transmute::<&Pivot, &Borrowed<'borrow, T>>(self)
        }
    }
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
    /// Heap-allocated thin
    pub(crate) thin: ManuallyDrop<Thin<T, B>>,

    /// Heap-allocated fat
    pub(crate) fat: ManuallyDrop<Fat<T, B>>,

    /// Borrowed slice
    pub(crate) borrowed: Borrowed<'borrow, T>,

    /// Pivot representation with niche
    pub(crate) pivot: Pivot,

    /// View to access the tagged word
    pub(crate) words: WordView,

    /// View to access the slice
    pub(crate) slice: SliceView<T>,

    /// View to access the counter
    pub(crate) shared: SharedCountView<B>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Repr {
    Inline = 0b01,
    Thin = 0b10,
    Fat = 0b11,
    Borrowed = 0b00,
}
