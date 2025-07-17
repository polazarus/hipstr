use core::hint::unreachable_unchecked;
use core::marker::PhantomData;
use core::mem::{offset_of, transmute, ManuallyDrop, MaybeUninit};
use core::num::NonZeroU8;
use core::ptr::NonNull;

use crate::backend::Backend;
use crate::common::traits::MutVector;
use crate::vecs::hip::allocated::{Allocated, Fat, SharedCountView, Thin};
use crate::vecs::hip::Inline;
use crate::vecs::{TAG_BORROWED, TAG_BORROWED_MASKED, TAG_FAT, TAG_INLINE, TAG_MASK, TAG_THIN};
use crate::Rc;

const WORD_SIZE_M1: usize = size_of::<*mut ()>() - 1;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Tag {
    Borrowed = (TAG_BORROWED & TAG_MASK) as isize,
    Inline = (TAG_INLINE & TAG_MASK) as isize,
    Thin = (TAG_THIN & TAG_MASK) as isize,
    Fat = (TAG_FAT & TAG_MASK) as isize,
}

/// Internal pivot representation for a "hip" vector.
#[derive(Clone, Copy)]
#[repr(C)]
pub(crate) struct Repr {
    _align: [usize; 0],

    #[cfg(target_endian = "little")]
    tag_byte: NonZeroU8,

    #[cfg(target_endian = "little")]
    _word_remainder: MaybeUninit<[u8; WORD_SIZE_M1]>,

    #[cfg(target_endian = "little")]
    _word1: MaybeUninit<*mut ()>,

    _word2: MaybeUninit<*mut ()>,

    #[cfg(target_endian = "big")]
    _word1: MaybeUninit<*mut ()>,

    #[cfg(target_endian = "big")]
    _word_remainder: MaybeUninit<[u8; WORD_SIZE_M1]>,

    #[cfg(target_endian = "big")]
    tag_byte: NonZeroU8,
}

impl Repr {
    pub const fn repr(&self) -> Tag {
        let byte = self.tag_byte.get();
        match byte & TAG_MASK {
            TAG_BORROWED_MASKED => Tag::Borrowed,
            TAG_INLINE => Tag::Inline,
            TAG_THIN => Tag::Thin,
            TAG_FAT => Tag::Fat,
            _ => unsafe { unreachable_unchecked() },
        }
    }

    pub const unsafe fn inline<T>(&self) -> &Inline<T> {
        debug_assert!(
            size_of::<Inline<T>>() == size_of::<Repr>(),
            "size mismatch between Inline and Repr"
        );
        debug_assert!(
            matches!(self.repr(), Tag::Inline),
            "invalid repr (inline expected)"
        );
        unsafe {
            // SAFETY: The layout of `Pivot` matches the layout of `Inline<T>`.
            transmute::<&Repr, &Inline<T>>(self)
        }
    }

    pub const unsafe fn slice_view<T>(&self) -> &SliceView<T> {
        debug_assert!(
            matches!(self.repr(), Tag::Thin | Tag::Fat | Tag::Borrowed),
            "invalid repr (thin, fat or borrowed expected)"
        );
        // SAFETY: The layout of `Pivot` matches the layout of `SliceView<T>`.
        unsafe { transmute::<&Repr, &SliceView<T>>(self) }
    }

    pub const unsafe fn borrowed<'borrow, T>(&self) -> &Borrowed<'borrow, T> {
        debug_assert!(
            matches!(self.repr(), Tag::Borrowed),
            "invalid repr (borrowed expected)"
        );
        // SAFETY: The layout of `Pivot` matches the layout of `Borrowed<'borrow, T>`.
        unsafe { transmute::<&Repr, &Borrowed<'borrow, T>>(self) }
    }

    pub const unsafe fn thin<T, B: Backend>(&self) -> &Thin<T, B> {
        debug_assert!(
            matches!(self.repr(), Tag::Thin),
            "invalid repr (thin expected)"
        );
        // SAFETY: The layout of `Pivot` matches the layout of `Thin<T, B>`.
        unsafe { transmute::<&Repr, &Thin<T, B>>(self) }
    }

    pub const unsafe fn fat<T, B: Backend>(&self) -> &Fat<T, B> {
        debug_assert!(
            matches!(self.repr(), Tag::Fat),
            "invalid repr (fat expected)"
        );
        // SAFETY: The layout of `Pivot` matches the layout of `Fat<T, B>`.
        unsafe { transmute::<&Repr, &Fat<T, B>>(self) }
    }

    pub const unsafe fn shared_view<B: Backend>(&self) -> &SharedCountView<B> {
        debug_assert!(
            matches!(self.repr(), Tag::Thin | Tag::Fat),
            "invalid repr (thin or fat expected)"
        );
        // SAFETY: The layout of `Pivot` matches the layout of `SharedCountView<B>`.
        unsafe { transmute::<&Repr, &SharedCountView<B>>(self) }
    }

    pub const unsafe fn from_inline<T>(inline: Inline<T>) -> Repr {
        assert!(
            size_of::<Inline<T>>() == size_of::<Self>(),
            "size mismatch between Inline and Repr"
        );
        assert!(
            align_of::<Inline<T>>() <= align_of::<Self>(),
            "alignment mismatch between Inline and Repr (Repr alignment is insufficient)"
        );

        let inline = ManuallyDrop::new(inline);
        unsafe { InlineRepr { inline }.pivot }
    }

    pub const unsafe fn inline_mut<T>(&mut self) -> &mut Inline<T> {
        debug_assert!(
            size_of::<Inline<T>>() == size_of::<Repr>(),
            "size mismatch between Inline and Repr"
        );
        debug_assert!(
            matches!(self.repr(), Tag::Inline),
            "invalid repr (inline expected)"
        );

        unsafe { transmute::<&mut Self, &mut Inline<T>>(self) }
    }

    pub const unsafe fn thin_mut<T, B: Backend>(&mut self) -> &mut Thin<T, B> {
        debug_assert!(
            matches!(self.repr(), Tag::Thin),
            "invalid repr (thin expected)"
        );
        // SAFETY: The layout of `Pivot` matches the layout of `Thin<T, B>`.
        unsafe { transmute::<&mut Self, &mut Thin<T, B>>(self) }
    }

    pub const unsafe fn fat_mut<T, B: Backend>(&mut self) -> &mut Fat<T, B> {
        debug_assert!(
            matches!(self.repr(), Tag::Fat),
            "invalid repr (fat expected)"
        );
        // SAFETY: The layout of `Pivot` matches the layout of `Fat<T, B>`.
        unsafe { transmute::<&mut Self, &mut Fat<T, B>>(self) }
    }

    pub const unsafe fn slice_view_mut<T>(&mut self) -> &mut SliceView<T> {
        debug_assert!(
            matches!(self.repr(), Tag::Thin | Tag::Fat | Tag::Borrowed),
            "invalid repr (thin, fat or borrowed expected)"
        );
        // SAFETY: The layout of `Pivot` matches the layout of `SliceView<T>`.
        unsafe { transmute::<&mut Self, &mut SliceView<T>>(self) }
    }
}

union InlineRepr<T> {
    pivot: Repr,
    inline: ManuallyDrop<Inline<T>>,
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
    pub(crate) pivot: Repr,

    /// View to access the tagged word
    pub(crate) words: WordView,

    /// View to access the slice
    pub(crate) slice: SliceView<T>,

    /// View to access the counter
    pub(crate) shared: SharedCountView<B>,
}

#[repr(usize)]
#[derive(Clone, Copy)]
pub(crate) enum BorrowedTag {
    Value = TAG_BORROWED as usize, // reuse a tag of a fat vector
}

#[repr(C)]
pub(crate) struct Borrowed<'borrow, T> {
    #[cfg(target_endian = "little")]
    pub(crate) tag: BorrowedTag,

    pub(crate) ptr: *const T,

    pub(crate) len: usize,

    #[cfg(target_endian = "big")]
    pub tag: BorrowedTag,

    pub(crate) phantom: PhantomData<&'borrow [T]>,
}

impl<'borrow, T> Borrowed<'borrow, T> {
    #[inline]
    pub(crate) const fn new(slice: &'borrow [T]) -> Self {
        Self {
            tag: BorrowedTag::Value,
            ptr: slice.as_ptr(),
            len: slice.len(),
            phantom: PhantomData,
        }
    }

    #[inline]
    pub(crate) const fn as_slice(&self) -> &'borrow [T] {
        // SAFETY: validity ensured by construction.
        unsafe { core::slice::from_raw_parts(self.ptr as *const T, self.len) }
    }
}

impl<'borrow, T> Copy for Borrowed<'borrow, T> {}

impl<'borrow, T> Clone for Borrowed<'borrow, T> {
    fn clone(&self) -> Self {
        *self
    }
}

const ASSERTS: () = {
    assert!(offset_of!(Borrowed::<u8>, ptr) == offset_of!(SliceView::<u8>, ptr));
    assert!(offset_of!(Thin::<u8, Rc>, ptr) == offset_of!(SliceView::<u8>, ptr));
    assert!(offset_of!(Fat::<u8, Rc>, ptr) == offset_of!(SliceView::<u8>, ptr));
};
