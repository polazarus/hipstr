use core::hint::unreachable_unchecked;
use core::marker::PhantomData;
use core::mem::ManuallyDrop;
use core::ptr::NonNull;
#[cfg(target_endian = "little")]
use core::{mem::MaybeUninit, num::NonZeroU8};

use crate::backend::Backend;
use crate::common::manually_drop_as_ref;
use crate::vecs::{InlineVec, SmartVec};

const WORD_SIZE_M1: usize = size_of::<*mut ()>() - 1;
const INLINE_BYTES: usize = size_of::<*mut ()>() * 3 - 1;

pub struct HipVec<'borrow, T, B: Backend> {
    pivot: Pivot,
    _marker: PhantomData<&'borrow (T, B)>,
}

#[derive(Clone, Copy)]
#[repr(C)]
struct Pivot {
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

#[derive(Clone, Copy)]
#[repr(C)]
struct WordView {
    #[cfg(target_endian = "little")]
    tag: usize,

    _others: [MaybeUninit<*mut ()>; 2],

    #[cfg(target_endian = "big")]
    tag: usize,
}

struct SliceView<T> {
    #[cfg(target_endian = "little")]
    tag: usize,

    /// Pointer to the slice data
    ptr: NonNull<T>,

    /// Length of the slice
    len: usize,

    #[cfg(target_endian = "big")]
    tag: usize,
}

impl<T> SliceView<T> {
    fn as_slice(&self) -> &[T] {
        unsafe {
            // SAFETY: The pointer is guaranteed to be valid and the length is non-negative.
            core::slice::from_raw_parts(self.ptr.as_ptr(), self.len)
        }
    }
}

impl<T> Copy for SliceView<T> {}

impl<T> Clone for SliceView<T> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
pub union Union<'borrow, T, B: Backend> {
    /// Inline representation
    pub inline: ManuallyDrop<InlineVec<T, INLINE_BYTES>>,

    /// Heap-allocated
    pub allocated: ManuallyDrop<Allocated<T, B>>,

    pub borrowed: Borrowed<'borrow, T>,

    /// Pivot representation with niche
    pivot: Pivot,

    /// View to access the tagged word
    words: WordView,

    /// View to access the slice
    slice: SliceView<T>,
}

#[repr(usize)]
#[derive(Clone, Copy)]
enum BorrowedTag {
    Value = TAG_FAT as usize, // reuse a tag of a fat vector
}

struct Borrowed<'borrow, T> {
    #[cfg(target_endian = "little")]
    pub tag: BorrowedTag,

    pub ptr: NonNull<T>,

    pub len: usize,

    #[cfg(target_endian = "big")]
    pub tag: BorrowedTag,

    phantom: PhantomData<&'borrow [T]>,
}

impl<'borrow, T> Copy for Borrowed<'borrow, T> {}

impl<'borrow, T> Clone for Borrowed<'borrow, T> {
    fn clone(&self) -> Self {
        *self
    }
}

struct Allocated<T, B: Backend> {
    owner: SmartVec<T, B>,
    ptr: NonNull<T>,
    len: usize,
}

impl<'borrow, T, B: Backend> Union<'borrow, T, B> {
    fn make(self) -> HipVec<'borrow, T, B> {
        unsafe {
            HipVec {
                pivot: self.pivot,
                _marker: PhantomData,
            }
        }
    }
}

const TAG_INLINE: u8 = 0b01;
const TAG_THIN: u8 = 0b10;
const TAG_FAT: u8 = 0b11;

enum Tag {
    Inline = 0b01,
    Thin = 0b10,
    Fat = 0b11,
    Borrowed = 0b100,
}

unsafe impl<T: Sync, B: Backend + Sync> Sync for HipVec<'_, T, B> {}
unsafe impl<T: Send, B: Backend + Send> Send for HipVec<'_, T, B> {}

impl<'borrow, T, B: Backend> HipVec<'borrow, T, B> {
    unsafe fn union(&self) -> &Union<'borrow, T, B> {
        unsafe { &*(self as *const Self as *const Union<'borrow, T, B>) }
    }

    unsafe fn tag(&self) -> Tag {
        let byte = unsafe { self.union().pivot.tag_byte.get() };
        match byte & 0x11 {
            0b00 => unsafe { unreachable_unchecked() },
            TAG_INLINE => Tag::Inline,
            TAG_THIN => Tag::Thin,
            TAG_FAT => {
                let word = unsafe { self.union().words.tag };
                if word >> 2 == 0 {
                    Tag::Borrowed
                } else {
                    Tag::Fat
                }
            }
            _ => Tag::Borrowed,
        }
    }

    unsafe fn as_borrowed_unchecked(&self) -> &Borrowed<'borrow, T> {
        unsafe { &self.union().borrowed }
    }

    unsafe fn as_allocated_unchecked(&self) -> &Allocated<T, B> {
        unsafe { manually_drop_as_ref(&self.union().allocated) }
    }

    unsafe fn as_inline_unchecked(&self) -> &InlineVec<T, INLINE_BYTES> {
        unsafe { manually_drop_as_ref(&self.union().inline) }
    }

    pub fn as_slice(&self) -> &[T] {
        match unsafe { self.tag() } {
            Tag::Inline => unsafe { self.as_inline_unchecked().as_slice() },
            _ => unsafe { &self.union().slice }.as_slice(),
        }
    }

    pub fn as_ptr(&self) -> *const T {
        match unsafe { self.tag() } {
            Tag::Inline => unsafe { self.as_inline_unchecked().as_ptr() },
            _ => unsafe { self.union().slice.ptr.as_ptr() },
        }
    }

    pub fn len(&self) -> usize {
        match unsafe { self.tag() } {
            Tag::Inline => unsafe { self.as_inline_unchecked().len() },
            _ => unsafe { self.union().slice.len },
        }
    }
}
