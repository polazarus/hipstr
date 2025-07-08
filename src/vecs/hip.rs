use core::hint::unreachable_unchecked;
use core::marker::PhantomData;
use core::mem::{offset_of, ManuallyDrop};
use core::ptr::NonNull;
#[cfg(target_endian = "little")]
use core::{mem::MaybeUninit, num::NonZeroU8};

use crate::backend::Backend;
use crate::common::manually_drop_as_ref;
use crate::vecs::{InlineVec, SmartThinVec, SmartVec};

#[cfg(test)]
mod tests;

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

#[repr(C)]
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

impl<T> Copy for SliceView<T> {}

impl<T> Clone for SliceView<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> SliceView<T> {
    fn as_slice(&self) -> &[T] {
        unsafe {
            // SAFETY: The pointer is guaranteed to be valid and the length is non-negative.
            core::slice::from_raw_parts(self.ptr.as_ptr(), self.len)
        }
    }
}

#[repr(C)]
union Union<'borrow, T, B: Backend> {
    /// Inline representation
    inline: ManuallyDrop<InlineVec<T, INLINE_BYTES>>,

    /// Heap-allocated
    allocated: ManuallyDrop<Allocated<T, B>>,

    /// Borrowed slice
    borrowed: Borrowed<'borrow, T>,

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

#[repr(C)]
struct Borrowed<'borrow, T> {
    #[cfg(target_endian = "little")]
    tag: BorrowedTag,

    ptr: *const T,

    len: usize,

    #[cfg(target_endian = "big")]
    pub tag: BorrowedTag,

    phantom: PhantomData<&'borrow [T]>,
}

impl<'borrow, T> Borrowed<'borrow, T> {
    #[inline]
    pub const fn new(slice: &'borrow [T]) -> Self {
        Self {
            tag: BorrowedTag::Value,
            ptr: slice.as_ptr(),
            len: slice.len(),
            phantom: PhantomData,
        }
    }

    #[inline]
    pub const fn as_slice(&self) -> &'borrow [T] {
        unsafe { core::slice::from_raw_parts(self.ptr, self.len) }
    }
}

impl<'borrow, T> Copy for Borrowed<'borrow, T> {}

impl<'borrow, T> Clone for Borrowed<'borrow, T> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
struct Allocated<T, B: Backend> {
    owner: SmartVec<T, B>,
    ptr: *const T,
    len: usize,
}

impl<'borrow, T, B: Backend> Union<'borrow, T, B> {
    const fn make(self) -> HipVec<'borrow, T, B> {
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
const TAG_THIN_FAT_BORROWED: u8 = 0b10;
const TAG_MASK: u8 = 0b11;

enum Tag {
    Inline = 0b01,
    Thin = 0b10,
    Fat = 0b11,
    Borrowed = 0b100,
}

unsafe impl<T: Sync, B: Backend + Sync> Sync for HipVec<'_, T, B> {}
unsafe impl<T: Send, B: Backend + Send> Send for HipVec<'_, T, B> {}

impl<'borrow, T, B: Backend> HipVec<'borrow, T, B> {
    #[inline]
    pub(crate) fn from_slice_clone(slice: &[T]) -> Self
    where
        T: Clone,
    {
        if slice.len() <= InlineVec::<T, INLINE_BYTES>::CAP {
            Self::from_inline(InlineVec::from_slice_clone(slice))
        } else {
            let stv = SmartThinVec::from_slice_clone(slice);
            let owner = SmartVec::from_thin(stv);
            Self::from_smart_vec(owner)
        }
    }

    #[inline]
    pub(crate) fn from_slice_copy(slice: &[T]) -> Self
    where
        T: Copy,
    {
        if slice.len() <= InlineVec::<T, INLINE_BYTES>::CAP {
            Self::from_inline(InlineVec::from_slice_copy(slice))
        } else {
            let stv = SmartThinVec::from_slice_copy(slice);
            let owner = SmartVec::from_thin(stv);
            Self::from_smart_vec(owner)
        }
    }

    #[inline]
    fn from_smart_vec(owner: SmartVec<T, B>) -> Self {
        let ptr = owner.as_ptr();
        let len = owner.len();
        let allocated = ManuallyDrop::new(Allocated { owner, ptr, len });
        let union = Union { allocated };
        union.make()
    }

    #[inline]
    const fn from_inline(inline: InlineVec<T, INLINE_BYTES>) -> Self {
        let inline = ManuallyDrop::new(inline);
        let union = Union { inline };
        union.make()
    }

    #[inline]
    pub fn is_unique(&self) -> bool {
        match unsafe { self.tag() } {
            Tag::Inline => true,
            Tag::Thin | Tag::Fat => unsafe { self.as_allocated_unchecked().owner.is_unique() },
            Tag::Borrowed => false,
        }
    }

    pub const fn is_owned(&self) -> bool {
        match unsafe { self.tag() } {
            Tag::Inline => true,
            Tag::Thin | Tag::Fat => true,
            Tag::Borrowed => false,
        }
    }

    pub const fn is_borrowed(&self) -> bool {
        match unsafe { self.tag() } {
            Tag::Inline => false,
            Tag::Thin | Tag::Fat => false,
            Tag::Borrowed => true,
        }
    }

    pub const fn is_inline(&self) -> bool {
        matches!(unsafe { self.tag() }, Tag::Inline)
    }

    #[inline]
    pub const fn borrowed(slice: &'borrow [T]) -> Self {
        let borrowed = Borrowed::new(slice);
        let union = Union { borrowed };
        union.make()
    }

    const unsafe fn union(&self) -> &Union<'borrow, T, B> {
        const {
            assert!(size_of::<Union<'borrow, T, B>>() == size_of::<Pivot>());
            assert!(align_of::<Union<'borrow, T, B>>() == align_of::<Pivot>());
        }

        unsafe { &*(&raw const self.pivot as *const Union<'borrow, T, B>) }
    }

    const unsafe fn union_mut(&mut self) -> &mut Union<'borrow, T, B> {
        unsafe { &mut *(&raw mut self.pivot as *mut Union<'borrow, T, B>) }
    }

    const unsafe fn tag(&self) -> Tag {
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

    #[inline]
    unsafe fn as_inline_unchecked(&self) -> &InlineVec<T, INLINE_BYTES> {
        unsafe { manually_drop_as_ref(&self.union().inline) }
    }

    #[inline]
    const unsafe fn as_slice_view(&self) -> &SliceView<T> {
        let view = unsafe { &self.union().slice };
        debug_assert!(
            view.tag & TAG_THIN_FAT_BORROWED as usize != 0,
            "invalid repr (allocated or borrowed expected)"
        );
        view
    }

    #[inline]
    pub fn as_slice(&self) -> &[T] {
        match unsafe { self.tag() } {
            Tag::Inline => unsafe { self.as_inline_unchecked().as_slice() },
            _ => unsafe { self.as_slice_view() }.as_slice(),
        }
    }

    #[inline]
    pub fn as_ptr(&self) -> *const T {
        match unsafe { self.tag() } {
            Tag::Inline => unsafe { self.as_inline_unchecked().as_ptr() },
            _ => unsafe { self.union().slice.ptr.as_ptr() },
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        match unsafe { self.tag() } {
            Tag::Inline => unsafe { self.as_inline_unchecked().len() },
            _ => unsafe { self.as_slice_view() }.len,
        }
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    pub fn force_clone_or_copy(&self) -> Self
    where
        T: Copy,
    {
        todo!()
    }
}
