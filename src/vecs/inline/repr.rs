//! Internal representation of inline vectors.

use core::mem::MaybeUninit;
use core::num::NonZeroUsize;
use core::ptr;
use core::ptr::NonNull;

use generic_array::{ArrayLength, GenericArray};

use super::length::{InlineLength, Seal};
use crate::common::derives::Copy;

pub const fn bits(n: usize) -> u32 {
    usize::BITS - n.leading_zeros()
}

#[repr(C)]
pub struct InlineRepr<T, L>
where
    L: InlineLength,
{
    #[cfg(target_endian = "little")]
    init_word: NonZeroUsize,

    rest: GenericArray<MaybeUninit<usize>, L::WordsM1>,

    #[cfg(target_endian = "big")]
    init_word: NonZeroUsize,

    phantom: core::marker::PhantomData<[T]>,
}

impl<T, N: InlineLength> Copy for InlineRepr<T, N> where
    <<N as Seal>::WordsM1 as ArrayLength>::ArrayType<MaybeUninit<usize>>: Copy
{
}

impl<T, N: InlineLength> Clone for InlineRepr<T, N>
where
    <<N as Seal>::WordsM1 as ArrayLength>::ArrayType<MaybeUninit<usize>>: Copy,
{
    fn clone(&self) -> Self {
        *self
    }
}

impl<T, L> InlineRepr<T, L>
where
    L: InlineLength,
{
    /// Creates a new, uninitialized inline representation.
    pub const fn new() -> Self {
        let init_word = const { NonZeroUsize::new(1).unwrap() };
        Self {
            init_word,
            rest: GenericArray::uninit(),
            phantom: core::marker::PhantomData,
        }
    }

    /// Creates a new, zeroed inline representation.
    pub const unsafe fn zeroed() -> Self {
        let init_word = NonZeroUsize::new(1).unwrap();
        Self {
            init_word,
            rest: unsafe { MaybeUninit::zeroed().assume_init() },
            phantom: core::marker::PhantomData,
        }
    }

    const LENGTH_AND_DATA: (usize, usize, usize, usize) = {
        let blob = L::USIZE;
        let t_align = align_of::<T>();
        let t_size = size_of::<T>();

        let (len_size, data_size) = if t_size == 0 {
            (size_of::<usize>(), usize::MAX >> 1)
        } else {
            let t_size_a = t_size / t_align;
            let blob_a = blob / t_align;
            let mut len_a = 1;

            let data_size = loop {
                if len_a >= blob_a {
                    break 0;
                }
                let max_data = (blob_a - len_a) / t_size_a;
                let needed_len_bits = (bits(max_data) + 1) as usize; // 1 bit for the tag
                let len_bits = 8 * len_a * t_align;
                if max_data == 0 || needed_len_bits <= len_bits {
                    break max_data;
                }
                len_a += 1;
            };

            let mut len_size = len_a * t_align;
            if len_size > size_of::<usize>() {
                len_size = size_of::<usize>();
            }

            (len_size, data_size)
        };

        let len_off;
        let data_off;
        if cfg!(target_endian = "little") {
            len_off = 0;
            data_off = len_size;
        } else {
            data_off = 0;
            len_off = blob - len_size;
        }
        (len_off, len_size, data_off, data_size)
    };

    /// Offset inside the representation where the length is stored.
    const LEN_OFFSET: usize = Self::LENGTH_AND_DATA.0;

    /// Size in bytes of the length field.
    const LEN_SIZE: usize = Self::LENGTH_AND_DATA.1;

    /// Offset inside the representation where the data starts.
    const DATA_OFFSET: usize = Self::LENGTH_AND_DATA.2;

    /// Maximum number of elements that can be stored inline.
    pub const CAPACITY: usize = Self::LENGTH_AND_DATA.3;

    /// Offset inside a `usize` where the length is stored.
    const IN_LEN_OFFSET: usize = if cfg!(target_endian = "little") {
        0
    } else {
        size_of::<usize>() - Self::LEN_SIZE
    };

    /// Checks if the given length can be stored inline.
    pub const fn is_len_valid(len: usize) -> bool {
        // strict comparison to take into account the tag bit
        (bits(len) as usize) < Self::LEN_SIZE * 8
    }

    /// Returns the length of the inline vector.
    pub const fn len(&self) -> usize {
        let mut value: usize = 0;
        let src: NonNull<u8> =
            unsafe { NonNull::from_ref(self).cast::<u8>().add(Self::LEN_OFFSET) };
        let dst: NonNull<u8> = NonNull::from_mut(&mut value).cast();

        unsafe {
            dst.add(Self::IN_LEN_OFFSET)
                .copy_from_nonoverlapping(src, Self::LEN_SIZE);
        }
        value >> 1
    }

    /// Sets the length of the inline vector.
    ///
    /// # Safety
    ///
    /// The length must be valid (i.e. `Self::is_len_valid(len)` must be true), and
    /// must not exceed the current capacity. Setting the length to a value
    /// greater than the current length is only safe if the new elements are
    /// properly initialized.
    pub const unsafe fn set_len(&mut self, len: usize) {
        debug_assert!(Self::is_len_valid(len));
        let value = (len << 1) | 1;

        let dst: NonNull<u8> =
            unsafe { NonNull::from_mut(self).cast::<u8>().add(Self::LEN_OFFSET) };
        let src: NonNull<u8> = NonNull::from_ref(&value).cast();

        unsafe {
            src.add(Self::IN_LEN_OFFSET)
                .copy_to_nonoverlapping(dst, Self::LEN_SIZE);
        }
    }

    /// Returns a pointer to the inline vector.
    pub const fn as_ptr(&self) -> *const T {
        if Self::CAPACITY == 0 {
            return ptr::dangling();
        }

        unsafe {
            NonNull::from_ref(self)
                .cast::<u8>()
                .add(Self::DATA_OFFSET)
                .cast()
                .as_ptr()
        }
    }

    /// Returns a mutable pointer to the inline vector.
    pub const fn as_mut_ptr(&mut self) -> *mut T {
        self.as_non_null().as_ptr()
    }

    /// Returns a non-null pointer to the inline vector.
    pub const fn as_non_null(&mut self) -> NonNull<T> {
        if Self::CAPACITY == 0 {
            return NonNull::dangling();
        }

        unsafe {
            NonNull::from_mut(self)
                .cast::<u8>()
                .add(Self::DATA_OFFSET)
                .cast()
        }
    }
}
