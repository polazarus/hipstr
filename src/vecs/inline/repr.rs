//! Internal representation of inline vectors.

use core::mem::MaybeUninit;
use core::num::NonZeroUsize;
use core::ptr;

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
    pub const fn new() -> Self {
        let init_word = const { NonZeroUsize::new(1).unwrap() };
        Self {
            init_word,
            rest: GenericArray::uninit(),
            phantom: core::marker::PhantomData,
        }
    }
    pub const fn zeroed() -> Self {
        let init_word = NonZeroUsize::new(1).unwrap();
        Self {
            init_word,
            rest: unsafe { MaybeUninit::zeroed().assume_init() },
            phantom: core::marker::PhantomData,
        }
    }

    const fn ptr(&self) -> *const u8 {
        ptr::from_ref(self).cast()
    }

    const fn mut_ptr(&mut self) -> *mut u8 {
        ptr::from_mut(self).cast()
    }

    pub const fn length_and_data() -> (usize, usize, usize, usize) {
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
    }

    const LEN_OFFSET: usize = Self::length_and_data().0;
    const LEN_SIZE: usize = Self::length_and_data().1;
    const DATA_OFFSET: usize = Self::length_and_data().2;

    pub const CAPACITY: usize = Self::length_and_data().3;

    pub const fn is_len_valid(len: usize) -> bool {
        // strict comparison to take into account the tag bit
        (bits(len) as usize) < Self::LEN_SIZE * 8
    }

    pub const fn len(&self) -> usize {
        let mut value: usize = 0;
        let src: *const u8 = unsafe { self.ptr().add(Self::LEN_OFFSET).cast() };
        let dst: *mut u8 = (&raw mut value).cast();

        let offset = if cfg!(target_endian = "little") {
            0
        } else {
            size_of::<usize>() - Self::LEN_SIZE
        };
        unsafe {
            dst.add(offset)
                .copy_from_nonoverlapping(src, Self::LEN_SIZE);
        }
        value >> 1
    }

    pub const unsafe fn set_len(&mut self, len: usize) {
        assert!(Self::is_len_valid(len));
        let dst: *mut u8 = unsafe { self.mut_ptr().add(Self::LEN_OFFSET).cast() };

        let offset = if cfg!(target_endian = "little") {
            0
        } else {
            size_of::<usize>() - Self::LEN_SIZE
        };
        let len = (len << 1) | 1;
        let src: *const u8 = (&raw const len).cast();
        let src = unsafe { src.add(offset) };
        unsafe {
            dst.copy_from_nonoverlapping(src, Self::LEN_SIZE);
        }
    }

    pub const fn as_ptr(&self) -> *const T {
        if Self::CAPACITY == 0 {
            return ptr::dangling();
        }

        unsafe { self.ptr().add(Self::DATA_OFFSET).cast() }
    }

    pub const fn as_mut_ptr(&mut self) -> *mut T {
        if Self::CAPACITY == 0 {
            return ptr::dangling_mut();
        }

        unsafe { self.mut_ptr().add(Self::DATA_OFFSET).cast() }
    }
}
