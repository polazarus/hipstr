use core::marker::PhantomData;
use core::mem::{ManuallyDrop, MaybeUninit};
use core::num::NonZeroU8;
use core::ptr::NonNull;

use typenum::{U};
use super::InlineVec;

type Align<T> = [T; 0];

const POINTER_SIZE: usize = core::mem::size_of::<*mut ()>();
const POINTER_SIZE_M1: usize = POINTER_SIZE - 1;

pub struct HipVec<'borrow, T, B>(Pivot, PhantomData<(T, &'borrow B)>);

struct Pivot {
    #[cfg(target_endian = "little")]
    tag_byte: NonZeroU8,

    #[cfg(target_endian = "little")]
    _word_remainder: MaybeUninit<[u8; POINTER_SIZE_M1]>,

    _words: [MaybeUninit<*mut ()>; 2],

    #[cfg(target_endian = "big")]
    _word_remainder: MaybeUninit<[u8; POINTER_SIZE_M1]>,

    #[cfg(target_endian = "big")]
    _tag: NonZeroU8,
}

trait SizeOf {
    const SIZE: usize;
    type Size;
}
impl<T> SizeOf for T {
    const SIZE: usize = size_of::<T>();
    type Size = U<{size_of::<T>()}>;
}

pub struct Inline<T, const N: usize> {
    _size: NonZeroU8,
    _inline: [MaybeUninit<T>; N],
}


impl<'borrow, T, B> HipVec<'borrow, T, B> {
    const N: usize = 2;
    fn as_inline(&self) -> Option<&InlineVec<T>> {
        if self.is_inline() {
            let
        }

    }
}

enum H<T, const N: usize> {
    Inline(InlineSize, [MaybeUninit<T>; N]),
    Heap(NonNull<T>, NonNull<T>, usize),
}
