use core::ops::{Div, Rem, Sub};

use generic_array::ArrayLength;
use typenum::{NonZero, Quot, Sub1, B1, U, U0, U12, U16, U20, U24, U4, U8};

/// Size of a pointer on the current platform, in bytes.
#[cfg(target_pointer_width = "32")]
pub type PointerSize = U4;

/// Size of a pointer on the current platform, in bytes.
#[cfg(target_pointer_width = "64")]
pub type PointerSize = U8;

/// Alignment of a pointer on the current platform, in bytes.
pub type PointerAlign = PointerSize;

/// Trait for type numbers that are divisible by another.
pub trait Divisible<U>: Div<U> + Rem<U, Output = U0> {}

impl<T, U> Divisible<U> for T where T: Div<U> + Rem<U, Output = U0> {}

const _DIVISIBLE_ASSERTS: () = {
    const fn is_divisible<T: Divisible<U<4>>>() {}
    is_divisible::<U4>();
    is_divisible::<U8>();
    is_divisible::<U12>();
    is_divisible::<U16>();
    is_divisible::<U20>();
    is_divisible::<U24>();
};

/// Trait for type numbers that can be used as inline lengths.
pub trait InlineLength: NonZero + ArrayLength + Seal {}

pub trait Seal {
    type Words: ArrayLength;
    type WordsM1: ArrayLength;
}

impl<T> InlineLength for T
where
    T: NonZero + ArrayLength + Divisible<PointerAlign>,
    Quot<T, PointerAlign>: ArrayLength + Sub<B1>,
    Sub1<Quot<T, PointerAlign>>: ArrayLength,
{
}

impl<T> Seal for T
where
    T: NonZero + ArrayLength + Divisible<PointerAlign>,
    Quot<T, PointerAlign>: ArrayLength + Sub<B1>,
    Sub1<Quot<T, PointerAlign>>: ArrayLength,
{
    type Words = Quot<T, PointerAlign>;
    type WordsM1 = Sub1<Self::Words>;
}

const _INLINE_LENGTH_ASSERTS: () = {
    const fn is_inline_length<T: InlineLength>() {}
    #[cfg(target_pointer_width = "32")]
    {
        is_inline_length::<U4>();
        is_inline_length::<U12>();
        is_inline_length::<U20>();
    }
    is_inline_length::<U8>();
    is_inline_length::<U16>();
    is_inline_length::<U24>();
};
