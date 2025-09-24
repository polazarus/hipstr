use core::ops::{Div, Rem, Sub};

use generic_array::ArrayLength;
use typenum::{NonZero, Quot, Sub1, Unsigned, B1, U0, U8};

/// Size of a pointer on the current platform, in bytes.
#[cfg(target_pointer_width = "16")]
pub type PointerSize = U2;

/// Size of a pointer on the current platform, in bytes.
#[cfg(target_pointer_width = "32")]
pub type PointerSize = U4;

/// Size of a pointer on the current platform, in bytes.
#[cfg(target_pointer_width = "64")]
pub type PointerSize = U8;

#[cfg(not(any(
    target_pointer_width = "64",
    target_pointer_width = "32",
    target_pointer_width = "16",
)))]
compile_error!("unsupported target pointer width");

/// Trait for type numbers that are divisible by another.
pub trait Divisible<U: Unsigned + NonZero>: Unsigned + Div<U> + Rem<U, Output = U0> {}

impl<T, U> Divisible<U> for T
where
    T: Unsigned + Div<U> + Rem<U, Output = U0>,
    U: Unsigned + NonZero,
{
}

/// Trait for type numbers that can be used as inline lengths.
///
/// Basically, this means they are non-zero and divisible by the pointer size.
pub trait InlineLength: NonZero + ArrayLength + Divisible<PointerSize> + Seal {}

pub trait Seal {
    type Words: ArrayLength;
    type WordsM1: ArrayLength;
}

impl<T> InlineLength for T
where
    T: NonZero + ArrayLength + Divisible<PointerSize>,
    Quot<T, PointerSize>: ArrayLength + Sub<B1>,
    Sub1<Quot<T, PointerSize>>: ArrayLength,
{
}

impl<T> Seal for T
where
    T: NonZero + ArrayLength + Divisible<PointerSize>,
    Quot<T, PointerSize>: ArrayLength + Sub<B1>,
    Sub1<Quot<T, PointerSize>>: ArrayLength,
{
    type Words = Quot<T, PointerSize>;
    type WordsM1 = Sub1<Self::Words>;
}
