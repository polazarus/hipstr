use core::fmt;

use const_default::ConstDefault;

#[cfg(feature = "alloc")]
pub(crate) mod header;
pub(crate) mod methods;
pub(crate) mod range;
#[cfg(feature = "alloc")]
pub(crate) mod tagged_pointer;
#[cfg(test)]
pub(crate) mod tests;
pub(crate) mod traits;
pub(crate) mod utils;

pub mod drain;
pub mod markers;
pub mod splice;

pub use range::RangeError;

#[derive(Default, Copy, Clone, PartialEq, Eq, Debug)]
#[repr(usize)]
pub enum ZeroUsize {
    #[default]
    ZeroUsize = 0,
}

impl ConstDefault for ZeroUsize {
    const DEFAULT: Self = Self::ZeroUsize;
}

/// Panics with the provided displayable error message.
///
/// # Panics
///
/// Always panics with the provided error message.
#[track_caller]
#[inline]
pub(crate) fn panic_display<T>(e: impl fmt::Display) -> T {
    panic!("{e}");
}

/// Unwraps a `Result`, panicking with the error message if it is an `Err`.
#[track_caller]
#[inline]
pub(crate) fn unwrap_display<T, E: fmt::Display>(result: Result<T, E>) -> T {
    match result {
        Ok(value) => value,
        Err(e) => panic_display(e),
    }
}

#[macro_export]
#[doc(hidden)]
macro_rules! __count {
    (@ $_x:tt) => { () };
    ($($x:tt),* $(,)? ) => {
        <[()]>::len(&[$($crate::__count!(@ $x)),*])
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! __vector {
    ( const $ty:ty : $e:expr; $n:expr ) => {
        {
            let mut vec = <$ty>::with_capacity($n);
            let mut n = $n;
            let e = $e;
            while n > 0 {
                vec.push(e);
                n -= 1;
            }
            vec
        }
    };

    ( $ty:ty : ) => {
        <$ty>::new()
    };
    ( $ty:ty : $($e:expr),* $(,)? ) => {
        {
            let mut vec = <$ty>::with_capacity($crate::__count!($($e),*));
            $(
                vec.push($e);
            )*
            vec
        }
    };
    ( $ty:ty : $e:expr; $n:expr ) => {
        {
            let mut vec = <$ty>::with_capacity($n);
            for e in core::iter::repeat_n($e, $n) {
                vec.push(e);
            }
            vec
        }
    };


}
