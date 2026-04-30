use core::fmt;

use const_default::ConstDefault;

pub(crate) mod header;
pub(crate) mod methods;
pub(crate) mod range;
pub(crate) mod tagged_pointer;
#[cfg(test)]
pub(crate) mod tests;
pub(crate) mod traits;
pub(crate) mod utils;

pub mod drain;
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

#[macro_export]
#[doc(hidden)]
macro_rules! __count {
    (@ $_x:tt) => { () };
    ($($x:tt),* $(,)? ) => {
        <[()]>::len(&[$($crate::__count!(@ $x)),*])
    };
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

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum TryReserveError {
    CapacityOverflow,
    AllocError { layout: core::alloc::Layout },
}

impl fmt::Debug for TryReserveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::CapacityOverflow => write!(f, "capacity overflow"),
            Self::AllocError { layout } => write!(f, "allocation error: layout {layout:?}"),
        }
    }
}

impl fmt::Display for TryReserveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::CapacityOverflow => write!(f, "capacity overflow"),
            Self::AllocError { layout } => write!(f, "allocation error: layout {layout:?}"),
        }
    }
}

pub(crate) trait TryReserveErrorExt<T> {
    fn unwrap_or_oom(self) -> T;
}

impl<T> TryReserveErrorExt<T> for Result<T, TryReserveError> {
    fn unwrap_or_oom(self) -> T {
        match self {
            Ok(value) => value,
            Err(TryReserveError::CapacityOverflow) => panic!("capacity overflow"),
            Err(TryReserveError::AllocError { layout }) => alloc::alloc::handle_alloc_error(layout),
        }
    }
}
