//! Thin vectors.
//!
//! Thin vectors are heap-allocated vectors with a pointer-sized handle on stack. The handle is a
//! pointer to the heap allocation, but it is masked to be non-null even when the vector is empty.

use alloc::fmt;

mod base;
mod generic;

#[cfg(test)]
mod copy_tests;

pub(crate) use base::Base;

pub use self::generic::ThinVec;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[non_exhaustive]
pub struct TryReserveError(pub(crate) TryReserveErrorKind);

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TryReserveErrorKind {
    CapacityOverflow,
    AllocError { layout: core::alloc::Layout },
}

impl fmt::Display for TryReserveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            TryReserveErrorKind::CapacityOverflow => write!(f, "capacity overflow"),
            TryReserveErrorKind::AllocError { layout } => {
                write!(f, "allocation error: layout {layout:?}")
            }
        }
    }
}

pub(crate) fn unwrap_or_oom<T>(result: Result<T, TryReserveError>) -> T {
    match result {
        Ok(value) => value,
        Err(TryReserveError(TryReserveErrorKind::CapacityOverflow)) => {
            panic!("capacity overflow")
        }
        Err(TryReserveError(TryReserveErrorKind::AllocError { layout })) => {
            alloc::alloc::handle_alloc_error(layout)
        }
    }
}

/// Creates a [`ThinVec`] containing the arguments, with array-expression syntax.
macro_rules! thin_vec {
    () => {
        $crate::next::common::__vector!( $crate::next::thin::ThinVec<_> : )
    };
    ($e:expr; $n:expr) => {
        $crate::next::common::__vector!( $crate::next::thin::ThinVec<_> : $e; $n )
    };
    ($($e:expr),* $(,)?) => {
        $crate::next::common::__vector!( $crate::next::thin::ThinVec<_> : $($e),* )
    };
}

pub(crate) use thin_vec;
