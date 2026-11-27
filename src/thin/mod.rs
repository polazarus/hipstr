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

#[derive(Clone, PartialEq, Eq, Debug)]
#[non_exhaustive]
pub struct TryReserveError(pub(crate) TryReserveErrorKind);

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum TryReserveErrorKind {
    CapacityOverflow,
    AllocError {
        layout: core::alloc::Layout,
    },
    /// From an adopted `Vec`'s own `try_reserve`.
    Std(alloc::collections::TryReserveError),
}

impl TryReserveError {
    /// Converts into std's error, whose constructors are unstable.
    pub(crate) fn into_std(self) -> alloc::collections::TryReserveError {
        let overflow = || {
            alloc::vec::Vec::<u8>::new()
                .try_reserve(usize::MAX)
                .expect_err("always overflows")
        };
        match self.0 {
            TryReserveErrorKind::CapacityOverflow => overflow(),
            // retry the same size through `Vec` to get an allocation error
            TryReserveErrorKind::AllocError { layout } => alloc::vec::Vec::<u8>::new()
                .try_reserve_exact(layout.size())
                .err()
                .unwrap_or_else(overflow),
            TryReserveErrorKind::Std(e) => e,
        }
    }
}

impl fmt::Display for TryReserveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            TryReserveErrorKind::CapacityOverflow => write!(f, "capacity overflow"),
            TryReserveErrorKind::AllocError { layout } => {
                write!(f, "allocation error: layout {layout:?}")
            }
            TryReserveErrorKind::Std(ref e) => fmt::Display::fmt(e, f),
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
        Err(TryReserveError(TryReserveErrorKind::Std(e))) => panic!("{e}"),
    }
}

/// Creates a [`ThinVec`] containing the arguments, with array-expression syntax.
macro_rules! thin_vec {
    () => {
        $crate::common::__vector!( $crate::thin::ThinVec<_> : )
    };
    ($e:expr; $n:expr) => {
        $crate::common::__vector!( $crate::thin::ThinVec<_> : $e; $n )
    };
    ($($e:expr),* $(,)?) => {
        $crate::common::__vector!( $crate::thin::ThinVec<_> : $($e),* )
    };
}

pub(crate) use thin_vec;
