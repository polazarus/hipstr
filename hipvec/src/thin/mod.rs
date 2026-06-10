//! Thin vectors.
//!
//! Thin vectors are heap-allocated vectors with a pointer-sized handle on stack. The handle is a
//! pointer to the heap allocation, but it is masked to be non-null even when the vector is empty.

use alloc::fmt;

mod base;
mod generic;

#[cfg(test)]
mod copy_tests;

#[cfg(test)]
mod noncopy_tests;

pub(crate) use base::Base;

use crate::common::markers;

pub use self::generic::ThinVec as GenericThinVec;

pub type ThinVec<T> = self::generic::ThinVec<T, markers::NonCopy>;
pub type CopyThinVec<T> = self::generic::ThinVec<T, markers::Copy>;

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

/// Creates a [`ThinVec`] containing the arguments.
///
/// `thin_vec!` allows `ThinVec`s to be defined with the same syntax as array expressions. There
/// are two forms of this macro:
///
/// - Create a [`ThinVec`] containing a given list of elements:
///
/// ```
/// # use hipvec::thin_vec;
/// let v = thin_vec![1, 2, 3];
/// assert_eq!(v[0], 1);
/// assert_eq!(v[1], 2);
/// assert_eq!(v[2], 3);
/// ```
///
/// - Create a [`ThinVec`] from a given element and size:
///
/// ```
/// # use hipvec::thin_vec;
/// let v = thin_vec![1; 3];
/// assert_eq!(v.as_slice(), [1, 1, 1]);
/// ```
///
/// Note that unlike array expressions this syntax supports all elements which implement [`Clone`]
/// and the number of elements doesn't have to be a constant.
///
/// This will use `clone` to duplicate an expression, so one should be careful using this with types
/// having a nonstandard `Clone` implementation. For example, `thin_vec![Rc::new(1); 2]` will
/// create a thin vector of two references to the same boxed integer value, not two references
/// pointing to independently boxed integers.
///
/// Also, note that `thin_vec![expr; 0]` is allowed, and produces an empty thin vector. This
/// will still evaluate `expr`, however, and immediately drop the resulting value, so be mindful of
/// side effects.
#[macro_export]
macro_rules! thin_vec {
    () => {
        $crate::__vector!( $crate::thin::ThinVec<_> : )
    };
    ($e:expr; $n:expr) => {
        $crate::__vector!( $crate::thin::ThinVec<_> : $e; $n )
    };
    ($($e:expr),* $(,)?) => {
        $crate::__vector!( $crate::thin::ThinVec<_> : $($e),* )
    };
}

/// Creates a [`CopyThinVec`] containing the arguments.
///
/// `copy_thin_vec!` allows `CopyThinVec`s to be defined with the same syntax as array
/// expressions. There are two forms of this macro:
///
/// - Create a [`CopyThinVec`] containing a given list of elements:
///
/// ```
/// # use hipvec::copy_thin_vec;
/// let v = copy_thin_vec![1, 2, 3];
/// assert_eq!(v[0], 1);
/// assert_eq!(v[1], 2);
/// assert_eq!(v[2], 3);
/// ```
///
/// - Create a [`CopyThinVec`] from a given element and size:
///
/// ```
/// # use hipvec::copy_thin_vec;
/// let v = copy_thin_vec![1; 3];
/// assert_eq!(v.as_slice(), [1, 1, 1]);
/// ```
///
/// Note that unlike array expressions this syntax supports all elements which implement [`Clone`]
/// and the number of elements doesn't have to be a constant.
///
/// This will use `clone` to duplicate an expression, so one should be careful using this with types
/// having a nonstandard `Clone` implementation. For example, `copy_thin_vec![Rc::new(1); 2]` will
/// create a thin vector of two references to the same boxed integer value, not two references
/// pointing to independently boxed integers.
///
/// Also, note that `copy_thin_vec![expr; 0]` is allowed, and produces an empty thin vector.
/// This will still evaluate `expr`, however, and immediately drop the resulting value, so be
/// mindful of side effects.
#[macro_export]
macro_rules! copy_thin_vec {
    () => {
        $crate::__vector!( $crate::thin::CopyThinVec<_> : )
    };
    ($e:expr; $n:expr) => {
        $crate::__vector!( $crate::thin::CopyThinVec<_> : $e; $n )
    };
    ($($e:expr),* $(,)?) => {
        $crate::__vector!( $crate::thin::CopyThinVec<_> : $($e),* )
    };
}
