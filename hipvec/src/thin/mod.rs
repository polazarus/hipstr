//! Thin vectors.
//!
//! Thin vectors are heap-allocated vectors with a pointer-sized handle on stack. The handle is a
//! pointer to the heap allocation, but it is masked to be non-null even when the vector is empty.

use alloc::fmt;

use const_default::ConstDefault;

pub(crate) mod base;
pub mod copy;
pub mod noncopy;

pub struct Reserved(#[allow(unused)] usize);

impl Default for Reserved {
    fn default() -> Self {
        Self::DEFAULT
    }
}

impl ConstDefault for Reserved {
    const DEFAULT: Self = Self(0);
}

impl fmt::Debug for Reserved {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Reserved")
    }
}

pub type ThinVec<T> = noncopy::ThinVec<T, Reserved>;
pub type CopyThinVec<T> = copy::ThinVec<T, Reserved>;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[non_exhaustive]
pub struct TryReserveError(TryReserveErrorKind);

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

// TODO improve repetitions to use from iterator when available

#[macro_export]
macro_rules! thin_vec {
    () => {
        $crate::thin::ThinVec::new()
    };
    ($e:expr; $n:expr) => {
        {
            let mut vec = $crate::thin::ThinVec::with_capacity($n);
            for e in core::iter::repeat_n($e, $n) {
                vec.push(e);
            }
            vec
        }
    };
    ($($e:expr),* $(,)?) => {
        {
            let mut vec = $crate::thin::ThinVec::with_capacity($crate::__count!($($e),*));
            $(
                vec.push($e);
            )*
            vec
        }
    };
}

#[macro_export]
macro_rules! copy_thin_vec {
    () => {
        $crate::thin::CopyThinVec::new()
    };
    ($e:expr; $n:expr) => {
        {
            let mut vec = $crate::thin::CopyThinVec::with_capacity($n);
            for e in core::iter::repeat_n($e, $n) {
                vec.push(e);
            }
            vec
        }
    };
    ($($e:expr),* $(,)?) => {
        {
            let mut vec = $crate::thin::CopyThinVec::with_capacity($crate::__count!($($e),*));
            $(
                vec.push($e);
            )*
            vec
        }
    };
}
