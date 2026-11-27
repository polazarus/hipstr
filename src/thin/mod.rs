//! Thin heap buffers: the elements follow the header in one allocation.

use alloc::fmt;

mod base;

pub(crate) use base::Base;

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
        Err(e) => oom(e),
    }
}

/// Panics, or aborts on an allocation error (not testable: excluded from
/// coverage).
#[cold]
#[track_caller]
#[cfg_attr(coverage_nightly, coverage(off))]
fn oom(e: TryReserveError) -> ! {
    match e.0 {
        TryReserveErrorKind::CapacityOverflow => panic!("capacity overflow"),
        TryReserveErrorKind::AllocError { layout } => alloc::alloc::handle_alloc_error(layout),
        TryReserveErrorKind::Std(e) => panic!("{e}"),
    }
}

#[cfg(test)]
mod tests {
    use alloc::string::ToString;

    use super::*;

    #[test]
    fn display() {
        let overflow = TryReserveError(TryReserveErrorKind::CapacityOverflow);
        assert_eq!(overflow.to_string(), "capacity overflow");
        let std_e = alloc::vec::Vec::<u8>::new()
            .try_reserve(usize::MAX)
            .unwrap_err();
        let e = TryReserveError(TryReserveErrorKind::Std(std_e.clone()));
        assert_eq!(e.to_string(), std_e.to_string());
        assert_eq!(e.into_std(), std_e);
        assert_eq!(overflow.into_std(), std_e);
    }

    #[test]
    #[should_panic(expected = "capacity overflow")]
    fn unwrap_overflow() {
        unwrap_or_oom::<()>(Err(TryReserveError(TryReserveErrorKind::CapacityOverflow)));
    }
}
