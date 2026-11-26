use core::fmt;

use layouts::BasicLayout;

pub(crate) mod base;
pub mod copy;
pub mod layouts;

pub type InlineVec<T> = copy::InlineVec<T, BasicLayout>;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[non_exhaustive]
pub struct TryReserveError();

impl core::error::Error for TryReserveError {}

impl fmt::Display for TryReserveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.message())
    }
}

impl TryReserveError {
    pub(crate) const fn message(&self) -> &'static str {
        "capacity overflow"
    }
}

/// Creates an [`InlineVec`] containing the arguments, with array-expression syntax.
macro_rules! inline_vec {
    () => {
        $crate::next::common::__vector!( $crate::next::inline::InlineVec<_> : )
    };
    ($e:expr; $n:expr) => {
        $crate::next::common::__vector!( const $crate::next::inline::InlineVec<_> : $e; $n )
    };
    ($($e:expr),* $(,)?) => {
        $crate::next::common::__vector!( $crate::next::inline::InlineVec<_> : $($e),* )
    };
}

pub(crate) use inline_vec;
