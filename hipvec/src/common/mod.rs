use const_default::ConstDefault;

pub(crate) mod header;
pub(crate) mod methods;
pub(crate) mod tagged_pointer;
#[cfg(test)]
pub(crate) mod tests;
pub(crate) mod utils;

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

