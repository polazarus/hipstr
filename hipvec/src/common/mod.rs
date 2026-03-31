use const_default::ConstDefault;

pub(crate) mod methods;
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
