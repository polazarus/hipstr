mod seal {
    pub trait Seal {}
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Copy;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NonCopy;

impl seal::Seal for Copy {}
impl seal::Seal for NonCopy {}

pub trait Copyness: seal::Seal {
    const COPY: bool;
}

impl Copyness for Copy {
    const COPY: bool = true;
}

impl Copyness for NonCopy {
    const COPY: bool = false;
}
