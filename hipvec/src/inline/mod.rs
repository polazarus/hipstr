use layouts::BasicLayout;

mod base;
pub mod copy;
pub mod layouts;
pub mod noncopy;

pub type InlineVec<T> = noncopy::InlineVec<T, BasicLayout>;
pub type CopyInlineVec<T> = copy::InlineVec<T, BasicLayout>;
