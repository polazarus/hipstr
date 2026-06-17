pub type HipVec<'a, T, B> = super::generic::HipVec<'a, T, B, crate::common::markers::NonCopy>;

#[cfg(test)]
mod tests;
