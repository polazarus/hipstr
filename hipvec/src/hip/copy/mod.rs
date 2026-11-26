pub type HipVec<'a, T, B> = super::generic::HipSlice<'a, T, B, crate::common::markers::Copy>;

#[cfg(test)]
mod tests;
