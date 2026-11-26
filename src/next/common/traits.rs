/// Implements `Extend` for a vector type, given:
/// - Vector type
/// - Element type
/// - Generic parameters enclosed in square brackets
/// - Where clause enclosed in square brackets
///
/// Requirement: the vector type must have `len()`, `capacity()`, `reserve()`, `as_mut_ptr()`, and `set_len()` methods.
macro_rules! impl_extend {
    ( $ty:ty,  $param:ty, [ $($gen:tt)* ], [ $($where_clause:tt)* ]  ) => {
        impl<$($gen)*> core::iter::Extend<$param> for $ty where $($where_clause)* {
            fn extend<_I: IntoIterator<Item=$param>>(&mut self, iter: _I) {
                let mut iterator = iter.into_iter();
                while let Some(element) = iterator.next() {
                    let len = self.len();
                    if len == self.capacity() {
                        let (lower, _) = iterator.size_hint();
                        self.reserve(lower.saturating_add(1)); // if lower is usize::MAX, this must panic
                    }
                    // SAFETY: space was reserved
                    unsafe {
                        self.as_mut_ptr().add(len).write(element);
                        self.set_len(len + 1);
                    }
                }
            }
        }
    };
}

pub(crate) use impl_extend;
