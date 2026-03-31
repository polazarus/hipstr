pub unsafe trait Vector {
    type Item;

    fn len(&self) -> usize;
    fn capacity(&self) -> usize;
    fn as_ptr(&self) -> *const Self::Item;
    fn as_slice(&self) -> &[Self::Item];
}

macro_rules! impl_vector {
    (impl$(( $($gen:tt)* ))? Vector<Item=$item:ty> for $ty:ty $(where $($where:tt)*)?) => {
        unsafe impl$(<$($gen)*>)? $crate::traits::Vector for $ty $(where $($where)*)?
        {
            type Item = $item;

            fn len(&self) -> usize {
                self.len()
            }

            fn capacity(&self) -> usize {
                self.capacity()
            }

            fn as_ptr(&self) -> *const Self::Item {
                self.as_ptr()
            }

            fn as_slice(&self) -> &[Self::Item] {
                self.as_slice()
            }
        }
    };
    (impl$(($($gen:tt)*))? MutVector<Item=$item:ty> for $ty:ty $(where $($where:tt)*)?) => {
        $crate::traits::impl_vector!(impl$(($($gen)*))? Vector<Item=$item> for $ty $(where $($where)*)?);

        unsafe impl$(<$($gen)*>)? $crate::traits::MutVector for $ty $(where $($where)*)?
        {

            fn as_mut_ptr(&mut self) -> *mut Self::Item {
                self.as_mut_ptr()
            }

            fn as_mut_slice(&mut self) -> &mut [Self::Item] {
                self.as_mut_slice()
            }

            unsafe fn set_len(&mut self, new_len: usize) {
                unsafe { self.set_len(new_len); }
            }

            fn reserve(&mut self, additional: usize) {
                self.reserve(additional);
            }
        }
    };
}

#[cfg(feature = "alloc")]
impl_vector!(impl(T) MutVector<Item=T> for alloc::vec::Vec<T>);

pub unsafe trait MutVector: Vector {
    fn as_mut_ptr(&mut self) -> *mut Self::Item;
    fn as_mut_slice(&mut self) -> &mut [Self::Item];
    unsafe fn set_len(&mut self, new_len: usize);
    fn reserve(&mut self, additional: usize);
}

pub(crate) use impl_vector;
