/// Traits for vector-like types.
///
/// # Safety
///
/// Implementors must ensure that the methods correctly reflect the properties of the vector, such
/// as length, capacity, and pointer stability.
pub unsafe trait Vector {
    type Item;

    fn len(&self) -> usize;

    #[inline]
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn capacity(&self) -> usize;

    fn as_ptr(&self) -> *const Self::Item;

    fn as_slice(&self) -> &[Self::Item];
}

macro_rules! impl_vector {
    (impl$(( $($gen:tt)* ))? Vector<Item=$item:ty> for $ty:ty $(where $($where:tt)*)?) => {
        unsafe impl$(<$($gen)*>)? $crate::traits::Vector for $ty $(where $($where)*)?
        {
            type Item = $item;

            #[inline]
            fn len(&self) -> usize {
                self.len()
            }

            #[inline]
            fn is_empty(&self) -> bool {
                self.is_empty()
            }

            #[inline]
            fn capacity(&self) -> usize {
                self.capacity()
            }

            #[inline]
            fn as_ptr(&self) -> *const Self::Item {
                self.as_ptr()
            }

            #[inline]
            fn as_slice(&self) -> &[Self::Item] {
                self.as_slice()
            }
        }
    };
    (impl$(($($gen:tt)*))? MutVector<Item=$item:ty> for $ty:ty $(where $($where:tt)*)?) => {
        $crate::traits::impl_vector!(impl$(($($gen)*))? Vector<Item=$item> for $ty $(where $($where)*)?);

        unsafe impl$(<$($gen)*>)? $crate::traits::MutVector for $ty $(where $($where)*)?
        {

            #[inline]
            fn as_mut_ptr(&mut self) -> *mut Self::Item {
                self.as_mut_ptr()
            }

            #[inline]
            fn as_mut_slice(&mut self) -> &mut [Self::Item] {
                self.as_mut_slice()
            }

            #[inline]
            unsafe fn set_len(&mut self, new_len: usize) {
                unsafe { self.set_len(new_len); }
            }

            #[inline]
            fn reserve(&mut self, additional: usize) {
                self.reserve(additional);
            }

            #[inline]
            fn reserve_exact(&mut self, additional: usize) {
                self.reserve_exact(additional);
            }

            #[inline]
            fn push(&mut self, value: Self::Item) {
                self.push(value);
            }
        }
    };
}

#[cfg(feature = "alloc")]
impl_vector!(impl(T) MutVector<Item=T> for alloc::vec::Vec<T>);

/// Traits for mutable vector-like types.
///
/// # Safety
///
/// Implementors must ensure that the methods correctly reflect the properties of the vector, such
/// as length, capacity, and pointer stability.
pub unsafe trait MutVector: Vector {
    fn as_mut_ptr(&mut self) -> *mut Self::Item;
    fn as_mut_slice(&mut self) -> &mut [Self::Item];
    unsafe fn set_len(&mut self, new_len: usize);
    fn reserve(&mut self, additional: usize);
    fn reserve_exact(&mut self, additional: usize);
    fn push(&mut self, value: Self::Item);
}

pub(crate) use impl_vector;
