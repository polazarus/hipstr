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

/// Traits for mutable vector-like types.
///
/// # Safety
///
/// Implementors must ensure that the methods correctly reflect the properties of the vector, such
/// as length, capacity, and pointer stability.
pub unsafe trait MutableVector: Vector {
    fn as_mut_ptr(&mut self) -> *mut Self::Item;

    fn as_mut_slice(&mut self) -> &mut [Self::Item];

    fn spare_capacity_mut(&mut self) -> &mut [core::mem::MaybeUninit<Self::Item>];

    /// Sets the length of the vector to the new length.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the new length is less than or equal to the capacity of the vector,
    /// and that the elements between the old length and the new length are properly initialized.
    unsafe fn set_len(&mut self, new_len: usize);

    fn pop(&mut self) -> Option<Self::Item>;

    fn truncate(&mut self, new_len: usize);

    fn clear(&mut self);
}

/// Traits for growable vector-like types.
///
/// # Safety
///
/// Implementors must ensure that the methods correctly reflect the properties of the vector, such
/// as length, capacity, and pointer stability.
pub unsafe trait GrowableVector: MutableVector {
    /// Reserves capacity for at least `additional` more elements to be inserted in the vector.
    ///
    /// The collection may reserve more space to avoid frequent reallocations.
    ///
    /// # Panics
    ///
    /// May panics if the new capacity would exceed some maximum allowed size.
    fn reserve(&mut self, additional: usize);

    /// Reserves the minimum capacity for at least `additional` more elements to be inserted in the vector.
    ///
    /// The collection may reserve more space for technical reasons.
    ///
    /// # Panics
    ///
    /// May panics if the new capacity would exceed some maximum allowed size.
    fn reserve_exact(&mut self, additional: usize);

    /// Appends an element to the back of the vector.
    ///
    /// # Panics
    ///
    /// May panics if the new length would exceed some maximum allowed size.
    fn push(&mut self, value: Self::Item);
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
    (impl$(($($gen:tt)*))? GrowableVector<Item=$item:ty> for $ty:ty $(where $($where:tt)*)?) => {
        unsafe impl$(<$($gen)*>)? $crate::traits::GrowableVector for $ty $(where $($where)*)?
        {

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
    (impl$(($($gen:tt)*))? MutableVector<Item=$item:ty> for $ty:ty $(where $($where:tt)*)?) => {
        unsafe impl$(<$($gen)*>)? $crate::traits::MutableVector for $ty $(where $($where)*)?
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
            fn spare_capacity_mut(&mut self) -> &mut [core::mem::MaybeUninit<Self::Item>] {
                self.spare_capacity_mut()
            }

            #[inline]
            unsafe fn set_len(&mut self, new_len: usize) {
                unsafe { self.set_len(new_len); }
            }


            #[inline]
            fn pop(&mut self) -> Option<Self::Item> {
                self.pop()
            }

            #[inline]
            fn truncate(&mut self, new_len: usize) {
                self.truncate(new_len);
            }

            #[inline]
            fn clear(&mut self) {
                self.clear();
            }
        }
    }
}

#[cfg(feature = "alloc")]
impl_vector!(impl(T) Vector<Item=T> for alloc::vec::Vec<T>);

#[cfg(feature = "alloc")]
impl_vector!(impl(T) MutableVector<Item=T> for alloc::vec::Vec<T>);

#[cfg(feature = "alloc")]
impl_vector!(impl(T) GrowableVector<Item=T> for alloc::vec::Vec<T>);

pub(crate) use impl_vector;
