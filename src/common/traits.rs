#![allow(clippy::len_without_is_empty)]

use core::mem::MaybeUninit;
use core::ptr::NonNull;

use sealed::Sealed;

#[cfg(test)]
pub(crate) mod tests;

pub(crate) mod sealed {
    pub trait Sealed {}
}

/// A vector trait that allows for low-level operations on the vector's memory.
pub trait Vector: Sealed {
    type Item;

    /// Returns the length of the vector.
    fn len(&self) -> usize;

    /// Returns the capacity of the vector.
    fn capacity(&self) -> usize;

    /// Returns a pointer to the first element of the vector.
    fn as_ptr(&self) -> *const Self::Item;
}

/// A vector trait that extends the [`Vector`] trait with additional methods.
pub trait VectorExt: Vector {
    /// Returns `true` if the vector is empty.
    #[inline]
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns a slice of the vector.
    #[inline]
    fn as_slice(&self) -> &[Self::Item] {
        unsafe { core::slice::from_raw_parts(self.as_ptr(), self.len()) }
    }
}

impl<T: Vector + ?Sized> VectorExt for T {}

/// A mutable vector trait that allows for low-level operations on the vector's memory.
///
/// # Safety
///
/// This trait is unsafe because it allows for low-level operations that can
/// lead to undefined behavior if not used correctly.
///
/// In particular, the intricate semantics of the length and capacity of the vector
/// can lead to memory safety issues if not handled properly.
pub unsafe trait MutVector: Vector {
    /// Sets the length of the vector.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the new length does not exceed the capacity of the vector.
    /// This is a low-level operation and should be used with caution.
    /// The caller must ensure that the memory is valid for the new length.
    unsafe fn set_len(&mut self, len: usize);

    /// Returns a non-null pointer to the first element of the vector.
    fn as_non_null(&mut self) -> NonNull<Self::Item>;
}

/// A mutable vector trait that extends the [`MutVector`] trait with additional methods.
pub trait MutVectorExt: MutVector {
    /// Returns a mutable slice of the vector.
    fn as_mut_slice(&mut self) -> &mut [Self::Item] {
        unsafe { core::slice::from_raw_parts_mut(self.as_mut_ptr(), self.len()) }
    }

    /// Returns a mutable pointer to the first element of the vector.
    fn as_mut_ptr(&mut self) -> *mut Self::Item {
        self.as_non_null().as_ptr()
    }

    /// Returns a mutable slice to the spare capacity of the vector.
    fn spare_capacity_mut(&mut self) -> &mut [MaybeUninit<Self::Item>] {
        let len = self.len();
        let capacity = self.capacity();
        let spare_len = capacity - len;
        unsafe {
            let start = self.as_mut_ptr().add(len).cast();
            core::slice::from_raw_parts_mut(start, spare_len)
        }
    }
}

impl<T: MutVector + ?Sized> MutVectorExt for T {}

impl<T> Sealed for alloc::vec::Vec<T> {}

impl<T> Vector for alloc::vec::Vec<T> {
    type Item = T;

    fn len(&self) -> usize {
        self.len()
    }

    fn capacity(&self) -> usize {
        self.capacity()
    }

    fn as_ptr(&self) -> *const Self::Item {
        self.as_ptr()
    }
}

unsafe impl<T> MutVector for alloc::vec::Vec<T> {
    unsafe fn set_len(&mut self, len: usize) {
        unsafe { self.set_len(len) }
    }

    fn as_non_null(&mut self) -> NonNull<Self::Item> {
        unsafe { NonNull::new_unchecked(self.as_mut_ptr()) }
    }
}
