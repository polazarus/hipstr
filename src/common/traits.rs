use core::borrow::{Borrow, BorrowMut};
use core::ptr::NonNull;

use sealed::Sealed;

#[cfg(test)]
pub(crate) mod tests;

pub(crate) mod sealed {
    pub trait Sealed {}
}

/// Traits for vectors that can be read.
///
/// # Safety
///
/// - `as_ptr` must be valid for reads of `len` elements of type `Item`.
/// - `as_ptr` must returns a valid aligned and non zero pointer.
/// - `len` must be less than or equal to `capacity` at all times.
pub unsafe trait Vector: Sealed {
    /// The item type of the vector.
    type Item;

    /// Gets the length of the vector.
    fn len(&self) -> usize;

    /// Checks if the vector is empty.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Gets the capacity of the vector.
    fn capacity(&self) -> usize;

    /// Gets a slice of the vector's contents.
    fn as_slice(&self) -> &[Self::Item] {
        // SAFETY: trait invariant guarantees valid pointer and length
        unsafe { core::slice::from_raw_parts(self.as_ptr(), self.len()) }
    }

    /// Gets a pointer to the vector's buffer.
    fn as_ptr(&self) -> *const Self::Item;
}

/// Traits for vectors that can be mutated.
///
/// # Safety
///
/// - `as_mut_ptr` and `as_non_null` must return the same aligned and non zero
///   pointer as `as_ptr`.
/// - `as_mut_ptr` and `as_non_null` must be valid for writes of `len` elements
///   of type `Item`.
pub unsafe trait MutVector: Vector {
    /// Sets the length of the vector.
    ///
    /// # Safety
    ///
    /// The length must be valid and must not exceed the current capacity. The
    /// caller must ensure that the new elements are properly initialized.
    unsafe fn set_len(&mut self, len: usize);

    /// Gets a mutable pointer to the vector's buffer.
    fn as_mut_ptr(&mut self) -> *mut Self::Item;

    /// Gets a non-null mutable pointer to the vector's buffer.
    fn as_non_null(&mut self) -> NonNull<Self::Item> {
        // SAFETY: trait invariant guarantees valid pointer
        unsafe { NonNull::new_unchecked(self.as_mut_ptr()) }
    }

    fn as_mut_slice(&mut self) -> &mut [Self::Item] {
        // SAFETY: trait invariant guarantees valid pointer and length
        unsafe { core::slice::from_raw_parts_mut(self.as_mut_ptr(), self.len()) }
    }

    /// Reserves capacity for at least `additional` more elements to be inserted.
    ///
    /// The vector may reserve more space to avoid frequent reallocations.
    fn reserve(&mut self, additional: usize);
}

/// Traits for vectors that can be mutated.
pub trait Mutate: Vector {
    /// A mutable vector type
    type MutVector<'a>: MutVector<Item = Self::Item>
    where
        Self: 'a;

    /// A reference type
    type RefMut<'a>: BorrowMut<Self::MutVector<'a>> + Borrow<Self::MutVector<'a>>
    where
        Self: 'a;

    /// Gets a mutable reference to the vector.
    fn mutate(&mut self) -> Self::RefMut<'_>;
}

impl<T: MutVector> Mutate for T {
    type MutVector<'a>
        = Self
    where
        Self: 'a;
    type RefMut<'a>
        = &'a mut Self
    where
        Self: 'a;

    #[inline]
    fn mutate(&mut self) -> Self::RefMut<'_> {
        self
    }
}

impl<T> Sealed for alloc::vec::Vec<T> {}

unsafe impl<T> Vector for alloc::vec::Vec<T> {
    type Item = T;

    fn len(&self) -> usize {
        self.len()
    }

    fn capacity(&self) -> usize {
        self.capacity()
    }

    fn as_slice(&self) -> &[Self::Item] {
        self.as_slice()
    }

    fn as_ptr(&self) -> *const Self::Item {
        self.as_ptr()
    }
}

unsafe impl<T> MutVector for alloc::vec::Vec<T> {
    unsafe fn set_len(&mut self, len: usize) {
        unsafe { self.set_len(len) }
    }

    fn as_mut_ptr(&mut self) -> *mut Self::Item {
        self.as_mut_ptr()
    }

    fn as_mut_slice(&mut self) -> &mut [Self::Item] {
        self.as_mut_slice()
    }

    fn reserve(&mut self, additional: usize) {
        self.reserve(additional);
    }
}
