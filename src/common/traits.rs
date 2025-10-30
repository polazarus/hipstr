use core::borrow::{Borrow, BorrowMut};
use core::ptr::NonNull;

use sealed::Sealed;

#[cfg(test)]
pub(crate) mod tests;

pub(crate) mod sealed {
    pub trait Sealed {}
}

pub trait Vector: Sealed {
    type Item;

    fn len(&self) -> usize;
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
    fn capacity(&self) -> usize;
    fn as_slice(&self) -> &[Self::Item];
    fn as_ptr(&self) -> *const Self::Item;
}

pub trait MutVector: Vector {
    /// Sets the length of the vector.
    ///
    /// # Safety
    ///
    /// The length must be valid and must not exceed the current capacity. The
    /// caller must ensure that the new elements are properly initialized.
    unsafe fn set_len(&mut self, len: usize);

    fn as_mut_ptr(&mut self) -> *mut Self::Item;

    fn as_non_null(&mut self) -> NonNull<Self::Item>;

    fn as_mut_slice(&mut self) -> &mut [Self::Item];
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

impl<T> Vector for alloc::vec::Vec<T> {
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

impl<T> MutVector for alloc::vec::Vec<T> {
    unsafe fn set_len(&mut self, len: usize) {
        unsafe { self.set_len(len) }
    }

    fn as_mut_ptr(&mut self) -> *mut Self::Item {
        self.as_mut_ptr()
    }

    fn as_mut_slice(&mut self) -> &mut [Self::Item] {
        self.as_mut_slice()
    }

    fn as_non_null(&mut self) -> NonNull<Self::Item> {
        unsafe { NonNull::new_unchecked(self.as_mut_ptr()) }
    }
}
