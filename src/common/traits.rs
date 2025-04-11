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
    fn capacity(&self) -> usize;
    fn as_slice(&self) -> &[Self::Item];
    fn as_ptr(&self) -> *const Self::Item;
}

pub trait MutVector: Vector {
    unsafe fn set_len(&mut self, len: usize);

    fn as_mut_ptr(&mut self) -> *mut Self::Item;

    fn as_non_null(&mut self) -> NonNull<Self::Item>;

    fn as_mut_slice(&mut self) -> &mut [Self::Item];
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
