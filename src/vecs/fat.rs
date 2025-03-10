#![allow(unused)]

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::mem::ManuallyDrop;
use core::ops;
use core::ptr::NonNull;

use super::Fat;
use crate::common::manually_drop_as_ref;
use crate::smart::{Kind, UpdateResult};

/// A smart fat vector.
///
/// This is a wrapper around a standard Rust vector that provides automatic
/// reference counting and copy-on-write semantics.
#[repr(transparent)]
pub struct SmartFat<T, C: Kind>(pub(super) NonNull<Fat<T, C>>);

impl<T, C: Kind> SmartFat<T, C> {
    /// Creates a new smart fat vector from a [`Vec`].
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::SmartFatVec;
    /// ```
    pub fn new(vec: Vec<T>) -> Self {
        let ptr = Box::into_raw(Box::new(Fat::new(vec)));
        let non_null = unsafe { NonNull::new_unchecked(ptr) };
        Self(non_null)
    }

    const fn header(&self) -> &Fat<T, C> {
        unsafe { self.0.as_ref() }
    }

    const unsafe fn header_mut(&mut self) -> &mut Fat<T, C> {
        unsafe { self.0.as_mut() }
    }

    #[inline]
    pub const fn as_vec(&self) -> &Vec<T> {
        manually_drop_as_ref(&self.header().vec)
    }

    #[inline]
    pub fn mutate(&mut self) -> Option<&mut Vec<T>> {
        if self.count().is_unique() {
            Some(unsafe { self.as_vec_mut_unchecked() })
        } else {
            None
        }
    }

    pub(crate) unsafe fn as_vec_mut_unchecked(&mut self) -> &mut Vec<T> {
        unsafe { &mut self.header_mut().vec }
    }

    pub(crate) fn count(&self) -> &C {
        &self.header().count
    }

    #[inline]
    pub fn as_mut_ptr(&mut self) -> Option<*mut T> {
        if self.count().is_unique() {
            unsafe { Some(self.as_vec_mut_unchecked().as_mut_ptr()) }
        } else {
            None
        }
    }

    #[inline]
    pub fn as_mut_slice(&mut self) -> Option<&mut [T]> {
        if self.count().is_unique() {
            Some(unsafe { self.as_vec_mut_unchecked().as_mut_slice() })
        } else {
            None
        }
    }
}

impl<T, C: Kind> From<Vec<T>> for SmartFat<T, C> {
    fn from(vec: Vec<T>) -> Self {
        Self::new(vec)
    }
}

impl<T, C: Kind> From<&[T]> for SmartFat<T, C>
where
    T: Clone,
{
    fn from(slice: &[T]) -> Self {
        Self::new(slice.to_vec())
    }
}

impl<T, C: Kind> From<Box<[T]>> for SmartFat<T, C> {
    fn from(boxed: Box<[T]>) -> Self {
        Self::new(boxed.into_vec())
    }
}

impl<T, C: Kind> Clone for SmartFat<T, C> {
    fn clone(&self) -> Self {
        if self.count().incr() == UpdateResult::Overflow {
            panic!("count overflow");
        } else {
            Self(self.0)
        }
    }
}

impl<T, C: Kind> ops::Deref for SmartFat<T, C> {
    type Target = Vec<T>;

    fn deref(&self) -> &Self::Target {
        self.as_vec()
    }
}

impl<T, C: Kind> Drop for SmartFat<T, C> {
    fn drop(&mut self) {
        if self.count().decr() == UpdateResult::Overflow {
            let ptr = self.0.as_ptr();
            unsafe {
                // drop the refcount box at the end of scope
                let mut fat = Box::from_raw(ptr);
                // drop the vector
                ManuallyDrop::drop(&mut fat.vec);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec;

    use super::*;
    use crate::Arc;

    #[test]
    fn from_vec() {
        let vec = vec![1, 2, 3];
        let smart_vec: SmartFat<i32, Arc> = SmartFat::from(vec);
        assert_eq!(smart_vec.as_vec(), &[1, 2, 3]);
    }
}
