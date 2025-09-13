use alloc::boxed::Box;
use alloc::vec::Vec;
use core::mem::ManuallyDrop;
use core::ptr::{self, NonNull};

use rules_derive::rules_derive;

use super::reprs::FatRepr;
use crate::backend::{BackendImpl, CloneOnOverflow, Counter, PanicOnOverflow, UpdateResult};
use crate::common::derives::*;
use crate::common::manually_drop_as_mut;
use crate::vecs::reprs::FatInner;
use crate::Backend;

/// A smart fat vector with reference counting.
#[repr(transparent)]
#[rules_derive(
    ConstDefault(Self::EMPTY),
    From(source = Vec<T>, cons = Self::from_vec),
)]
pub struct SmartFatVec<T, B: Backend>(FatRepr<T, B>);

impl<T, B: Backend> SmartFatVec<T, B> {
    const EMPTY: Self = Self(FatRepr::EMPTY);

    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self::EMPTY
    }

    #[inline]
    pub(super) const unsafe fn from_repr(repr: FatRepr<T, B>) -> Self {
        Self(repr)
    }

    /// Creates a new `SmartFatVec` from a standard `Vec`.
    pub(crate) fn from_vec(vec: Vec<T>) -> Self {
        let cap = vec.capacity();
        let repr = if cap == 0 {
            FatRepr::EMPTY
        } else {
            let mut vec = ManuallyDrop::new(vec);

            // SAFETY: the vector ptr is not null by type invariant
            // as_non_null is not stable yet
            let ptr = unsafe { NonNull::new_unchecked(vec.as_mut_ptr()) };
            let len = vec.len();
            let inner = Box::new(FatInner {
                prefix: B::DEFAULT,
                ptr,
                cap,
                len,
            });
            let inner = Box::into_raw(inner);
            // SAFETY: Box pointer is not null
            let inner = unsafe { NonNull::new_unchecked(inner) };
            FatRepr::new(inner)
        };
        Self(repr)
    }

    #[must_use]
    pub const fn as_ptr(&self) -> *const T {
        match self.0.as_ref() {
            Some(inner) => inner.ptr.as_ptr(),
            None => ptr::dangling(),
        }
    }

    #[must_use]
    pub const fn capacity(&self) -> usize {
        match self.0.as_ref() {
            Some(inner) => inner.cap,
            None => 0,
        }
    }

    #[must_use]
    pub const fn len(&self) -> usize {
        match self.0.as_ref() {
            Some(inner) => inner.len,
            None => 0,
        }
    }

    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[must_use]
    pub const fn as_slice(&self) -> &[T] {
        unsafe { core::slice::from_raw_parts(self.as_ptr(), self.len()) }
    }

    #[must_use]
    pub fn is_unique(&self) -> bool {
        self.0.as_ref().is_none_or(|inner| inner.prefix.is_unique())
    }

    pub fn as_mut(&mut self) -> Option<RefMut<'_, T, B>> {
        if self.is_unique() {
            Some(unsafe { self.as_mut_unchecked() })
        } else {
            None
        }
    }

    /// Gets a mutable reference to the underlying vector without
    /// checking for uniqueness.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the vector is uniquely owned, i.e. no other
    /// references (clones) to the same data exist. Failing to do so may
    /// result in undefined behavior.
    #[must_use]
    pub unsafe fn as_mut_unchecked(&mut self) -> RefMut<'_, T, B> {
        let vec = self.0.as_mut().map_or_else(Vec::new, |inner| unsafe {
            Vec::from_raw_parts(inner.ptr.as_ptr(), inner.len, inner.cap)
        });
        RefMut(ManuallyDrop::new(vec), self)
    }

    #[must_use]
    pub fn try_clone(&self) -> Option<Self> {
        if let Some(inner) = self.0.as_ref() {
            if inner.prefix.incr() == UpdateResult::Overflow {
                return None;
            }
            // now when can copy the repr
        } else {
            // empty vector's repr is copyable
        }
        Some(unsafe { self.copy() })
    }

    const unsafe fn copy(&self) -> Self {
        Self(self.0)
    }
}

impl<T, B: Backend> Drop for SmartFatVec<T, B> {
    fn drop(&mut self) {
        if let Some(inner) = self.0.as_mut() {
            if inner.prefix.decr() == UpdateResult::Overflow {
                let ptr = inner.ptr.as_ptr();
                let len = inner.len;
                let cap = inner.cap;
                // SAFETY: we are taking ownership of the vector, so the pointer is valid
                // and was allocated by the global allocator
                let _ = unsafe { Vec::from_raw_parts(ptr, len, cap) };
            }
        }
    }
}

impl<T, C: Counter> Clone for SmartFatVec<T, BackendImpl<C, PanicOnOverflow>> {
    #[track_caller]
    fn clone(&self) -> Self {
        let Some(clone) = self.try_clone() else {
            panic!("count overflow");
        };
        clone
    }
}

impl<T: Clone, C: Counter> Clone for SmartFatVec<T, BackendImpl<C, CloneOnOverflow>> {
    fn clone(&self) -> Self {
        self.try_clone()
            .unwrap_or_else(|| Self::from_vec(self.as_slice().to_vec()))
    }
}

pub struct RefMut<'a, T, B: Backend>(ManuallyDrop<Vec<T>>, &'a mut SmartFatVec<T, B>);

impl<T, B: Backend> core::ops::Deref for RefMut<'_, T, B> {
    type Target = Vec<T>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T, B: Backend> core::ops::DerefMut for RefMut<'_, T, B> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T, B: Backend> Drop for RefMut<'_, T, B> {
    fn drop(&mut self) {
        let vec = &mut *self.0;
        let len = vec.len();
        let cap = vec.capacity();
        let ptr = unsafe { NonNull::new_unchecked(vec.as_mut_ptr()) };

        if let Some(inner) = self.1 .0.as_mut() {
            inner.len = len;
            inner.cap = cap;
            inner.ptr = ptr;
        } else {
            let inner = Box::new(FatInner {
                prefix: B::DEFAULT,
                len: 0,
                cap: 0,
                ptr: NonNull::dangling(),
            });
            let inner = Box::into_raw(inner);
            // SAFETY: Box pointer is not null
            let inner = unsafe { NonNull::new_unchecked(inner) };

            self.1 .0 = FatRepr::new(inner);
        }
    }
}
