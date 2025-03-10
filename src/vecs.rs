#![allow(unused)]

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::marker::PhantomData;
use core::mem::{self, ManuallyDrop};
use core::ptr::{self, NonNull};
use core::slice;

use thin::PrefixedThinVec;

use crate::common::manually_drop_as_ref;
use crate::smart::Kind;
use crate::Arc;

pub mod fat;
pub mod inline;
pub mod thin;

#[doc(inline)]
pub use inline::InlineVec;
pub use thin::{SmartThinVec, ThinVec};

#[derive(Clone, Copy, Debug)]
#[repr(usize)]
enum ZeroUsize {
    Zero = 0,
}

/// A guard that drops the initialized elements of a slice.
struct SliceGuard<T> {
    ptr: NonNull<T>,
    initialized: usize,
}

impl<T> Drop for SliceGuard<T> {
    fn drop(&mut self) {
        if mem::needs_drop::<T>() {
            unsafe {
                let slice = slice::from_raw_parts_mut(self.ptr.as_ptr(), self.initialized);
                ptr::drop_in_place(slice);
            }
        }
    }
}

union Either<T, C: Kind> {
    #[allow(unused)]
    fat: ManuallyDrop<Fat<T, C>>,
    #[allow(unused)]
    thin: ManuallyDrop<thin::PrefixedThinVec<T, thin::SmartPrefix<C>>>,
    inspect: ManuallyDrop<Inspect<C>>,
}

#[repr(C)]
struct Inspect<C> {
    count: C,
    ptr: *const (),
    cap: usize,
    len: usize,
}

enum Split<F, T> {
    Fat(F),
    Thin(T),
}

macro_rules! delegate_method_split {
    {} => {};
    {
        $(#[$m:meta])*
        $v:vis
        const
        fn $name:ident
        (&self $(, $p_name:ident : $p_type:ty)* $(,)?)
        $(-> $r_type:ty)?;

        $($remainder:tt)*
    } => {
        $(#[$m])*
        $v
        const
        fn $name (&self, $($p_name : $p_type),* ) $( -> $r_type)? {
            match self.split_ref() {
                Split::Fat(fat) => fat.as_vec().$name( $($p_name),*),
                Split::Thin(thin) => thin.as_vec().$name( $($p_name),*),
            }
        }

        delegate_method_split!($($remainder)*);
    };
    {
        $(#[$m:meta])*
        $v:vis
        fn $name:ident
        (&self$(, $p_name:ident : $p_type:ty)* $(,)?)
        $(-> $r_type:ty)?;

        $($remainder:tt)*
    } => {
        $(#[$m])*
        $v
        fn $name(&self, $($p_name : $p_type),*) $( -> $r_type)? {
            match self.split_ref() {
                Split::Fat(fat) => fat.$name($($p_name),*),
                Split::Thin(thin) => thin.$name($($p_name),*),
            }
        }

        delegate_method_split!($($remainder)*);
    };
}

/// A shared fat vector header.
///
/// This header is the whole vector.
#[derive(Clone, Debug)]
#[repr(C)]
struct Fat<T, C> {
    count: C,
    vec: ManuallyDrop<Vec<T>>,
}

impl<T, C: Kind> Fat<T, C> {
    /// Creates a new fat vector from a [`Vec`].
    fn new(vec: Vec<T>) -> Self {
        Self {
            count: C::one(),
            vec: ManuallyDrop::new(vec),
        }
    }
}

#[repr(transparent)]
pub struct SmartVec<T, C>(NonNull<Either<T, C>>)
where
    C: Kind;

impl<T, C: Kind> SmartVec<T, C> {
    fn from_fat(fat: fat::SmartFat<T, C>) -> Self {
        let fat = ManuallyDrop::new(fat);
        Self(fat.0.cast())
    }

    fn from_thin(thin: thin::SmartThinVec<T, C>) -> Self {
        let thin = ManuallyDrop::new(thin);
        Self(thin.0.cast())
    }

    /// INTERNAL USE ONLY: Returns a owned smart reference to the underlying representation.
    fn split_owned(self) -> Split<fat::SmartFat<T, C>, thin::SmartThinVec<T, C>> {
        let this = ManuallyDrop::new(self);
        if unsafe { this.0.as_ref().inspect.ptr.is_null() } {
            Split::Thin(thin::SmartThinVec(this.0.cast()))
        } else {
            Split::Fat(fat::SmartFat(this.0.cast()))
        }
    }

    /// INTERNAL USE ONLY: Returns a reference to the underlying vector
    const fn split_ref(&self) -> Split<&fat::SmartFat<T, C>, &thin::SmartThinVec<T, C>> {
        unsafe {
            if manually_drop_as_ref(&self.0.as_ref().inspect).ptr.is_null() {
                Split::Thin(mem::transmute(&self.0))
            } else {
                Split::Fat(mem::transmute(&self.0))
            }
        }
    }

    /// INTERNAL USE ONLY: Returns a mutable reference to the underlying vector
    fn split_mut(&mut self) -> Split<&mut fat::SmartFat<T, C>, &mut thin::SmartThinVec<T, C>> {
        unsafe {
            if self.0.as_ref().inspect.ptr.is_null() {
                Split::Thin(mem::transmute(&mut self.0))
            } else {
                Split::Fat(mem::transmute(&mut self.0))
            }
        }
    }

    pub(crate) fn from_vec(vec: Vec<T>) -> Self {
        Self::from_fat(fat::SmartFat::new(vec))
    }

    pub(crate) fn from_boxed(boxed: Box<[T]>) -> Self {
        Self::from_vec(boxed.into_vec())
    }

    pub fn from_slice_copy(slice: &[T]) -> Self
    where
        C: Kind,
        T: Copy,
    {
        Self::from_thin(thin::SmartThinVec::from_slice_copy(slice))
    }

    pub fn from_slice_clone(slice: &[T]) -> Self
    where
        C: Kind,
        T: Clone,
    {
        Self::from_thin(thin::SmartThinVec::from_slice_clone(slice))
    }

    delegate_method_split! {
        #[inline]
        #[must_use]
        pub fn as_ptr(&self) -> *const T;

        #[inline]
        #[must_use]
        pub fn len(&self) -> usize;

        #[inline]
        #[must_use]
        pub fn as_slice(&self) -> &[T];

        #[inline]
        #[must_use]
        pub fn capacity(&self) -> usize;

        #[inline]
        #[must_use]
        pub fn is_empty(&self) -> bool;
    }

    #[inline]
    pub fn as_mut_ptr(&mut self) -> Option<*mut T> {
        match self.split_mut() {
            Split::Fat(fat) => fat.as_mut_ptr(),
            Split::Thin(thin) => thin.mutate().map(PrefixedThinVec::as_mut_ptr),
        }
    }

    pub fn as_mut_slice(&mut self) -> Option<&mut [T]> {
        match self.split_mut() {
            Split::Fat(fat) => fat.as_mut_slice(),
            Split::Thin(thin) => thin.mutate().map(PrefixedThinVec::as_mut_slice),
        }
    }
}

impl<T, C> Drop for SmartVec<T, C>
where
    C: Kind,
{
    fn drop(&mut self) {
        match self.split_mut() {
            Split::Fat(fat) => unsafe { ptr::drop_in_place(fat) },
            Split::Thin(thin) => unsafe { ptr::drop_in_place(thin) },
        }
    }
}

impl<T, C> Clone for SmartVec<T, C>
where
    C: Kind,
{
    fn clone(&self) -> Self {
        match self.split_ref() {
            Split::Fat(fat) => Self::from_fat(fat.clone()),
            Split::Thin(thin) => Self::from_thin(thin.clone()),
        }
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec;
    use std::println;

    use super::*;
    use crate::Arc;

    #[test]
    fn from_vec() {
        let vec = vec![1, 2, 3];
        let ptr = SmartVec::<_, Arc>::from_vec(vec);
        assert_eq!(ptr.as_slice(), &[1, 2, 3]);
    }

    #[test]
    fn from_slice() {
        let slice = &[1, 2, 3];
        let ptr = SmartVec::<_, Arc>::from_slice_copy(slice);
        println!("ok");
        assert_eq!(ptr.as_slice(), &[1, 2, 3]);
    }
}
