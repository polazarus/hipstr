//! Smart vector type (fat or thin).

use alloc::vec::Vec;
use core::marker::PhantomData;
use core::mem::{offset_of, transmute, ManuallyDrop, MaybeUninit};
use core::num::NonZeroUsize;
use core::ptr;
use core::ptr::NonNull;

use super::smart_thin::SmartThinVec;
use super::thin::ThinHandle;
use crate::backend::{
    Backend, BackendImpl, CloneOnOverflow, Counter, PanicOnOverflow, UpdateResult,
};
use crate::macros::trait_impls;
use crate::smart::{Inner, Smart};
use crate::vecs::thin::Header;

#[cfg(test)]
mod tests;

const TAG_MASK: usize = 0b11 as usize;
const THIN_BIT: usize = 0b01;
const TAG_THIN: usize = 0b11;
const TAG_FAT: usize = 0b10;
const TAG_OWNED_MASK: usize = 0b10;

enum Variant<F, T> {
    Fat(F),
    Thin(T),
}

/// Tagged smart pointer.
#[repr(transparent)]
struct TaggedSmart<T, B>(NonNull<()>, PhantomData<(Vec<T>, B)>);

// Manual implementation of Clone and Copy traits to avoid requiring additional
// trait bounds on the generic parameter B

impl<T, B> Clone for TaggedSmart<T, B> {
    #[cfg_attr(coverage_nightly, coverage(off))]
    fn clone(&self) -> Self {
        *self
    }
}

impl<T, B> Copy for TaggedSmart<T, B> {}

impl<T, B: Backend> TaggedSmart<T, B> {
    /// Gets the owner.
    fn get(self) -> Variant<Smart<Vec<T>, B>, SmartThinVec<T, B>> {
        let ptr = self.ptr();

        if self.is_fat() {
            Variant::Fat(unsafe { Smart::from_raw(ptr.cast()) })
        } else {
            Variant::Thin(unsafe { SmartThinVec::from_raw(ptr.cast()) })
        }
    }

    fn addr(self) -> usize {
        self.0.as_ptr() as usize
    }

    #[inline]
    fn is_thin(self) -> bool {
        debug_assert!(self.check_tag());
        self.addr() & THIN_BIT != 0
    }

    #[inline]
    fn is_fat(self) -> bool {
        debug_assert!(self.check_tag());
        self.addr() & THIN_BIT == 0
    }

    fn ptr(self) -> NonNull<()> {
        debug_assert!(self.check_tag());

        self.0.map_addr(|addr| {
            // SAFETY: the pointer is non-null and aligned
            unsafe { NonZeroUsize::new_unchecked(addr.get() & !TAG_MASK) }
        })
    }

    /// Constructed a tagged smart pointer from a [`Smart`].
    #[inline]
    fn from_fat(raw: Smart<Vec<T>, B>) -> Self {
        let ptr = Smart::into_raw(raw);
        debug_assert!(ptr.is_aligned());
        debug_assert!(ptr.addr().get() & TAG_MASK == 0);

        // SAFETY: add a 2-bit tag to a non-null pointer with the same alignment
        // requirement as usize (typically 4 bytes on 32-bit architectures, and
        // more on 64-bit architectures)
        let tagged = ptr.map_addr(|addr| addr | TAG_FAT).cast();

        let this = Self(tagged, PhantomData);
        debug_assert!(this.check_tag());
        debug_assert!(this.is_fat());
        this
    }

    #[inline]
    fn from_thin(raw: SmartThinVec<T, B>) -> Self {
        let ptr = SmartThinVec::into_raw(raw);
        debug_assert!(ptr.is_aligned());
        debug_assert!(ptr.addr().get() & TAG_MASK == 0);

        // SAFETY: add a 2-bit tag to a non-null pointer with the same alignment
        // requirement as usize (typically 4 bytes on 32-bit architectures, and
        // more on 64-bit architectures)
        let tagged = ptr.map_addr(|addr| addr | TAG_THIN).cast();

        let this = Self(tagged, PhantomData);
        debug_assert!(this.check_tag());
        debug_assert!(this.is_thin());
        this
    }

    /// Returns a reference to the counter.
    #[inline]
    fn count(&self) -> &B {
        const {
            assert!(offset_of!(Header<T, B>, prefix) == 0);
            assert!(offset_of!(Inner<Vec<T>, B>, count) == 0);
        }
        let counter: &B = unsafe { self.ptr().cast().as_ref() };

        #[cfg(debug_assertions)]
        {
            let m = ManuallyDrop::new(self.get());
            unsafe {
                match &*m {
                    Variant::Fat(fat) => {
                        debug_assert_eq!(&raw const fat.0.as_ref().count, ptr::from_ref(counter));
                    }
                    Variant::Thin(thin) => {
                        debug_assert_eq!(&raw const thin.0.as_ref().prefix, ptr::from_ref(counter));
                    }
                }
            }
        }

        counter
    }

    #[inline]
    fn as_slice(&self) -> &[T] {
        let v = ManuallyDrop::new(self.get());
        let short_lived = match &*v {
            Variant::Fat(fat) => fat.as_slice(),
            Variant::Thin(thin) => thin.as_slice(),
        };
        // SAFETY: the owner is valid.
        unsafe { transmute(short_lived) }
    }

    /// Checks if the tag is valid.
    #[inline]
    fn check_tag(self) -> bool {
        let addr = self.0.addr().get();
        (addr & !TAG_MASK) != 0 && (addr & TAG_OWNED_MASK as usize) != 0
    }
}

/// A smart vector.
///
/// This type has two internal representations:
///
/// - *fat* representation: [`Smart<Vec<T>, B>`].
///   A double indirection is needed to access the vector's data.
/// - *thin* representation: [`SmartThinVec<T, B>`].
#[repr(transparent)]
pub struct SmartVec<T, B: Backend>(TaggedSmart<T, B>);

impl<T, B: Backend> SmartVec<T, B> {
    /// Creates a new smart vector.
    pub fn new() -> Self {
        let thin = SmartThinVec::new();
        let tagged_ptr = TaggedSmart::from_thin(thin);
        Self(tagged_ptr)
    }

    /// Creates a new smart vector with the given capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        let thin = SmartThinVec::with_capacity(capacity);
        let tagged_ptr = TaggedSmart::from_thin(thin);
        Self(tagged_ptr)
    }

    #[inline]
    pub fn is_thin(&self) -> bool {
        self.0.is_thin()
    }

    #[inline]
    pub fn is_fat(&self) -> bool {
        self.0.is_fat()
    }

    fn from_fat(raw: Smart<Vec<T>, B>) -> Self {
        let tagged_ptr = TaggedSmart::from_fat(raw);
        Self(tagged_ptr)
    }

    fn from_thin(raw: SmartThinVec<T, B>) -> Self {
        let tagged_ptr = TaggedSmart::from_thin(raw);
        Self(tagged_ptr)
    }

    pub fn as_slice(&self) -> &[T] {
        self.0.as_slice()
    }

    pub fn as_ptr(&self) -> *const T {
        let v = ManuallyDrop::new(self.0.get());
        match &*v {
            Variant::Fat(fat) => fat.as_ptr(),
            Variant::Thin(thin) => thin.as_ptr(),
        }
    }

    /// Returns the length of the vector.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hipstr::vecs::SmartVec;
    /// use hipstr::Arc;
    ///
    /// let mut v = SmartVec::<i32, Arc>::new();
    /// assert_eq!(v.len(), 0);
    /// v.mutate().push(1);
    /// assert_eq!(v.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        let v = ManuallyDrop::new(self.0.get());
        match &*v {
            Variant::Fat(fat) => fat.len(),
            Variant::Thin(thin) => thin.len(),
        }
    }

    pub fn capacity(&self) -> usize {
        let v = ManuallyDrop::new(self.0.get());
        match &*v {
            Variant::Fat(fat) => fat.capacity(),
            Variant::Thin(thin) => thin.capacity(),
        }
    }

    pub fn is_empty(&self) -> bool {
        let v = ManuallyDrop::new(self.0.get());
        match &*v {
            Variant::Fat(fat) => fat.is_empty(),
            Variant::Thin(thin) => thin.is_empty(),
        }
    }

    /// Returns true if this vector reference is unique, that is, not shared.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hipstr::vecs::SmartVec;
    /// use hipstr::Arc;
    ///
    /// let v = SmartVec::<i32, Arc>::new();
    /// assert!(v.is_unique());
    /// let w = v.clone();
    /// assert!(!v.is_unique());
    /// ```
    pub fn is_unique(&self) -> bool {
        self.count().is_unique()
    }

    pub fn mutate(&mut self) -> RefMut<T, B>
    where
        T: Clone,
    {
        let mut v = ManuallyDrop::new(self.0.get());
        let r = match &mut *v {
            Variant::Fat(fat) => {
                if let Some(mut_vec) = fat.as_mut() {
                    Variant::Fat(unsafe { transmute::<&mut Vec<T>, &mut Vec<T>>(mut_vec) })
                } else {
                    let mut thin = SmartThinVec::<T, B>::from_slice_clone(fat.as_slice());
                    let handle = unsafe { thin.handle().extend_lifetime() };
                    self.0 = TaggedSmart::from_thin(thin);
                    Variant::Thin(handle)
                }
            }
            Variant::Thin(thin) => {
                let _ = thin.mutate();
                let handle = unsafe { thin.handle().extend_lifetime() };
                Variant::Thin(handle)
            }
        };
        RefMut(r)
    }

    pub fn mutate_copy(&mut self) -> RefMut<T, B>
    where
        T: Copy,
    {
        let mut v = ManuallyDrop::new(self.0.get());
        let r = match &mut *v {
            Variant::Fat(fat) => {
                if let Some(mut_vec) = fat.as_mut() {
                    Variant::Fat(unsafe { transmute::<&mut Vec<T>, &mut Vec<T>>(mut_vec) })
                } else {
                    let mut thin = SmartThinVec::<T, B>::from_slice_copy(fat.as_slice());
                    let handle = unsafe { thin.handle().extend_lifetime() };
                    self.0 = TaggedSmart::from_thin(thin);
                    Variant::Thin(handle)
                }
            }
            Variant::Thin(thin) => {
                let _ = thin.mutate_copy();
                let handle = unsafe { thin.handle().extend_lifetime() };
                Variant::Thin(handle)
            }
        };
        RefMut(r)
    }

    pub fn as_mut(&mut self) -> Option<RefMut<T, B>> {
        if self.count().is_unique() {
            let r = {
                let mut v = ManuallyDrop::new(self.0.get());

                // SAFETY: uniqueness checked above
                match &mut *v {
                    Variant::Fat(fat) => Variant::Fat(unsafe { fat.as_mut_unchecked_extended() }),
                    Variant::Thin(thin) => {
                        Variant::Thin(unsafe { thin.handle().extend_lifetime() })
                    }
                }
            };
            Some(RefMut(r))
        } else {
            None
        }
    }

    pub fn try_clone(&self) -> Option<Self> {
        if self.count().incr() == UpdateResult::Done {
            Some(Self(self.0))
        } else {
            None
        }
    }

    fn count(&self) -> &B {
        self.0.count()
    }

    pub fn force_clone(&self) -> Self
    where
        T: Clone,
    {
        self.try_clone().unwrap_or_else(|| {
            let v = ManuallyDrop::new(self.0.get());
            let t = match &*v {
                Variant::Fat(fat) => SmartThinVec::from_slice_clone(fat.as_slice()),
                Variant::Thin(thin) => thin.force_clone(),
            };
            Self::from_thin(t)
        })
    }

    pub fn force_clone_or_copy(&self) -> Self
    where
        T: Copy,
    {
        self.try_clone().unwrap_or_else(|| {
            let v = ManuallyDrop::new(self.0.get());
            let t = match &*v {
                Variant::Fat(fat) => SmartThinVec::from_slice_copy(fat.as_slice()),
                Variant::Thin(thin) => thin.force_clone_or_copy(),
            };
            Self::from_thin(t)
        })
    }
}

impl<T, C: Counter> Clone for SmartVec<T, BackendImpl<C, PanicOnOverflow>> {
    fn clone(&self) -> Self {
        self.try_clone().unwrap_or_else(|| panic!("count overflow"))
    }
}

impl<T: Clone, C: Counter> Clone for SmartVec<T, BackendImpl<C, CloneOnOverflow>> {
    fn clone(&self) -> Self {
        self.force_clone()
    }
}

impl<T, B: Backend> Drop for SmartVec<T, B> {
    fn drop(&mut self) {
        let _ = self.0.get();
    }
}

pub struct RefMut<'a, T, P>(Variant<&'a mut Vec<T>, ThinHandle<'a, T, P>>);

impl<'a, T, P> RefMut<'a, T, P> {
    pub fn as_slice(&self) -> &[T] {
        match &self.0 {
            Variant::Fat(fat) => fat.as_slice(),
            Variant::Thin(thin) => thin.as_slice(),
        }
    }

    pub fn as_mut_slice(&mut self) -> &mut [T] {
        match &mut self.0 {
            Variant::Fat(fat) => fat.as_mut_slice(),
            Variant::Thin(thin) => thin.as_mut_slice(),
        }
    }

    pub fn push(&mut self, value: T) {
        match &mut self.0 {
            Variant::Fat(fat) => fat.push(value),
            Variant::Thin(thin) => thin.push(value),
        }
    }

    pub fn pop(&mut self) -> Option<T> {
        match &mut self.0 {
            Variant::Fat(fat) => fat.pop(),
            Variant::Thin(thin) => thin.pop(),
        }
    }

    pub fn insert(&mut self, index: usize, value: T) {
        match &mut self.0 {
            Variant::Fat(fat) => fat.insert(index, value),
            Variant::Thin(thin) => thin.insert(index, value),
        }
    }

    pub fn remove(&mut self, index: usize) -> T {
        match &mut self.0 {
            Variant::Fat(fat) => fat.remove(index),
            Variant::Thin(thin) => thin.remove(index),
        }
    }

    pub fn clear(&mut self) {
        match &mut self.0 {
            Variant::Fat(fat) => fat.clear(),
            Variant::Thin(thin) => thin.clear(),
        }
    }

    pub fn reserve(&mut self, additional: usize) {
        match &mut self.0 {
            Variant::Fat(fat) => fat.reserve(additional),
            Variant::Thin(thin) => thin.reserve(additional),
        }
    }

    pub fn reserve_exact(&mut self, additional: usize) {
        match &mut self.0 {
            Variant::Fat(fat) => fat.reserve_exact(additional),
            Variant::Thin(thin) => thin.reserve_exact(additional),
        }
    }

    pub fn shrink_to_fit(&mut self) {
        match &mut self.0 {
            Variant::Fat(fat) => fat.shrink_to_fit(),
            Variant::Thin(thin) => thin.shrink_to_fit(),
        }
    }

    pub fn shrink_to(&mut self, min_capacity: usize) {
        match &mut self.0 {
            Variant::Fat(fat) => fat.shrink_to(min_capacity),
            Variant::Thin(thin) => thin.shrink_to(min_capacity),
        }
    }

    pub fn truncate(&mut self, len: usize) {
        match &mut self.0 {
            Variant::Fat(fat) => fat.truncate(len),
            Variant::Thin(thin) => thin.truncate(len),
        }
    }

    pub fn split_off(&mut self, at: usize) -> SmartVec<T, P>
    where
        P: Backend,
    {
        match &mut self.0 {
            Variant::Fat(fat) => {
                let new = fat.split_off(at);
                SmartVec::from_fat(Smart::new(new))
            }
            Variant::Thin(thin) => {
                let new = thin.split_off(at);
                SmartVec::from_thin(SmartThinVec::from_thin_vec(new))
            }
        }
    }

    pub fn as_ptr(&self) -> *const T {
        match &self.0 {
            Variant::Fat(fat) => fat.as_ptr(),
            Variant::Thin(thin) => thin.as_ptr(),
        }
    }

    pub fn as_mut_ptr(&mut self) -> *mut T {
        match &mut self.0 {
            Variant::Fat(fat) => fat.as_mut_ptr(),
            Variant::Thin(thin) => thin.as_mut_ptr(),
        }
    }

    pub fn spare_capacity_mut(&mut self) -> &mut [MaybeUninit<T>] {
        match &mut self.0 {
            Variant::Fat(fat) => fat.spare_capacity_mut(),
            Variant::Thin(thin) => thin.spare_capacity_mut(),
        }
    }

    pub unsafe fn set_len(&mut self, len: usize) {
        unsafe {
            match &mut self.0 {
                Variant::Fat(fat) => fat.set_len(len),
                Variant::Thin(thin) => thin.set_len(len),
            }
        }
    }

    pub fn extend_from_slice(&mut self, other: &[T])
    where
        T: Clone,
    {
        match &mut self.0 {
            Variant::Fat(fat) => fat.extend_from_slice(other),
            Variant::Thin(thin) => thin.extend_from_slice(other),
        }
    }

    pub fn extend_from_slice_copy(&mut self, other: &[T])
    where
        T: Copy,
    {
        match &mut self.0 {
            Variant::Fat(fat) => fat.extend_from_slice(other),
            Variant::Thin(thin) => thin.extend_from_slice_copy(other),
        }
    }

    fn extend_iter(&mut self, iter: impl IntoIterator<Item = T>) {
        match &mut self.0 {
            Variant::Fat(fat) => fat.extend(iter),
            Variant::Thin(thin) => thin.extend_iter(iter),
        }
    }
}

trait_impls! {
    [T, B] where [B: Backend] {
        Extend { T => RefMut<'_, T, B>; }
    }
}
