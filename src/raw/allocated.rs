//! Allocated representation.

use core::marker::PhantomData;
use core::mem::{forget, ManuallyDrop, MaybeUninit};
use core::ops::{Deref, DerefMut, Range};
use core::panic::{RefUnwindSafe, UnwindSafe};
use core::ptr::NonNull;

// TODO remove once provenance API stabilized
use sptr::Strict;

use crate::alloc::vec::Vec;
use crate::backend::Backend;
use crate::smart::{self, Inner, Smart, UpdateResult};

const MASK: usize = super::MASK as usize;
const TAG: usize = super::TAG_ALLOCATED as usize;

/// Tagged smart pointer (with forced exposed provenance).
///
/// The exposed provenance is required to cast [`Allocated`] from and to the
/// [`Pivot`](super::Pivot) representation.
struct TaggedSmart<B: Backend>(usize, PhantomData<Smart<Vec<u8>, B>>);

// Manual implementation of Clone and Copy traits to avoid requiring additional
// trait bounds on the generic parameter B

impl<B: Backend> Clone for TaggedSmart<B> {
    #[cfg_attr(coverage_nightly, coverage(off))]
    fn clone(&self) -> Self {
        *self
    }
}

impl<B: Backend> Copy for TaggedSmart<B> {}

impl<B: Backend> TaggedSmart<B> {
    /// Constructed a tagged rc from a `rc::Raw`.
    #[inline]
    #[allow(unstable_name_collisions)]
    fn from(raw: Smart<Vec<u8>, B>) -> Self {
        let ptr = raw.into_raw().as_ptr();
        debug_assert!(ptr.is_aligned());
        debug_assert!((ptr as usize) & MASK == 0);

        // TODO use strict and exposed provenance API once stabilized

        // SAFETY: add a 2-bit tag to a non-null pointer with the same alignment
        // requirement as usize (typically 4 bytes on 32-bit architectures, and
        // more on 64-bit architectures)
        let addr = ptr.map_addr(|addr| addr | TAG).expose_addr();

        Self(addr, PhantomData)
    }

    /// Converts back into the `rc::Raw`.
    #[inline]
    #[allow(unstable_name_collisions)]
    fn into(self) -> smart::Smart<Vec<u8>, B> {
        let this: smart::Smart<Vec<u8>, B>;

        debug_assert!(self.0 & MASK == TAG);

        // SAFETY: remove a 2-bit tag to a non-null pointer with the same
        // alignment as usize (typically 4 on 32-bit architectures, and
        // more on 64-bit architectures)
        unsafe {
            // TODO use strict and exposed provenance API once stabilized
            let new_ptr = sptr::from_exposed_addr_mut::<Inner<Vec<u8>, B>>(self.0)
                .map_addr(|addr| addr ^ TAG);

            debug_assert!(!new_ptr.is_null());

            #[cfg(miri)]
            let _ = &*new_ptr; // check provenance early

            this = smart::Smart::from_raw(NonNull::new_unchecked(new_ptr));
        }

        this
    }

    /// Checks if the tag is valid.
    #[inline]
    const fn check_tag(self) -> bool {
        self.0 & MASK == TAG
    }

    /// Explicitly clones this tagged smart pointer.
    fn explicit_clone(self) -> Self {
        let r = ManuallyDrop::new(self.into());
        Self::from((*r).clone())
    }
}

/// Allocated representation.
///
/// # Warning!
///
/// For big-endian platform, the owner pointer is **after** the slice.
/// For little-endian platform, the owner pointer is **before** the slice.
#[repr(C)]
pub struct Allocated<B: Backend> {
    #[cfg(target_endian = "little")]
    /// Tagged smart pointer of the owning vector
    owner: TaggedSmart<B>,

    /// Pointer to the slice's start
    ptr: *const u8,

    /// Length of the slice
    len: usize,

    #[cfg(target_endian = "big")]
    /// Tagged smart pointer of the owning vector
    owner: TaggedSmart<B>,
}

impl<B: Backend> Copy for Allocated<B> {}

impl<B: Backend> Clone for Allocated<B> {
    #[cfg_attr(coverage_nightly, coverage(off))]
    fn clone(&self) -> Self {
        *self
    }
}

unsafe impl<B: Backend + Sync> Sync for Allocated<B> {}

unsafe impl<B: Backend + Send> Send for Allocated<B> {}

impl<B: Backend + Unpin> Unpin for Allocated<B> {}

impl<B: Backend + UnwindSafe> UnwindSafe for Allocated<B> {}

impl<B: Backend + RefUnwindSafe> RefUnwindSafe for Allocated<B> {}

impl<B: Backend> Allocated<B> {
    /// Converts the allocated representation into its owner.
    fn into_owner(self) -> Smart<Vec<u8>, B> {
        self.owner.into()
    }

    /// Returns a reference to the owner.
    ///
    /// This function buses the [`Copy`]-ness of [`Allocated`] to get a copy
    /// (and not a clone) of the [`Smart`] reference wrapped in [`ManuallyDrop`]
    /// to ensure it's not dropped.
    fn owner(&self) -> impl Deref<Target = Smart<Vec<u8>, B>> {
        ManuallyDrop::new(self.into_owner())
    }

    /// Returns a mutable reference to the owner.
    ///
    /// This function buses the [`Copy`]-ness of [`Allocated`] to get a copy
    /// (and not a clone) of the [`Smart`] reference wrapped in [`ManuallyDrop`]
    /// to ensure it's not dropped.
    ///
    /// # Safety
    ///
    /// The owner must not be shared, cf. [`Self::is_unique`].
    unsafe fn owner_mut(&mut self) -> impl DerefMut<Target = Smart<Vec<u8>, B>> {
        debug_assert!(self.is_unique());
        ManuallyDrop::new(self.into_owner())
    }

    /// Creates an allocated from a vector.
    ///
    /// Takes ownership of the vector without copying the data.
    #[inline]
    pub fn new(v: Vec<u8>) -> Self {
        let ptr = v.as_ptr();
        let len = v.len();
        let owner = Smart::new(v);

        let this = Self {
            ptr,
            len,
            owner: TaggedSmart::from(owner),
        };

        debug_assert!(this.is_unique());

        this
    }

    /// Returns the length of this allocated string.
    #[inline]
    pub const fn len(&self) -> usize {
        // NOTE: must be const to be used in Raw::len even if there is no
        // way the allocated representation will be used in the const case

        // debug_assert!(self.is_valid()); // not const

        self.len
    }

    /// Returns as a byte slice.
    #[inline]
    pub const fn as_slice(&self) -> &[u8] {
        // NOTE: must be const to be used in Raw::as_slice even if there is no
        // way the allocated representation will be used in the const case

        // debug_assert!(self.is_valid()); // not const

        // SAFETY: Type invariant
        unsafe { core::slice::from_raw_parts(self.ptr, self.len) }
    }

    /// Returns a raw pointer to the first element.
    #[inline]
    pub const fn as_ptr(&self) -> *const u8 {
        // NOTE: must be const to be used in Raw::as_ptr even if there is no way
        // the allocated representation will be used in the const case

        // debug_assert!(self.is_valid()); // is_valid is not const!
        self.ptr
    }

    /// Returns a mutable slice if possible (unique non-static reference).
    #[inline]
    pub fn as_mut_slice(&mut self) -> Option<&mut [u8]> {
        if self.is_unique() {
            // SAFETY:
            // * unique -> no one else can "see" the string
            // * type invariant -> valid slice
            Some(unsafe { self.as_mut_slice_unchecked() })
        } else {
            None
        }
    }

    /// Returns a mutable slice.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the `Allocated` is actually uniquely shared.
    #[inline]
    pub unsafe fn as_mut_slice_unchecked(&mut self) -> &mut [u8] {
        debug_assert!(self.is_valid());
        debug_assert!(self.is_unique());

        unsafe { core::slice::from_raw_parts_mut(self.ptr.cast_mut(), self.len) }
    }

    /// Creates a new `Allocated` for some range with the same owner.
    ///
    /// # Safety
    ///
    /// Range must be a range `a..b` such that `a <= b <= len`.
    #[inline]
    pub unsafe fn slice_unchecked(&self, range: Range<usize>) -> Self {
        debug_assert!(self.is_valid());
        debug_assert!(range.start <= range.end);
        debug_assert!(range.start <= self.len);
        debug_assert!(range.end <= self.len);

        let owner = self.owner.explicit_clone();

        // SAFETY: type invariant -> self.ptr..self.ptr+self.len is valid
        // also Rust like C specify you can move to the last + 1
        let ptr = unsafe { self.ptr.add(range.start) };

        Self {
            ptr,
            len: range.len(),
            owner,
        }
    }

    /// Clones this vector.
    #[inline]
    pub fn explicit_clone(&self) -> Self {
        debug_assert!(self.is_valid());

        let owner = self.owner();
        if owner.incr() == UpdateResult::Overflow {
            Self::new(self.as_slice().to_vec())
        } else {
            *self
        }
    }

    /// Drops this vector explicitly.
    #[inline]
    pub fn explicit_drop(self) {
        debug_assert!(self.is_valid());
        let _ = self.into_owner();
    }

    /// Return `true` iff this representation is valid.
    #[inline]
    #[cfg_attr(coverage_nightly, coverage(off))]
    pub fn is_valid(&self) -> bool {
        if !self.owner.check_tag() {
            return false;
        }

        let owner = self.owner();
        let owner_ptr = owner.as_ptr();
        let shift = unsafe { self.ptr.offset_from(owner_ptr) };
        shift >= 0 && {
            #[allow(clippy::cast_sign_loss)]
            let shift = shift as usize;
            shift <= owner.len() && shift + self.len <= owner.len()
        }
    }

    /// Returns the backend capacity.
    #[inline]
    pub fn capacity(&self) -> usize {
        debug_assert!(self.is_valid());

        self.owner().capacity()
    }

    /// Unwraps the inner vector if it makes any sense.
    #[inline]
    pub fn try_into_vec(self) -> Result<Vec<u8>, Self> {
        debug_assert!(self.is_valid());

        let owner = self.owner();
        if self.ptr != owner.as_ptr() {
            // the starts differ, cannot truncate
            return Err(self);
        }

        let len = self.len();

        self.into_owner().try_unwrap().map_or_else(
            |owner| {
                forget(owner); // do not drop
                Err(self)
            },
            |mut owner| {
                owner.truncate(len);
                Ok(owner)
            },
        )
    }

    /// Returns `true` if there is only one reference to the underlying vector.
    pub fn is_unique(&self) -> bool {
        debug_assert!(self.is_valid());

        self.owner().is_unique()
    }

    /// Pushes a slice at the end of the underlying vector.
    ///
    /// # Safety
    ///
    /// The reference must be unique, cf. [`Self::is_unique`].
    pub unsafe fn push_slice_unchecked(&mut self, addition: &[u8]) {
        debug_assert!(self.is_valid());

        // SAFETY: unique by precondition
        let mut owner = unsafe { self.owner_mut() };

        // SAFETY: unique by precondition
        let v = unsafe { owner.as_mut_unchecked() };

        // SAFETY: compute the shift from within the vector range (type invariant)
        #[allow(clippy::cast_sign_loss)]
        let shift = unsafe { self.ptr.offset_from(v.as_ptr()) as usize };
        v.truncate(shift + self.len);
        v.extend_from_slice(addition);
        self.len += addition.len();

        // SAFETY: shift to within the vector range (the shift was already
        // in the old range).
        self.ptr = unsafe { v.as_ptr().add(shift) };
    }

    /// Returns the remaining spare capacity of the unique vector as a slice of
    /// `MaybeUnit<u8>`. If the vector is actually shared, returns an empty
    /// slice.
    ///
    /// The returned slice can be used to fill the vector with data (e.g. by
    /// reading from a file) before marking the data as initialized using the
    /// `set_len` method.
    pub fn spare_capacity_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        debug_assert!(self.is_valid());

        if !self.is_unique() {
            return &mut [];
        }

        // SAFETY: unique checked above
        let mut owner = unsafe { self.owner_mut() };

        // SAFETY: lifetime is extended to `'_` only
        let v = unsafe { owner.as_mut_unchecked_extended() };

        // SAFETY: computes the shift from within the vector range (type
        // invariant)
        #[allow(clippy::cast_sign_loss)]
        let start = unsafe { self.ptr.offset_from(v.as_ptr()) as usize };

        // truncates to the actual used length without shrinking
        v.truncate(start + self.len);

        v.spare_capacity_mut()
    }

    /// Forces the length of the vector to `new_len`.
    ///
    /// # Safety
    ///
    /// Either:
    /// 1. `new_len` is less than or equal to the current length, in which case
    ///    this truncates the vector, or
    /// 2. All of these conditions must be met:
    ///    - `new_len` is greater than `capacity()`
    ///    - The elements at `old_len..new_len` must be properly initialized
    ///    - The vector must be uniquely owned (not shared)
    ///
    /// Failing to meet these safety requirements can lead to undefined
    /// behavior.
    pub unsafe fn set_len(&mut self, new_len: usize) {
        if new_len <= self.len {
            self.len = new_len;
            return;
        }

        debug_assert!(self.is_unique());
        debug_assert!(new_len <= self.capacity());

        // SAFETY: uniqueness is a precondition
        let mut owner = unsafe { self.owner_mut() };

        // SAFETY: uniqueness is a precondition
        let v = unsafe { owner.as_mut_unchecked() };

        // SAFETY: compute the shift from within the vector range (type invariant)
        #[allow(clippy::cast_sign_loss)]
        let start = unsafe { self.ptr.offset_from(v.as_ptr()).abs_diff(0) };
        unsafe { v.set_len(start + new_len) };
        self.len = new_len;
    }

    /// Shrinks the capacity of the underlying vector as close as possible to
    /// `min_capacity`.
    ///
    /// The capacity will not shrink below the length of the vector or the
    /// supplied minimum capacity. That is, if the current capacity is less than
    /// or equal to the minimum capacity, no shrinking is done.
    pub fn shrink_to(&mut self, min_capacity: usize) {
        let min_capacity = min_capacity.max(self.len);

        if self.capacity() <= min_capacity {
            return;
        }

        let mut new_vec = Vec::with_capacity(min_capacity);
        new_vec.extend_from_slice(self.as_slice());
        let old = core::mem::replace(self, Self::new(new_vec));
        old.explicit_drop();
    }
}

#[cfg(test)]
mod tests {
    use super::Allocated;
    use crate::alloc::vec;
    use crate::Rc;

    #[test]
    fn test_alloc() {
        let allocated = Allocated::<Rc>::new(vec![]);
        let _ = allocated.explicit_drop();
    }

    #[test]
    #[cfg_attr(coverage_nightly, coverage(off))]
    fn test_try_into_vec() {
        let allocated = Allocated::<Rc>::new(vec![0, 1, 2]);
        assert_eq!(allocated.owner().ref_count(), 1);

        {
            let slice = unsafe { allocated.slice_unchecked(1..2) };

            assert_eq!(allocated.owner().ref_count(), 2);
            let Err(allocated) = slice.try_into_vec() else {
                panic!("shared reference cannot be converted to vec")
            };
            allocated.explicit_drop();
        }

        assert_eq!(allocated.owner().ref_count(), 1);

        assert!(allocated.try_into_vec().is_ok());
    }
}
