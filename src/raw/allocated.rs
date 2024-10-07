//! Allocated representation.

use core::marker::PhantomData;
use core::mem::{transmute, MaybeUninit};
use core::ops::Range;
use core::panic::{RefUnwindSafe, UnwindSafe};

// TODO remove once provenance API stabilized
use sptr::Strict;

use crate::alloc::vec::Vec;
use crate::backend::rc::Inner;
use crate::backend::{rc, Backend};

const MASK: usize = super::MASK as usize;
const TAG: usize = super::TAG_ALLOCATED as usize;

struct TaggedRawRc<B: Backend>(usize, PhantomData<rc::Raw<Vec<u8>, B>>);

impl<B: Backend> Clone for TaggedRawRc<B> {
    #[cfg_attr(coverage_nightly, coverage(off))]
    fn clone(&self) -> Self {
        *self
    }
}

impl<B: Backend> Copy for TaggedRawRc<B> {}

impl<B: Backend> TaggedRawRc<B> {
    /// Constructed a tagged rc from a `rc::Raw`.
    #[inline]
    #[allow(unstable_name_collisions)]
    fn from(raw: rc::Raw<Vec<u8>, B>) -> Self {
        // SAFETY: add a 2-bit tag to a non-null pointer with the same alignment
        // requirement as usize (typically 4 bytes on 32-bit architectures, and
        // more on 64-bit architectures)
        unsafe {
            let ptr: *mut Inner<Vec<u8>, B> = transmute(raw);
            debug_assert!((ptr as usize) & MASK == 0);
            debug_assert!(!ptr.is_null());

            // TODO use strict and exposed provenance API once stabilized
            let addr = ptr.map_addr(|addr| addr | TAG).expose_addr();

            Self(addr, PhantomData)
        }
    }

    /// Converts back into the `rc::Raw`.
    #[inline]
    #[allow(unstable_name_collisions)]
    fn into(self) -> rc::Raw<Vec<u8>, B> {
        let this: rc::Raw<Vec<u8>, B>;

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

            this = transmute::<*mut rc::Inner<_, _>, rc::Raw<_, _>>(new_ptr);

            debug_assert!(this.is_valid());
        }

        this
    }

    /// Checks if the tag is valid.
    #[inline]
    const fn check_tag(self) -> bool {
        self.0 & MASK == TAG
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
    owner: TaggedRawRc<B>,

    /// Pointer to the slice's start
    ptr: *const u8,

    /// Length of the slice
    len: usize,

    #[cfg(target_endian = "big")]
    /// Tagged smart pointer of the owning vector
    owner: TaggedRawRc<B>,
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
    fn owner(&self) -> rc::Raw<Vec<u8>, B> {
        self.owner.into()
    }

    /// Creates an allocated from a vector.
    ///
    /// Takes ownership of the vector without copying the data.
    #[inline]
    pub fn new(v: Vec<u8>) -> Self {
        let ptr = v.as_ptr();
        let len = v.len();
        let owner = rc::Raw::new(v);

        let this = Self {
            ptr,
            len,
            owner: TaggedRawRc::from(owner),
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
        // NOTE: must be const to be used in Raw::as_ptr even if there is no
        // way the allocated representation will be used in the const case

        // debug_assert!(self.is_valid()); // is_valid is not const!
        self.ptr
    }

    /// Returns a mutable slice if possible (unique non-static reference).
    #[inline]
    pub fn as_mut_slice(&mut self) -> Option<&mut [u8]> {
        debug_assert!(self.is_valid());

        // SAFETY: type invariant, valid owner
        let is_unique = unsafe { self.owner().is_unique() };

        if is_unique {
            // SAFETY:
            // * unique -> no one else can "see" the string
            // * type invariant -> valid slice
            Some(unsafe { core::slice::from_raw_parts_mut(self.ptr.cast_mut(), self.len) })
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

        self.incr_ref_count();

        // SAFETY: type invariant -> self.ptr..self.ptr+self.len is valid
        // also Rust like C specify you can move to the last + 1
        let ptr = unsafe { self.ptr.add(range.start) };

        Self {
            ptr,
            len: range.len(),
            owner: self.owner,
        }
    }

    /// Increments the reference count.
    #[inline]
    pub fn incr_ref_count(&self) {
        debug_assert!(self.is_valid());
        // SAFETY: type invariant -> owner is valid
        unsafe {
            self.owner().incr();
        }
    }

    /// Decrements the reference count.
    #[inline]
    #[must_use]
    pub fn decr_ref_count(self) -> bool {
        debug_assert!(self.is_valid());
        // SAFETY: type invariant -> owner is valid
        unsafe { self.owner().decr() }
    }

    /// Return `true` iff this representation is valid.
    #[inline]
    #[cfg_attr(coverage_nightly, coverage(off))]
    pub fn is_valid(&self) -> bool {
        if !self.owner.check_tag() {
            return false;
        }

        let owner = self.owner();
        if unsafe { !owner.is_valid() } {
            return false;
        }

        let owner = unsafe { owner.as_ref() };
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

        // SAFETY: type invariant -> owner is valid.
        let vec = unsafe { self.owner().as_ref() };
        vec.capacity()
    }

    /// Unwraps the inner vector if it makes any sense.
    #[inline]
    pub fn try_into_vec(self) -> Result<Vec<u8>, Self> {
        debug_assert!(self.is_valid());

        let owner = self.owner();
        let vec = unsafe { owner.as_ref() };
        let ptr = vec.as_ptr();

        if self.ptr != ptr {
            // the starts differ, cannot truncate
            return Err(self);
        }

        let len = self.len();

        // SAFETY: type invariant, the owner is valid
        unsafe {
            if owner.is_unique() {
                let mut owner = owner.unwrap();
                owner.truncate(len);
                Ok(owner)
            } else {
                Err(self)
            }
        }
    }

    /// Returns `true` if there is only one reference to the underlying vector.
    pub fn is_unique(&self) -> bool {
        debug_assert!(self.is_valid());

        // SAFETY: type invariant -> owner is valid
        unsafe { self.owner().is_unique() }
    }

    /// Pushes a slice at the end of the underlying vector.
    ///
    /// # Safety
    ///
    /// The reference must be unique.
    pub unsafe fn push_slice_unchecked(&mut self, addition: &[u8]) {
        debug_assert!(self.is_valid());

        let owner = self.owner();
        let v = unsafe { owner.as_mut() };

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

    /// Returns the remaining spare capacity of the unique vector as a slice of `MaybeUnit<u8>`.
    /// If the vector is actually shared, returns an empty slice.
    ///
    /// The returned slice can be used to fill the vector with data
    /// (e.g. by reading from a file) before marking the data as initialized
    /// using the `set_len` method.
    pub fn spare_capacity_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        debug_assert!(self.is_valid());

        if !self.is_unique() {
            return &mut [];
        }

        let owner = self.owner();
        let v = unsafe { owner.as_mut() };

        // SAFETY: compute the shift from within the vector range (type invariant)
        #[allow(clippy::cast_sign_loss)]
        let start = unsafe { self.ptr.offset_from(v.as_ptr()) as usize };
        v.truncate(start + self.len);
        v.spare_capacity_mut()
    }

    /// Forces the length of the vector to `new_len`.
    ///
    /// # Safety
    ///
    /// * `new_len` should be must be less than or equal to `capacity()`.
    /// * If `new_len` is greater or equal to the current length:
    ///   * The elements at `old_len..new_len` must be initialized.
    ///   * The vector should be uniquely owned, not shared.
    pub unsafe fn set_len(&mut self, new_len: usize) {
        if new_len <= self.len {
            self.len = new_len;
            return;
        }

        debug_assert!(self.is_unique());
        debug_assert!(new_len <= self.capacity());

        let owner = self.owner();
        let v = unsafe { owner.as_mut() };
        // SAFETY: compute the shift from within the vector range (type invariant)
        #[allow(clippy::cast_sign_loss)]
        let start = unsafe { self.ptr.offset_from(v.as_ptr()).abs_diff(0) };
        unsafe { v.set_len(start + new_len) };
        self.len = new_len;
    }

    pub fn shrink_to(&mut self, min_capacity: usize) {
        let min_capacity = min_capacity.max(self.len);

        if self.capacity() <= min_capacity {
            return;
        }

        let mut new_vec = Vec::with_capacity(min_capacity);
        new_vec.extend_from_slice(self.as_slice());
        let old = core::mem::replace(self, Self::new(new_vec));
        let _ignore = old.decr_ref_count();
    }
}

#[cfg(test)]
mod tests {
    use super::Allocated;
    use crate::alloc::vec;
    use crate::Local;

    #[test]
    fn test_alloc() {
        let allocated = Allocated::<Local>::new(vec![]);
        let _ = allocated.decr_ref_count();
    }

    #[test]
    fn test_try_into_vec() {
        let allocated = Allocated::<Local>::new(vec![0, 1, 2]);

        {
            let slice = unsafe { allocated.slice_unchecked(1..2) };

            assert_eq!(unsafe { allocated.owner().ref_count() }, 2);
            assert!(slice.try_into_vec().is_err());
        }

        assert!(!allocated.decr_ref_count());
        assert_eq!(unsafe { allocated.owner().ref_count() }, 1);

        assert!(allocated.try_into_vec().is_ok());
    }
}
