use core::mem::size_of;
use core::ops::Range;
use core::panic::{RefUnwindSafe, UnwindSafe};

use crate::alloc::vec::Vec;
use crate::Backend;

#[repr(C)]
pub struct Allocated<B: Backend> {
    #[cfg(target_endian = "little")]
    owner: B::RawPointer,

    ptr: *const u8,
    len: usize,

    #[cfg(target_endian = "big")]
    owner: B::RawPointer,
}

impl<B: Backend> Copy for Allocated<B> {}

impl<B: Backend> Clone for Allocated<B> {
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
    const _ASSERTS: () = {
        assert!(size_of::<B::RawPointer>() == size_of::<usize>());
    };

    /// Creates an allocated from a vector.
    ///
    /// Takes ownership of the vector without copying the data.
    #[inline]
    pub fn new(v: Vec<u8>) -> Self {
        let ptr = v.as_ptr();
        let len = v.len();
        let owner = B::into_raw(B::new(v));

        #[allow(clippy::inconsistent_struct_constructor)]
        Self { ptr, len, owner }
    }

    /// Returns the length of this allocated string.
    #[inline]
    pub const fn len(&self) -> usize {
        // debug_assert!(self.is_valid()); // is_valid is not const!

        self.len
    }

    /// Returns as a byte slice.
    #[inline]
    pub const fn as_slice(&self) -> &[u8] {
        // debug_assert!(self.is_valid()); // is_valid is not const!

        // SAFETY: Type invariant
        unsafe { core::slice::from_raw_parts(self.ptr, self.len) }
    }

    /// Returns a mutable slice if possible (unique non-static reference).
    #[inline]
    pub unsafe fn as_mut_slice<'a>(self) -> Option<&'a mut [u8]> {
        debug_assert!(
            self.is_valid(),
            "Inline::as_mut_slice on invalid representation"
        );

        // SAFETY: type invariant, valid owner
        let is_unique = unsafe { B::raw_is_unique(self.owner) };

        if is_unique {
            // SAFETY:
            // * unique -> no one else can "see" the string
            // * type invariant -> valid slice
            Some(unsafe { core::slice::from_raw_parts_mut(self.ptr.cast_mut(), self.len) })
        } else {
            None
        }
    }

    /// Creates a new `Allocated` for some range with the same owner.
    #[inline]
    pub fn slice(&self, range: Range<usize>) -> Self {
        debug_assert!(self.is_valid(), "Inline::slice on invalid representation");

        assert!(range.start <= self.len);
        assert!(range.end <= self.len);
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
        debug_assert!(
            self.is_valid(),
            "Allocated::incr_ref_count on invalid representation"
        );
        // SAFETY: type invariant -> owner is valid
        unsafe { B::raw_increment_count(self.owner) };
    }

    /// Decrements the reference count.
    #[inline]
    pub fn decr_ref_count(self) {
        debug_assert!(
            self.is_valid(),
            "Allocated::decr_ref_count on invalid representation"
        );
        // SAFETY: type invariant -> owner is valid
        unsafe { B::raw_decrement_count(self.owner) };
    }

    /// Return `true` iff this representation is valid.
    #[inline]
    pub fn is_valid(&self) -> bool {
        B::raw_is_valid(self.owner)
    }

    /// Returns a reference to the underlying vector.
    #[inline]
    pub fn owner_vec(&self) -> &Vec<u8> {
        debug_assert!(self.is_valid());

        // SAFETY: type invariant -> owner is valid.
        unsafe { B::raw_as_vec(self.owner) }
    }

    #[inline]
    pub fn try_into_vec(self) -> Result<Vec<u8>, Self> {
        debug_assert!(
            self.is_valid(),
            "Allocated::try_into_vec on invalid representation"
        );

        let ptr = self.owner_vec().as_ptr();
        if self.ptr != ptr {
            // the starts differ, cannot truncate
            return Err(self);
        }
        // SAFETY: type invariant, the owner is valid
        unsafe { B::raw_try_unwrap(self.owner) }
            .map_err(|owner| Self { owner, ..self })
            .map(|mut v| {
                v.truncate(self.len);
                v
            })
    }

    /// Returns `true` if there is only one reference to the underlying vector.
    pub fn is_unique(&self) -> bool {
        debug_assert!(self.is_valid());

        // SAFETY: type invariant -> owner is valid
        unsafe { B::raw_is_unique(self.owner) }
    }

    /// Pushes a slice at the end of the underlying vector.
    ///
    /// # Safety
    ///
    /// The reference must be unique.
    pub unsafe fn push_slice_unchecked(&mut self, addition: &[u8]) {
        let v = unsafe { B::raw_get_mut_unchecked(self.owner) };

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
}

#[cfg(test)]
mod tests {
    use super::Allocated;
    use crate::alloc::vec;
    use crate::Local;

    #[test]
    fn test_clone() {
        let allocated = Allocated::<Local>::new(vec![]);
        let _clone = allocated.clone();
        let local = unsafe { Local::from_raw(allocated.owner) };
        let count = Local::strong_count(&local);
        let _ = Local::into_raw(local);
        assert_eq!(count, 1);
        allocated.decr_ref_count();
    }

    #[test]
    fn test_try_into_vec() {
        let allocated = Allocated::<Local>::new(vec![0, 1, 2]);

        {
            let slice = allocated.slice(1..2);
            assert!(slice.try_into_vec().is_err());
        }
        allocated.decr_ref_count();

        assert!(allocated.try_into_vec().is_ok());
    }
}
