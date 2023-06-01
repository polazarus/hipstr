use std::{panic::{UnwindSafe, RefUnwindSafe}, mem::size_of, ops::Range};

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
        unsafe { std::slice::from_raw_parts(self.ptr, self.len) }
    }

    /// Returns a mutable slice if possible (unique non-static reference).
    #[inline]
    pub fn as_mut_slice(&mut self) -> Option<&mut [u8]> {
        debug_assert!(
            self.is_valid(),
            "Inline::as_mut_slice on invalid representation"
        );

        // SAFETY: if this reference is unique, no one else can "see" the string
        if unsafe { B::raw_is_unique(self.owner) } {
            Some(unsafe { std::slice::from_raw_parts_mut(self.ptr as *mut u8, self.len) })
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
        unsafe { B::raw_increment_count(self.owner) };
    }

    /// Decrements the reference count.
    #[inline]
    pub fn decr_ref_count(self) {
        debug_assert!(
            self.is_valid(),
            "Allocated::decr_ref_count on invalid representation"
        );
        unsafe { B::raw_decrement_count(self.owner) };
    }

    /// Return `true` iff this representation is valid.
    #[inline]
    pub fn is_valid(&self) -> bool {
        B::raw_is_valid(self.owner)
    }

    #[inline]
    pub fn owner_vec(&self) -> &Vec<u8> {
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
        unsafe { B::raw_try_unwrap(self.owner) }
            .map_err(|owner| Self { owner, ..self })
            .map(|mut v| {
                v.truncate(self.len);
                v
            })
    }
}