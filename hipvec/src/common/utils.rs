use core::mem;

/// A guard that drops the initialized elements of a slice.
///
/// # Type invariants
///
/// - The pointer `ptr` must be valid for reads and writes of `len` elements of type `T`.
/// - The `initialized` field must always be less than or equal to `len`.
/// - The elements from `ptr` to `ptr.add(initialized)` (excluded) must be initialized.
pub struct SliceWriteGuard<T> {
    ptr: *mut T,
    #[cfg(debug_assertions)]
    len: usize,
    initialized: usize,
}

impl<T> SliceWriteGuard<T> {
    /// Creates a new `SliceWriteGuard` from a raw pointer and a length.
    ///
    /// The length is only stored in debug builds for assertions.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the pointer is valid for writes of `len` elements of type `T`.
    #[inline]
    pub const unsafe fn new(ptr: *mut T, len: usize) -> Self {
        Self {
            ptr,
            #[cfg(debug_assertions)]
            len,
            initialized: 0,
        }
    }

    /// Writes a value to the slice and increments the initialized count.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the number of writes does not exceed the
    /// length of the slice.
    #[inline]
    pub const unsafe fn write(&mut self, value: T) {
        debug_assert!(self.initialized < self.len);

        // SAFETY: valid write by precondition
        unsafe {
            self.ptr.add(self.initialized).write(value);
        }
        self.initialized += 1;
    }

    #[inline]
    pub const fn complete(self) {
        debug_assert!(self.initialized == self.len);
        mem::forget(self);
    }
}

impl<T> Drop for SliceWriteGuard<T> {
    fn drop(&mut self) {
        // SAFETY: valid drop by precondition
        unsafe {
            debug_assert!(self.initialized <= self.len);
            drop_raw_slice(self.ptr, self.initialized);
        }
    }
}

/// Clones a slice of elements from a source pointer to a destination pointer,
/// using a guard to ensure proper dropping of initialized elements on panic.
///
/// # Safety
///
/// The caller must ensure that both pointers are valid for reads and writes
/// of `len` elements of type `T`.
#[inline]
#[track_caller]
pub unsafe fn guarded_slice_clone<T: Clone>(dst: *mut T, src: *const T, len: usize) {
    let mut guard = unsafe { SliceWriteGuard::new(dst, len) };

    for i in 0..len {
        // SAFETY: valid read by precondition
        let item_src = unsafe { &*src.add(i) };
        let item = item_src.clone();

        // SAFETY: valid write by precondition
        unsafe {
            guard.write(item);
        }
    }

    guard.complete();
}

/// Drops a slice of elements given a raw pointer and a length.
///
/// # Safety
///
/// The caller must ensure that the pointer is valid and that the length is correct.
#[inline]
pub unsafe fn drop_raw_slice<T>(ptr: *mut T, len: usize) {
    if mem::needs_drop::<T>() {
        // SAFETY: precondition
        unsafe {
            let slice = core::slice::from_raw_parts_mut(ptr, len);
            core::ptr::drop_in_place(slice);
        }
    }
}
