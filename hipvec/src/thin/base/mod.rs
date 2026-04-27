//! Internal representation of thin vectors.

use core::cmp;
use core::ptr::{self, NonNull};

use const_default::ConstDefault;

pub use crate::common::header::ThinHeader as Header;
use crate::common::methods;
use crate::common::tagged_pointer::TaggedPointer;
use crate::traits::MutableVector;

const TAG: usize = 0b10;

const fn min_non_zero_cap(size: usize) -> usize {
    if size == 1 {
        8
    } else if size <= 1024 {
        4
    } else {
        1
    }
}

#[derive(Debug)]
#[repr(transparent)]
pub struct Base<T, P>(TaggedPointer<Header<T, P>, TAG>);

impl<T, P> Default for Base<T, P> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T, P> ConstDefault for Base<T, P> {
    const DEFAULT: Self = Self::new();
}

impl<T, P> Base<T, P> {
    #[inline]
    const fn header(&self) -> Option<&Header<T, P>> {
        if let Some(header) = self.0.as_non_null() {
            unsafe { Some(header.as_ref()) }
        } else {
            None
        }
    }

    #[inline]
    const fn header_mut(&mut self) -> Option<&mut Header<T, P>> {
        if let Some(mut header) = self.0.as_non_null() {
            unsafe { Some(header.as_mut()) }
        } else {
            None
        }
    }

    #[inline]
    pub const fn new() -> Self {
        const { Self(TaggedPointer::null()) }
    }

    #[inline]
    pub const fn len(&self) -> usize {
        if let Some(header) = self.header() {
            header.len
        } else {
            0
        }
    }

    /// Sets the length
    ///
    /// # Safety
    ///
    /// The caller must ensure that `len` does not exceed the current capacity and that the new
    /// elements are properly initialized.
    pub const unsafe fn set_len(&mut self, len: usize) {
        if let Some(header) = self.header_mut() {
            assert!(len <= header.cap, "length exceeds capacity");
            header.len = len;
        } else if len != 0 {
            panic!("length overflow");
        }
    }

    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    pub const fn capacity(&self) -> usize {
        if let Some(header) = self.header() {
            header.cap
        } else {
            0
        }
    }

    #[inline]
    pub const fn as_ptr(&self) -> *const T {
        if let Some(header) = self.0.as_non_null() {
            unsafe { Header::data(header).as_ptr().cast_const() }
        } else {
            ptr::dangling()
        }
    }

    #[inline]
    pub const fn as_mut_ptr(&mut self) -> *mut T {
        if let Some(header) = self.0.as_non_null() {
            unsafe { Header::data(header).as_ptr() }
        } else {
            ptr::dangling_mut()
        }
    }

    #[inline]
    pub const fn as_non_null(&mut self) -> NonNull<T> {
        if let Some(header) = self.0.as_non_null() {
            unsafe { Header::data(header) }
        } else {
            NonNull::dangling()
        }
    }
    #[inline]
    pub const fn as_slice(&self) -> &[T] {
        unsafe { core::slice::from_raw_parts(self.as_ptr(), self.len()) }
    }

    #[inline]
    pub const fn as_mut_slice(&mut self) -> &mut [T] {
        unsafe { core::slice::from_raw_parts_mut(self.as_mut_ptr(), self.len()) }
    }

    #[inline]
    pub const fn spare_capacity_mut(&mut self) -> &mut [core::mem::MaybeUninit<T>] {
        methods::spare_capacity_mut!(self)
    }

    pub fn pop(&mut self) -> Option<T> {
        methods::pop!(self)
    }

    pub fn pop_if(&mut self, predicate: impl FnOnce(&mut T) -> bool) -> Option<T> {
        methods::pop_if!(self, predicate)
    }

    pub fn remove(&mut self, index: usize) -> T {
        methods::remove!(self, index)
    }

    pub fn swap_remove(&mut self, index: usize) -> T {
        methods::swap_remove!(self, index)
    }

    pub fn truncate(&mut self, new_len: usize) {
        methods::truncate!(self, new_len);
    }

    #[inline]
    pub fn clear(&mut self) {
        self.truncate(0);
    }

    pub const fn truncate_copy(&mut self, new_len: usize)
    where
        T: Copy,
    {
        methods::truncate_copy!(self, new_len);
    }

    #[inline]
    pub const fn clear_copy(&mut self)
    where
        T: Copy,
    {
        self.truncate_copy(0);
    }

    pub fn append(&mut self, other: &mut impl MutableVector<Item = T>)
    where
        P: ConstDefault,
    {
        methods::append!(self, other);
    }

    pub const fn prefix(&self) -> Option<&P> {
        if let Some(header) = self.header() {
            Some(&header.prefix)
        } else {
            None
        }
    }

    /// Creates a bitwise copy of the vector handle.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the original and the copy may be used simultaneously without
    /// violating Rust's aliasing rules.
    pub const unsafe fn copy(&self) -> Self {
        Self(self.0)
    }

    /// Drops the allocation if it exists.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the vector is not used after this method is called, and that the
    /// allocation is not dropped elsewhere, to avoid double free or use after free.
    #[inline]
    pub unsafe fn drop(&mut self) {
        if let Some(header) = self.0.as_non_null()
            && let Some((layout, _)) = Header::<T, P>::layout(unsafe { header.as_ref().cap })
        {
            // SAFETY: type invariant says the pointer is valid and properly aligned, and the layout is correct
            unsafe {
                alloc::alloc::dealloc(header.as_ptr().cast(), layout);
            }
        }
        // ignore two cases:
        // - the pointer is null, as it represents an empty vector with no allocated memory
        // - the layout is invalid, as it can only occur if the capacity is corrupted, in
        //   which case there's not much we can do anyway

        // reset the pointer for safety, should be removed by the compiler
        *self = Self::new();
    }
}

impl<T, P> Base<T, P>
where
    P: ConstDefault,
{
    pub fn with_capacity(capacity: usize) -> Self {
        if capacity == 0 {
            return Self::new();
        }

        let Some((layout, capacity)) = Header::<T, P>::layout(capacity) else {
            panic!("capacity overflow");
        };

        let ptr = unsafe { alloc::alloc::alloc(layout) };
        let Some(ptr) = NonNull::new(ptr) else {
            alloc::alloc::handle_alloc_error(layout);
        };
        let header_ptr = ptr.cast::<Header<T, P>>();
        unsafe {
            header_ptr.write(Header::with_capacity(capacity));
        }

        Self(header_ptr.into())
    }

    const MIN_CAPACITY: usize = const { min_non_zero_cap(size_of::<T>()) };

    pub fn reserve(&mut self, additional: usize) {
        let old_cap = self.capacity();
        let len = self.len();

        // Compute the required capacity, checking for overflow.
        let req_cap = len.checked_add(additional).expect("capacity overflow");

        if req_cap > old_cap {
            // Exponential growth to avoid frequent reallocations.
            // The doubling cannot overflow because the old cap is less than isize::MAX
            let floor_cap = cmp::max(old_cap * 2, Self::MIN_CAPACITY);

            let new_cap = cmp::max(req_cap, floor_cap);
            unsafe {
                self.set_capacity(new_cap);
            }
        }
    }

    pub fn reserve_exact(&mut self, additional: usize) {
        let old_cap = self.capacity();
        let len = self.len();
        let req_cap = len.checked_add(additional).expect("capacity overflow");
        if req_cap > old_cap {
            unsafe {
                self.set_capacity(req_cap);
            }
        }
    }

    pub unsafe fn set_capacity(&mut self, new_cap: usize) {
        if new_cap == 0 {
            *self = Self::new();
            return;
        }

        let old_cap = self.capacity();
        let old_layout = Header::<T, P>::layout(old_cap)
            .expect("capacity overflow")
            .0;
        let (new_layout, new_cap) = Header::<T, P>::layout(new_cap).expect("capacity overflow");

        if new_cap != old_cap {
            if let Some(ptr) = self.0.as_non_null() {
                let ptr: *mut Header<T, P> = unsafe {
                    alloc::alloc::realloc(ptr.as_ptr().cast(), old_layout, new_layout.size()).cast()
                };
                let Some(mut ptr) = NonNull::new(ptr) else {
                    alloc::alloc::handle_alloc_error(new_layout);
                };
                unsafe {
                    ptr.as_mut().cap = new_cap;
                }
                self.0 = ptr.into(); // transform the pointer back into a tagged pointer
            } else {
                *self = Self::with_capacity(new_cap);
            }
        }
    }

    #[inline]
    pub fn push(&mut self, value: T) {
        let _ = self.push_mut(value);
    }

    pub fn push_mut(&mut self, value: T) -> &mut T {
        methods::push_mut!(self, value)
    }

    pub fn push_within_capacity(&mut self, value: T) -> Result<&mut T, T> {
        methods::push_within_capacity!(self, value)
    }

    pub fn insert(&mut self, index: usize, value: T) {
        let _ = self.insert_mut(index, value);
    }

    pub fn insert_mut(&mut self, index: usize, value: T) -> &mut T {
        methods::insert_mut!(self, index, value)
    }

    pub fn extend_from_array<const N: usize>(&mut self, array: [T; N]) {
        methods::extend_from_array!(self, array);
    }

    pub fn resize(&mut self, new_len: usize, value: T)
    where
        T: Clone,
    {
        methods::resize!(self, new_len, value);
    }

    pub fn resize_copy(&mut self, new_len: usize, value: T)
    where
        T: Copy,
    {
        methods::resize_copy!(self, new_len, value);
    }

    pub fn resize_with(&mut self, new_len: usize, f: impl FnMut() -> T) {
        methods::resize_with!(self, new_len, f);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new() {
        TaggedPointer::<Header<u8, ()>, TAG>::debug_check();
        let repr: Base<u8, ()> = Base::new();
        assert_eq!(repr.len(), 0);
        assert_eq!(repr.capacity(), 0);
        assert_eq!(repr.as_ptr(), ptr::dangling());
    }
}
