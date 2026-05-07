//! Internal representation of thin vectors.

use core::ptr::{self, NonNull};
use core::{cmp, fmt};

use const_default::ConstDefault;

use super::{TryReserveError, TryReserveErrorKind, unwrap_or_oom};
pub use crate::common::header::ThinHeader as Header;
use crate::common::methods;
use crate::common::tagged_pointer::TaggedPointer;
use crate::common::utils::drop_raw_slice;
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
pub struct Base<T, P>(pub(crate) TaggedPointer<Header<T, P>, TAG>);

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
    #[expect(
        clippy::needless_pass_by_ref_mut,
        reason = "type invariant requires mutable access to get mutable reference to header"
    )]
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
    #[cfg_attr(debug_assertions, track_caller)]
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
    #[expect(clippy::needless_pass_by_ref_mut)]
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

    pub const fn pop(&mut self) -> Option<T> {
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
    pub unsafe fn drop_copy(&mut self) {
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

    /// Drops the elements and the allocation if it exists.
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
            // SAFETY: type invariant says the slice is valid
            unsafe {
                let data_ptr = Header::data(header).as_ptr();
                drop_raw_slice(data_ptr, header.as_ref().len);
                // header.as_mut().len = 0;
            }

            // SAFETY: type invariant says the allocated pointer is valid and properly aligned, and the layout is correct
            unsafe {
                alloc::alloc::dealloc(header.as_ptr().cast(), layout);
            }
        }
    }

    pub fn with_fresh_prefix<P2>(mut self) -> Base<T, P2>
    where
        P2: ConstDefault,
    {
        if let Some(header) = self.0.as_non_null() {
            if size_of::<P>() == size_of::<P2>() && align_of::<P>() == align_of::<P2>() {
                let prefix = unsafe { &raw mut (*header.as_ptr()).prefix };
                let prefix: *mut P2 = prefix.cast();
                unsafe {
                    prefix.write(P2::DEFAULT);
                }
                Base(self.0.cast())
            } else {
                let len = self.len();
                let mut base: Base<T, P2> = Base::with_capacity(len);
                methods::append!(&mut base, &mut self);
                base
            }
        } else {
            Base::new()
        }
    }
}

impl<T, P> Base<T, P>
where
    P: ConstDefault,
{
    pub fn with_capacity(capacity: usize) -> Self {
        unwrap_or_oom(Self::try_with_capacity(capacity))
    }

    pub fn try_with_capacity(capacity: usize) -> Result<Self, TryReserveError> {
        if capacity == 0 {
            return Ok(Self::new());
        }

        let Some((layout, capacity)) = Header::<T, P>::layout(capacity) else {
            return Err(TryReserveError(TryReserveErrorKind::CapacityOverflow));
        };

        let ptr = unsafe { alloc::alloc::alloc(layout) };
        let Some(ptr) = NonNull::new(ptr) else {
            return Err(TryReserveError(TryReserveErrorKind::AllocError { layout }));
        };
        let header_ptr = ptr.cast::<Header<T, P>>();
        unsafe {
            header_ptr.write(Header::with_capacity(capacity));
        }

        Ok(Self(header_ptr.into()))
    }

    const MIN_CAPACITY: usize = const { min_non_zero_cap(size_of::<T>()) };

    pub fn reserve(&mut self, additional: usize) {
        unwrap_or_oom(self.try_reserve(additional));
    }

    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        let old_cap = self.capacity();
        let len = self.len();

        // Compute the required capacity, checking for overflow.
        let req_cap = len
            .checked_add(additional)
            .ok_or(TryReserveError(TryReserveErrorKind::CapacityOverflow))?;

        if req_cap > old_cap {
            // Exponential growth to avoid frequent reallocations.
            // The doubling cannot overflow because the old cap is less than isize::MAX
            let floor_cap = cmp::max(old_cap * 2, Self::MIN_CAPACITY);

            let new_cap = cmp::max(req_cap, floor_cap);
            unsafe {
                self.try_realloc(new_cap)?;
            }
        }
        Ok(())
    }

    pub fn reserve_exact(&mut self, additional: usize) {
        unwrap_or_oom(self.try_reserve_exact(additional));
    }

    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), TryReserveError> {
        let old_cap = self.capacity();
        let len = self.len();
        let req_cap = len
            .checked_add(additional)
            .ok_or(TryReserveError(TryReserveErrorKind::CapacityOverflow))?;
        if req_cap > old_cap {
            unsafe {
                self.try_realloc(req_cap)?;
            }
        }
        Ok(())
    }

    pub unsafe fn try_realloc(&mut self, new_cap: usize) -> Result<(), TryReserveError> {
        if new_cap == 0 {
            *self = Self::new();
            return Ok(());
        }

        let old_cap = self.capacity();
        let old_layout = Header::<T, P>::layout(old_cap)
            .ok_or(TryReserveError(TryReserveErrorKind::CapacityOverflow))?
            .0;
        let (new_layout, new_cap) = Header::<T, P>::layout(new_cap)
            .ok_or(TryReserveError(TryReserveErrorKind::CapacityOverflow))?;

        if new_cap != old_cap {
            if let Some(ptr) = self.0.as_non_null() {
                let ptr: *mut Header<T, P> = unsafe {
                    alloc::alloc::realloc(ptr.as_ptr().cast(), old_layout, new_layout.size()).cast()
                };
                let Some(mut ptr) = NonNull::new(ptr) else {
                    return Err(TryReserveError(TryReserveErrorKind::AllocError {
                        layout: new_layout,
                    }));
                };
                unsafe {
                    ptr.as_mut().cap = new_cap;
                }
                self.0 = ptr.into(); // transform the pointer back into a tagged pointer
            } else {
                *self = Self::with_capacity(new_cap);
            }
        }
        Ok(())
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

    pub fn from_array<const N: usize>(array: [T; N]) -> Self {
        methods::from_array!(array)
    }

    pub fn from_slice(slice: &[T]) -> Self
    where
        T: Clone,
    {
        methods::from_slice!(slice)
    }

    pub fn from_slice_copy(slice: &[T]) -> Self
    where
        T: Copy,
    {
        methods::from_slice_copy!(slice)
    }

    pub fn extend_from_array<const N: usize>(&mut self, array: [T; N]) {
        methods::extend_from_array!(self, array);
    }

    #[track_caller]
    pub fn split_off(&mut self, at: usize) -> Self {
        methods::split_off!(self, at)
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

#[repr(transparent)]
pub struct Reserved(#[allow(unused)] usize);

impl Default for Reserved {
    fn default() -> Self {
        Self::DEFAULT
    }
}

impl ConstDefault for Reserved {
    const DEFAULT: Self = Self(0);
}

impl fmt::Debug for Reserved {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Reserved")
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
