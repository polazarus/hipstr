//! Internal representation of thin vectors.

use core::cmp;
use core::ptr::{self, NonNull};

use const_default::ConstDefault;

use super::{TryReserveError, TryReserveErrorKind, unwrap_or_oom};
use crate::backend::InitPrefix;
pub use crate::common::header::ThinHeader as Header;
use crate::common::tagged_pointer::TaggedPointer;
use crate::common::utils::drop_raw_slice;

/// Tag for the tagged pointer in `Base`.
///
/// This tag is chosen to be `0b10` to avoid conflicts with the null pointer, to
/// be distinct from the inline tag (0b1), while ensuring even a null pointer is
/// actually non-zero and as such providing a useful niche for Rust layout
/// optimisations.
const TAG: usize = 0b10;

/// Returns the minimum non-zero capacity for a given element size.
///
/// The implementation is purely heuristic based on the following observations:
/// - for small element sizes, the header is relatively large compared to the
///   elements, so we need a larger minimum capacity to avoid wasting too much
///   memory
/// - for larger element sizes, the header is relatively smaller, so we can
///   afford a smaller minimum capacity.
const fn min_non_zero_cap(size: usize) -> usize {
    if size == 1 {
        // the header is 3 machine words, let's round up the allocation to 4 machine words
        // efficient if the allocator rounds up to powers of two, and still small enough to avoid wasting too much memory
        size_of::<usize>()
    } else if size <= 1024 {
        // for larger element sizes, the header is relatively smaller, so we can
        // afford to have a smaller minimum capacity
        size_of::<usize>() / 2
    } else {
        // for very large element sizes, the header is negligible, so we can allow a minimum capacity of 1
        1
    }
}

/// Internal representation of a thin vector.
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
    /// Returns a reference to the header if the pointer is non-null, or `None`
    /// if the pointer is null, that is, if the vector is empty.
    #[inline]
    const fn header(&self) -> Option<&Header<T, P>> {
        if let Some(header) = self.0.as_non_null() {
            unsafe { Some(header.as_ref()) }
        } else {
            None
        }
    }

    /// Returns a mutable reference to the header if the pointer is non-null, or `None`
    /// if the pointer is null, that is, if the vector is empty.
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

    /// Returns a new empty thin vector, with no actual allocation, that is, the
    /// underlying pointer is null.
    #[inline]
    pub const fn new() -> Self {
        const { Self(TaggedPointer::null()) }
    }

    /// Returns a new thin vector with the given capacity, that is, with an actual allocation if the capacity is non-zero.
    #[inline]
    pub const fn len(&self) -> usize {
        if let Some(header) = self.header() {
            header.len
        } else {
            0
        }
    }

    /// Returns `true` if the vector is empty, that is, if its length is zero.
    #[inline]
    pub const fn is_empty(&self) -> bool {
        // one cannot simply check if the pointer is null to determine if the
        // vector is empty, because an empty vector can still have a non-null
        // pointer if it has a non-zero capacity, so actually need to check the
        // length instead
        self.len() == 0
    }

    /// Sets the length of the vector.
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

    /// Returns the capacity of the vector, that is, the maximum number of elements it can hold without reallocating.
    #[inline]
    pub const fn capacity(&self) -> usize {
        if let Some(header) = self.header() {
            header.cap
        } else {
            0
        }
    }

    /// Returns a pointer to the data, that is, the first element of the vector,
    /// or a dangling pointer if the vector is empty.
    ///
    /// Note that the pointer is guaranteed to be non-null.
    #[inline]
    pub const fn as_ptr(&self) -> *const T {
        if let Some(header) = self.0.as_non_null() {
            unsafe { Header::data(header).as_ptr().cast_const() }
        } else {
            ptr::dangling()
        }
    }

    /// Returns a mutable pointer to the data, that is, the first element of the vector,
    /// or a dangling pointer if the vector is empty.
    ///
    /// Note that the pointer is guaranteed to be non-null.
    #[inline]
    pub const fn as_mut_ptr(&mut self) -> *mut T {
        if let Some(header) = self.0.as_non_null() {
            unsafe { Header::data(header).as_ptr() }
        } else {
            ptr::dangling_mut()
        }
    }

    /// Returns a non-null pointer to the data, that is, the first element of
    /// the vector, or a dangling pointer if the vector is empty.
    #[inline]
    #[expect(clippy::needless_pass_by_ref_mut)]
    pub const fn as_non_null(&mut self) -> NonNull<T> {
        if let Some(header) = self.0.as_non_null() {
            unsafe { Header::data(header) }
        } else {
            NonNull::dangling()
        }
    }

    /// Returns a slice of the initialized elements in the vector.
    #[inline]
    pub const fn as_slice(&self) -> &[T] {
        unsafe { core::slice::from_raw_parts(self.as_ptr(), self.len()) }
    }

    /// Returns a mutable slice of the initialized elements in the vector.
    #[inline]
    pub const fn as_mut_slice(&mut self) -> &mut [T] {
        unsafe { core::slice::from_raw_parts_mut(self.as_mut_ptr(), self.len()) }
    }

    /// Drops the allocation if it exists.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the vector is not used after this method is called, and that the
    /// allocation is not dropped elsewhere, to avoid double free or use after free.
    #[inline]
    pub unsafe fn drop_container(&mut self) {
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

        // reset the pointer for safety, should be removed by the compiler
        *self = Self::new();
    }
}

impl<T, P> Base<T, P>
where
    P: InitPrefix,
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

    /// Copies `slice` into a new allocation (none when empty).
    pub fn from_slice_copy(slice: &[T]) -> Self
    where
        T: Copy,
        P: InitPrefix,
    {
        let mut this = unwrap_or_oom(Self::try_with_capacity(slice.len()));
        if !slice.is_empty() {
            // SAFETY: room for `slice.len()` elements, copyable elements, and
            // the fresh allocation cannot overlap `slice`
            unsafe {
                this.as_mut_ptr()
                    .copy_from_nonoverlapping(slice.as_ptr(), slice.len());
                this.set_len(slice.len());
            }
        }
        this
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
