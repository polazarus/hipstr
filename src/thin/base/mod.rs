//! Internal representation of thin vectors.

use core::cmp;
use core::ptr::{self, NonNull};

use const_default::ConstDefault;

use super::{TryReserveError, TryReserveErrorKind, unwrap_or_oom};
use crate::backend::InitPrefix;
pub use crate::common::header::ThinHeader as Header;
use crate::common::tagged_pointer::TaggedPointer;

/// Tag for the tagged pointer in `Base`.
///
/// This tag is chosen to be `0b10` to avoid conflicts with the null pointer, to
/// be distinct from the inline tag (0b1), while ensuring even a null pointer is
/// actually non-zero and as such providing a useful niche for Rust layout
/// optimisations.
const TAG: usize = 0b10;

/// Minimal non-zero capacity: one word of bytes, so that the smallest
/// allocation is 4 words with the 3-word header (allocators round up to
/// powers of two).
const MIN_CAPACITY: usize = size_of::<usize>();

/// A thin heap byte buffer: one allocation, the header then the bytes.
#[repr(transparent)]
pub struct Base<P>(pub(crate) TaggedPointer<Header<P>, TAG>);

impl<P> ConstDefault for Base<P> {
    const DEFAULT: Self = Self::new();
}

impl<P> Base<P> {
    /// Returns a reference to the header if the pointer is non-null, or `None`
    /// if the pointer is null, that is, if the vector is empty.
    #[inline]
    const fn header(&self) -> Option<&Header<P>> {
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
    const fn header_mut(&mut self) -> Option<&mut Header<P>> {
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
        Self(TaggedPointer::NULL)
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
    pub const fn as_ptr(&self) -> *const u8 {
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
    pub const fn as_mut_ptr(&mut self) -> *mut u8 {
        if let Some(header) = self.0.as_non_null() {
            unsafe { Header::data(header).as_ptr() }
        } else {
            ptr::dangling_mut()
        }
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
            && let Some((layout, _)) = Header::<P>::layout(unsafe { header.as_ref().cap })
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

impl<P> Base<P>
where
    P: InitPrefix,
{
    pub fn try_with_capacity(capacity: usize) -> Result<Self, TryReserveError> {
        if capacity == 0 {
            return Ok(Self::new());
        }

        let Some((layout, capacity)) = Header::<P>::layout(capacity) else {
            return Err(TryReserveError(TryReserveErrorKind::CapacityOverflow));
        };

        let ptr = unsafe { alloc::alloc::alloc(layout) };
        let Some(ptr) = NonNull::new(ptr) else {
            return Err(TryReserveError(TryReserveErrorKind::AllocError { layout }));
        };
        let header_ptr = ptr.cast::<Header<P>>();
        unsafe {
            header_ptr.write(Header::with_capacity(capacity));
        }

        Ok(Self(header_ptr.into()))
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
            let floor_cap = cmp::max(old_cap * 2, MIN_CAPACITY);

            let new_cap = cmp::max(req_cap, floor_cap);
            unsafe {
                self.try_realloc(new_cap)?;
            }
        }
        Ok(())
    }

    pub unsafe fn try_realloc(&mut self, new_cap: usize) -> Result<(), TryReserveError> {
        if new_cap == 0 {
            // SAFETY: replaced right away
            unsafe { self.drop_container() };
            return Ok(());
        }

        let old_cap = self.capacity();
        // SAFETY: the current capacity came from a valid layout
        let old_layout = unsafe { Header::<P>::layout(old_cap).unwrap_unchecked() }.0;
        let (new_layout, new_cap) = Header::<P>::layout(new_cap)
            .ok_or(TryReserveError(TryReserveErrorKind::CapacityOverflow))?;

        if new_cap != old_cap {
            if let Some(ptr) = self.0.as_non_null() {
                let ptr: *mut Header<P> = unsafe {
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
                *self = Self::try_with_capacity(new_cap)?;
            }
        }
        Ok(())
    }

    /// Copies `slice` into a new allocation (none when empty).
    pub fn from_slice_copy(slice: &[u8]) -> Self
    where
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
        TaggedPointer::<Header<()>, TAG>::debug_check();
        let repr: Base<()> = Base::new();
        assert_eq!(repr.len(), 0);
        assert_eq!(repr.capacity(), 0);
        assert_eq!(repr.as_ptr(), ptr::dangling());
    }

    type B = Base<crate::backend::Count>;

    #[test]
    fn null_and_allocated() {
        let mut b = B::try_with_capacity(0).unwrap();
        assert_eq!(b.capacity(), 0);
        assert_eq!(b.as_mut_ptr(), ptr::dangling_mut());
        // SAFETY: zero length on null
        unsafe { b.set_len(0) };
        // growing from null allocates
        b.try_reserve(3).unwrap();
        assert!(b.capacity() >= MIN_CAPACITY);
        assert_eq!(b.as_ptr(), b.as_mut_ptr().cast_const());
        // SAFETY: zero is in bounds
        unsafe { b.set_len(0) };
        // shrinking to zero frees
        // SAFETY: no elements
        unsafe { b.try_realloc(0).unwrap() };
        assert_eq!(b.capacity(), 0);
        let mut b = B::from_slice_copy(b"abc");
        assert_eq!(b.len(), 3);
        // SAFETY: not used afterwards
        unsafe { b.drop_container() };
    }

    #[test]
    fn edges() {
        // freeing nothing
        let mut b = B::new();
        // SAFETY: not used afterwards
        unsafe { b.drop_container() };
        // empty copy: no allocation
        assert_eq!(B::from_slice_copy(b"").capacity(), 0);
        let mut b = B::try_with_capacity(16).unwrap();
        let cap = b.capacity();
        // enough room already
        b.try_reserve(cap).unwrap();
        // same capacity
        // SAFETY: no elements
        unsafe { b.try_realloc(cap).unwrap() };
        assert_eq!(b.capacity(), cap);
        // overflowing length
        // SAFETY: zeroed, in bounds
        unsafe { b.set_len(1) };
        assert!(b.try_reserve(usize::MAX).is_err());
        // SAFETY: not used afterwards
        unsafe { b.drop_container() };
    }

    #[test]
    #[should_panic(expected = "length overflow")]
    fn set_len_on_null() {
        // SAFETY: checked
        unsafe { B::new().set_len(1) };
    }
}
