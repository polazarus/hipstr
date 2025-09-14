//! Common functions and types.

use alloc::alloc::handle_alloc_error;
use alloc::vec::Vec;
use core::alloc::Layout;
use core::mem::{self, ManuallyDrop, MaybeUninit};
use core::ops::{Bound, Range, RangeBounds};
use core::ptr::NonNull;
use core::{error, fmt};

use rules_derive::rules_derive;

pub mod boo;
pub(crate) mod derives;
pub mod drain;
pub mod into_iter;
pub(crate) mod methods;
pub(crate) mod non_zero;
#[cfg(test)]
mod tests;
pub mod traits;

/// A `usize`-sized zero.
#[repr(usize)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[rules_derive(derives::ConstDefault(Self::Zero))]
pub enum ZeroUsize {
    Zero = 0,
}

/// Panics with the provided displayable error message.
///
/// # Panics
///
/// Always panics with the provided error message.
#[track_caller]
pub(crate) fn panic_display<T>(e: impl fmt::Display) -> T {
    panic!("{e}");
}

/// Converts any generic range into a concrete `Range<usize>` given a length.
///
/// # Errors
///
/// Returns a `RangeError` if the range is invalid.
pub fn range(range: impl RangeBounds<usize>, len: usize) -> Result<Range<usize>, RangeError> {
    range_mono(
        range.start_bound().cloned(),
        range.end_bound().cloned(),
        len,
    )
}

/// Converts start and end bounds to a concrete `Range<usize>` given a length.
///
/// # Errors
///
/// Returns a `RangeError` if the range is invalid.
fn range_mono(
    start: Bound<usize>,
    end: Bound<usize>,
    len: usize,
) -> Result<Range<usize>, RangeError> {
    let start = match start {
        Bound::Included(start) => start,
        Bound::Excluded(start) => start.checked_add(1).ok_or(RangeError::StartOverflows)?,
        Bound::Unbounded => 0,
    };
    let end = match end {
        Bound::Included(end) => end.checked_add(1).ok_or(RangeError::EndOverflows)?,
        Bound::Excluded(end) => end,
        Bound::Unbounded => len,
    };
    if start > end {
        Err(RangeError::StartGreaterThanEnd { start, end })
    } else if end > len {
        Err(RangeError::EndOutOfBounds { end, len })
    } else {
        Ok(Range { start, end })
    }
}

/// Represents errors that can occur when creating a range.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum RangeError {
    /// The start index overflows.
    StartOverflows,
    /// The end index overflows.
    EndOverflows,
    /// The start index is greater than the end index.
    StartGreaterThanEnd { start: usize, end: usize },
    /// The end index is out of bounds.
    EndOutOfBounds { end: usize, len: usize },
}

impl RangeError {
    /// Returns a static message describing the error.
    #[must_use]
    pub const fn const_message(&self) -> &'static str {
        match self {
            Self::StartOverflows => "start index overflows",
            Self::EndOverflows => "end index overflows",
            Self::StartGreaterThanEnd { .. } => "start index is greater than end index",
            Self::EndOutOfBounds { .. } => "end index is out of bounds",
        }
    }
}

impl error::Error for RangeError {}

impl fmt::Display for RangeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::StartOverflows => write!(f, "start index overflows"),
            Self::EndOverflows => write!(f, "end index overflows"),
            Self::StartGreaterThanEnd { start, end } => {
                write!(f, "start index {start} is greater than end index {end}")
            }
            Self::EndOutOfBounds { end, len } => {
                write!(
                    f,
                    "end index {end} is out of bounds for slice of length {len}",
                )
            }
        }
    }
}

/// Converts a `ManuallyDrop<T>` reference to a `T` reference in a `const` context.
///
/// # Safety
///
/// This function is safe because `ManuallyDrop<T>` is a transparent wrapper of `T`.
#[inline]
pub(crate) const fn manually_drop_as_ref<T>(m: &ManuallyDrop<T>) -> &T {
    // SAFETY: `ManuallyDrop<T>` is a transparent wrapper of `T`.
    unsafe { core::mem::transmute::<&ManuallyDrop<T>, &T>(m) }
}

/// Copies a `T` slice to a `ManuallyDrop<T>` slice.
pub(crate) const fn maybe_uninit_write_copy_of_slice<T>(dst: &mut [MaybeUninit<T>], src: &[T])
where
    T: Copy,
{
    let len = src.len();
    assert!(
        len == dst.len(),
        "source slice length does not match destination slice length"
    );
    unsafe {
        dst.as_mut_ptr().copy_from(src.as_ptr().cast(), len);
    }
}

/// Converts a `ManuallyDrop<T>` mutable reference to a `T` mutable reference in a `const` context.
///
/// # Safety
///
/// This function is safe because `ManuallyDrop<T>` is a transparent wrapper of `T`.
#[inline]
pub(crate) const fn manually_drop_as_mut<T>(m: &mut ManuallyDrop<T>) -> &mut T {
    // SAFETY: `ManuallyDrop<T>` is a transparent wrapper of `T`.
    unsafe { core::mem::transmute::<&mut ManuallyDrop<T>, &mut T>(m) }
}

/// A guard that drops the initialized elements of a slice.
pub(crate) struct SliceWriteGuard<T> {
    ptr: *mut T,
    #[cfg(debug_assertions)]
    len: usize,
    initialized: usize,
}

impl<T> SliceWriteGuard<T> {
    /// Creates a new `SliceWriteGuard` from a raw pointer and a length.
    ///
    /// The length is only stored in debug builds for assertions.
    #[inline]
    pub const fn new(ptr: *mut T, len: usize) -> Self {
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
        unsafe {
            debug_assert!(self.initialized <= self.len);
            drop_raw_slice(self.ptr, self.initialized);
        }
    }
}

#[inline]
#[track_caller]
pub(crate) unsafe fn guarded_slice_clone<T: Clone>(dst: *mut T, src: *const T, len: usize) {
    let mut guard = SliceWriteGuard::new(dst, len);

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

#[inline]
#[cfg_attr(coverage_nightly, coverage(off))]
pub(crate) fn check_alloc(ptr: *mut u8, layout: Layout) -> NonNull<u8> {
    let Some(ptr) = NonNull::new(ptr) else {
        handle_alloc_error(layout);
    };
    ptr
}

/// Drops a slice of elements given a raw pointer and a length.
///
/// # Safety
///
/// The caller must ensure that the pointer is valid and that the length is correct.
#[inline]
pub(crate) unsafe fn drop_raw_slice<T>(ptr: *mut T, len: usize) {
    if mem::needs_drop::<T>() {
        // SAFETY: precondition
        unsafe {
            let slice = core::slice::from_raw_parts_mut(ptr, len);
            core::ptr::drop_in_place(slice);
        }
    }
}

/// [`Vec::push_within_capacity`] stable implementation.
pub(crate) fn vec_push_within_capacity<T>(v: &mut Vec<T>, value: T) -> Result<(), T> {
    let spare = v.spare_capacity_mut();
    if let [e, ..] = spare {
        e.write(value);
        // SAFETY: we just initialized one more element.
        unsafe {
            v.set_len(v.len() + 1);
        }
        Ok(())
    } else {
        Err(value)
    }
}

pub(crate) const unsafe fn transmute2<A, B>(value: A) -> B {
    const {
        assert!(mem::align_of::<A>() >= mem::align_of::<B>());
    }
    unsafe { transmute_unaligned::<A, B>(value) }
}

pub(crate) const unsafe fn transmute_unaligned<A, B>(value: A) -> B {
    const {
        assert!(mem::size_of::<A>() == mem::size_of::<B>());
    }
    union U<A, B> {
        a: ManuallyDrop<A>,
        b: ManuallyDrop<B>,
    }
    unsafe {
        ManuallyDrop::into_inner(
            U {
                a: ManuallyDrop::new(value),
            }
            .b,
        )
    }
}

#[track_caller]
pub(crate) const unsafe fn transmute_ref<A, B>(r: &A) -> &B {
    assert!(const { mem::align_of::<A>() >= mem::align_of::<B>() });
    unsafe { transmute2(r) }
}

#[track_caller]
pub(crate) const unsafe fn transmute_mut<A, B>(r: &mut A) -> &mut B {
    assert!(const { mem::align_of::<A>() == mem::align_of::<B>() });
    unsafe { transmute2(r) }
}
