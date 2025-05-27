//! Common functions and types.

use alloc::alloc::handle_alloc_error;
use core::alloc::Layout;
use core::mem::{self, ManuallyDrop, MaybeUninit};
use core::ops::{Bound, Range, RangeBounds};
use core::ptr::NonNull;
use core::{error, fmt, ptr};

pub mod drain;
#[cfg(test)]
mod tests;
pub mod traits;

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
struct SliceGuard<'a, T> {
    slice: &'a mut [MaybeUninit<T>],
    initialized: usize,
}

impl<T> Drop for SliceGuard<'_, T> {
    fn drop(&mut self) {
        if mem::needs_drop::<T>() {
            unsafe {
                let slice_ptr = ptr::from_mut(&mut self.slice[..self.initialized]);
                let slice_ptr = slice_ptr as *mut [T];
                ptr::drop_in_place(slice_ptr);
            }
        }
    }
}

#[inline]
pub(crate) fn guarded_slice_clone<T: Clone>(dst: &mut [MaybeUninit<T>], src: &[T]) -> usize {
    let mut guard = SliceGuard {
        slice: dst,
        initialized: 0,
    };

    for (dst, src) in guard.slice.iter_mut().zip(src.iter()) {
        dst.write(src.clone());
        guard.initialized += 1;
    }

    let written = guard.initialized;
    mem::forget(guard);
    written
}

#[inline]
#[cfg_attr(coverage_nightly, coverage(off))]
pub(crate) fn check_alloc(ptr: *mut u8, layout: Layout) -> NonNull<u8> {
    let Some(ptr) = NonNull::new(ptr) else {
        handle_alloc_error(layout);
    };
    ptr
}
