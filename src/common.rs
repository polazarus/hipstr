//! Common functions and types.

use alloc::alloc::handle_alloc_error;
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
pub mod traits;

#[cfg(test)]
mod tests;

#[repr(usize)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[rules_derive(derives::ConstDefault(Self::Zero))]
enum ZeroUsizeInner {
    Zero = 0,
}

/// A pointer-sized zero.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[rules_derive(derives::ConstDefault(Self(ZeroUsizeInner::Zero)))]
pub struct ZeroUsize(ZeroUsizeInner);

/// Gets a bitwise copy of a value, even if its type is not [`Copy`].
///
/// # Safety
///
/// The caller must ensure that `T` is safe to bitwise-copy.
pub(crate) const unsafe fn force_copy<T>(value: &T) -> T {
    // SAFETY: see the safety comment on the function.
    unsafe { core::ptr::read(value) }
}

/// Panics with the provided displayable error message.
///
/// # Panics
///
/// Always panics with the provided error message.
#[track_caller]
pub(crate) fn panic_display(e: impl fmt::Display) -> ! {
    panic!("{e}");
}

/// Unwraps a `Result`, panicking with the display of the error on failure.
///
/// # Panics
///
/// Always panics if the result is an `Err`.
#[track_caller]
pub(crate) fn unwrap_display<T, E: fmt::Display>(result: Result<T, E>) -> T {
    match result {
        Ok(value) => value,
        Err(e) => panic_display(e),
    }
}

#[track_caller]
#[cfg_attr(coverage_nightly, coverage(off))]
pub(crate) fn unwrap_unchecked_display<T, E: fmt::Display>(result: Result<T, E>) -> T {
    match result {
        Ok(value) => value,
        Err(e) => unsafe {
            if cfg!(debug_assertions) {
                panic!("{e}");
            } else {
                core::hint::unreachable_unchecked()
            }
        },
    }
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
    if start > len {
        return Err(RangeError::StartOutOfBounds { start, len });
    }
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
    /// The start index is out of bounds.
    StartOutOfBounds { start: usize, len: usize },
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
            Self::StartOutOfBounds { .. } => "start index is out of bounds",
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
            Self::StartOutOfBounds { start, len } => {
                write!(
                    f,
                    "start index {start} is out of bounds for slice of length {len}",
                )
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

/// Copies a `T` slice to a `ManuallyDrop<T>` slice.
///
/// # Panics
///
/// Panics if the lengths of the source and destination slices do not match.
pub(crate) const fn maybe_uninit_write_copy_of_slice<T>(dst: &mut [MaybeUninit<T>], src: &[T])
where
    T: Copy,
{
    let len = src.len();
    assert!(
        len == dst.len(),
        "source slice length does not match destination slice length"
    );
    // SAFETY: `T` is `Copy`, and the lengths are equal
    unsafe {
        dst.as_mut_ptr().copy_from(src.as_ptr().cast(), len);
    }
}

/// A guard that drops the initialized elements of a slice.
///
/// # Type invariants
///
/// - The pointer `ptr` must be valid for reads and writes of `len` elements of type `T`.
/// - The `initialized` field must always be less than or equal to `len`.
/// - The elements from `ptr` to `ptr.add(initialized)` (excluded) must be initialized.
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
pub(crate) unsafe fn guarded_slice_clone<T: Clone>(dst: *mut T, src: *const T, len: usize) {
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

/// Transmutes a value of type `A` to type `B` by bitwise copying.
///
/// # Safety
///
/// The caller must ensure that `A` and `B` have the same size and that
/// the bitwise representation of `A` is valid for `B`.
pub(crate) const unsafe fn force_transmute<A, B>(value: A) -> B {
    union U<A, B> {
        a: ManuallyDrop<A>,
        b: ManuallyDrop<B>,
    }

    debug_assert!(mem::size_of::<A>() == mem::size_of::<B>());

    let union = U {
        a: ManuallyDrop::new(value),
    };

    // SAFETY: caller ensures that the types are compatible.
    unsafe { ManuallyDrop::into_inner(union.b) }
}

/// Gets the range of indices of a child slice within a parent slice, if the
/// child is contained within the parent.
pub(crate) fn range_of<T>(child: &[T], parent: &[T]) -> Option<Range<usize>> {
    let child = child.as_ptr_range();
    let parent = parent.as_ptr_range();
    if parent.start <= child.start && child.end <= parent.end {
        // SAFETY: pointers are checked to be in the same range
        unsafe {
            let start = child.start.offset_from_unsigned(parent.start);
            let end = child.end.offset_from_unsigned(parent.start);
            Some(start..end)
        }
    } else {
        None
    }
}
