//! Common functions and types.

use core::mem::ManuallyDrop;
use core::ops::{Bound, Range, RangeBounds};
use core::{error, fmt};

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
#[derive(Debug, PartialEq, PartialOrd, Clone, Copy)]
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
    /// Returns a static message for the error.
    pub const fn const_message(&self) -> &'static str {
        match self {
            RangeError::StartOverflows => "start index overflows",
            RangeError::EndOverflows => "end index overflows",
            RangeError::StartGreaterThanEnd { .. } => "start index is greater than end index",
            RangeError::EndOutOfBounds { .. } => "end index is out of bounds",
        }
    }
}

impl error::Error for RangeError {}

impl fmt::Display for RangeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            RangeError::StartOverflows => write!(f, "start index overflows"),
            RangeError::EndOverflows => write!(f, "end index overflows"),
            RangeError::StartGreaterThanEnd { start, end } => {
                write!(f, "start index {} is greater than end index {}", start, end)
            }
            RangeError::EndOutOfBounds { end, len } => {
                write!(
                    f,
                    "end index {} is out of bounds for slice of length {}",
                    end, len
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

/// Compares two slices and returns their ordering, if possible.
#[inline(always)]
pub(crate) fn cmp_slice<T>(a: &[T], b: &[T]) -> Option<core::cmp::Ordering>
where
    T: PartialOrd,
{
    PartialOrd::partial_cmp(a, b)
}


#[cfg(test)]
mod tests {
    use alloc::format;

    use super::*;

    #[test]
    fn ranges() {
        assert_eq!(range(0..5, 10).unwrap(), 0..5);
        assert_eq!(range(0..=5, 10).unwrap(), 0..6);
        assert_eq!(range(..5, 10).unwrap(), 0..5);
        assert_eq!(range(..=5, 10).unwrap(), 0..6);
        assert_eq!(range(2.., 10).unwrap(), 2..10);

        let err = range(..=usize::MAX, 1).unwrap_err();
        assert_eq!(err, RangeError::EndOverflows);
        assert_eq!(format!("{err}"), "end index overflows");
        assert_eq!(err.const_message(), "end index overflows");

        let err = range((Bound::Excluded(usize::MAX), Bound::Unbounded), 10).unwrap_err();
        assert_eq!(err, RangeError::StartOverflows);
        assert_eq!(format!("{err}"), "start index overflows");
        assert_eq!(err.const_message(), "start index overflows");

        let err = range(5..2, 10).unwrap_err();
        assert_eq!(err, RangeError::StartGreaterThanEnd { start: 5, end: 2 });
        assert_eq!(
            format!("{err}"),
            "start index 5 is greater than end index 2"
        );
        assert_eq!(err.const_message(), "start index is greater than end index");

        let err = range(5..10, 5).unwrap_err();
        assert_eq!(err, RangeError::EndOutOfBounds { end: 10, len: 5 });
        assert_eq!(
            format!("{err}"),
            "end index 10 is out of bounds for slice of length 5"
        );
        assert_eq!(err.const_message(), "end index is out of bounds");

        assert_eq!(
            range(6..10, 5).unwrap_err(),
            RangeError::EndOutOfBounds { end: 10, len: 5 }
        );
        assert_eq!(
            format!("{err}"),
            "end index 10 is out of bounds for slice of length 5"
        );
        assert_eq!(err.const_message(), "end index is out of bounds");
    }
}
