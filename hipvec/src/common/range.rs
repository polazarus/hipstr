use core::error::Error;
use core::fmt;
use core::ops::{Bound, Range, RangeBounds};

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

impl Error for RangeError {}

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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn valid_range() {
        assert_eq!(range(0..5, 10), Ok(0..5));
        assert_eq!(range(3..=7, 10), Ok(3..8));
        assert_eq!(range(..4, 10), Ok(0..4));
        assert_eq!(range(..=4, 10), Ok(0..5));
        assert_eq!(range(6.., 10), Ok(6..10));
        assert_eq!(range(.., 10), Ok(0..10));
        assert_eq!(
            range((Bound::Excluded(2), Bound::Included(5)), 10),
            Ok(3..6)
        );
    }

    #[test]
    fn invalid_range() {
        assert_eq!(
            range((Bound::Excluded(usize::MAX), Bound::Unbounded), 10),
            Err(RangeError::StartOverflows)
        );
        assert_eq!(
            range((Bound::Unbounded, Bound::Included(usize::MAX)), 10),
            Err(RangeError::EndOverflows)
        );

        assert_eq!(
            range(11..15, 10),
            Err(RangeError::StartOutOfBounds { start: 11, len: 10 })
        );
        assert_eq!(
            range(8..12, 10),
            Err(RangeError::EndOutOfBounds { end: 12, len: 10 })
        );
        assert_eq!(
            range(5..3, 10),
            Err(RangeError::StartGreaterThanEnd { start: 5, end: 3 })
        );
    }
}
