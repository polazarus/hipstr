//! O(1) slicing, only for the 3-word representation (`Hip*` types).

use core::fmt;
use core::ops::{Bound, Range, RangeBounds};

use super::backend::Backend;
use super::enc::{Bytes, Encoding, Utf8};
use super::hip::Hip;
use super::repr::{Repr, Wide};

/// Kind of slicing error.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum SliceErrorKind {
    /// Start index should be less than or equal to the end index.
    StartGreaterThanEnd,
    /// Start index out of bounds.
    StartOutOfBounds,
    /// End index out of bounds.
    EndOutOfBounds,
    /// Start index is not at a char boundary.
    StartNotACharBoundary,
    /// End index is not at a char boundary.
    EndNotACharBoundary,
}

impl fmt::Display for SliceErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::StartGreaterThanEnd => "start index is greater than end index",
            Self::StartOutOfBounds => "start index out of bounds",
            Self::EndOutOfBounds => "end index out of bounds",
            Self::StartNotACharBoundary => "start index is not at a char boundary",
            Self::EndNotACharBoundary => "end index is not at a char boundary",
        })
    }
}

/// Slicing error, borrowing the value that failed to slice.
pub struct SliceError<'s, E: Encoding, R> {
    kind: SliceErrorKind,
    range: Range<usize>,
    source: &'s Hip<E, R>,
}

impl<E: Encoding, R> Clone for SliceError<'_, E, R> {
    fn clone(&self) -> Self {
        Self {
            kind: self.kind,
            range: self.range.clone(),
            source: self.source,
        }
    }
}

impl<'a, E: Encoding, R: Repr<'a, u8>> PartialEq for SliceError<'_, E, R>
where
    E::Slice: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind && self.range == other.range && self.source == other.source
    }
}

impl<'s, E: Encoding, R> SliceError<'s, E, R> {
    #[inline]
    #[must_use]
    pub const fn kind(&self) -> SliceErrorKind {
        self.kind
    }

    #[inline]
    #[must_use]
    pub const fn start(&self) -> usize {
        self.range.start
    }

    #[inline]
    #[must_use]
    pub const fn end(&self) -> usize {
        self.range.end
    }

    #[inline]
    #[must_use]
    pub fn range(&self) -> Range<usize> {
        self.range.clone()
    }

    /// The value that failed to slice.
    #[inline]
    #[must_use]
    pub const fn source(&self) -> &'s Hip<E, R> {
        self.source
    }
}

impl<'a, E: Encoding, R: Repr<'a, u8>> fmt::Debug for SliceError<'_, E, R>
where
    E::Slice: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SliceError")
            .field("kind", &self.kind)
            .field("range", &self.range)
            .field("source", &self.source)
            .finish()
    }
}

impl<E: Encoding, R> fmt::Display for SliceError<'_, E, R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} (range {:?})", self.kind, self.range)
    }
}

impl<'a, E: Encoding, R: Repr<'a, u8>> core::error::Error for SliceError<'_, E, R> where
    E::Slice: fmt::Debug
{
}

/// Resolves `range` against `len`.
fn simplify(
    range: impl RangeBounds<usize>,
    len: usize,
) -> Result<Range<usize>, (SliceErrorKind, Range<usize>)> {
    let start = match range.start_bound() {
        Bound::Included(&s) => s,
        Bound::Excluded(&s) => s.saturating_add(1),
        Bound::Unbounded => 0,
    };
    let end = match range.end_bound() {
        Bound::Included(&e) => e.saturating_add(1),
        Bound::Excluded(&e) => e,
        Bound::Unbounded => len,
    };
    let kind = if start > end {
        SliceErrorKind::StartGreaterThanEnd
    } else if start > len {
        SliceErrorKind::StartOutOfBounds
    } else if end > len {
        SliceErrorKind::EndOutOfBounds
    } else {
        return Ok(start..end);
    };
    Err((kind, start..end))
}

impl<'a, E: Encoding, B: Backend> Hip<E, Wide<'a, u8, B>> {
    /// # Safety
    ///
    /// `range` must be in bounds and cut at valid boundaries for `E`.
    #[inline]
    unsafe fn slice_bytes(&self, range: Range<usize>) -> Self {
        // SAFETY: precondition
        unsafe { Self::from_repr(self.repr().slice(range)) }
    }

    /// Range of `sub` within `self`, if `sub` points inside `self`.
    fn range_of(&self, sub: &E::Slice) -> Option<Range<usize>> {
        let outer = self.bytes().as_ptr_range();
        let inner = E::as_bytes(sub).as_ptr_range();
        if outer.start <= inner.start && inner.end <= outer.end {
            let start = inner.start as usize - outer.start as usize;
            Some(start..start + E::as_bytes(sub).len())
        } else {
            None
        }
    }

    /// Returns a slice of `self` designated by a reference into it, sharing
    /// the storage (O(1)).
    ///
    /// # Panics
    ///
    /// Panics if `sub` does not point inside `self`.
    #[must_use]
    pub fn slice_ref(&self, sub: &E::Slice) -> Self {
        self.try_slice_ref(sub)
            .expect("slice reference not inside the value")
    }

    /// Like [`slice_ref`](Self::slice_ref), returning `None` if `sub` does not
    /// point inside `self`.
    #[must_use]
    pub fn try_slice_ref(&self, sub: &E::Slice) -> Option<Self> {
        let range = self.range_of(sub)?;
        // SAFETY: in bounds, and `sub` is a valid `E::Slice` so its bounds are
        // valid cut points
        Some(unsafe { self.slice_bytes(range) })
    }

    /// Like [`slice_ref`](Self::slice_ref) without checking that `sub`
    /// points inside `self`.
    ///
    /// # Safety
    ///
    /// `sub` must point inside `self`.
    #[must_use]
    pub unsafe fn slice_ref_unchecked(&self, sub: &E::Slice) -> Self {
        let outer = self.bytes().as_ptr();
        let inner = E::as_bytes(sub);
        let start = inner.as_ptr() as usize - outer as usize;
        // SAFETY: precondition
        unsafe { self.slice_bytes(start..start + inner.len()) }
    }
}

impl<'a, B: Backend> Hip<Bytes, Wide<'a, u8, B>> {
    /// Returns a subslice sharing the storage (O(1); copied inline if small).
    ///
    /// # Panics
    ///
    /// Panics if the range is out of bounds.
    #[must_use]
    pub fn slice(&self, range: impl RangeBounds<usize>) -> Self {
        match self.try_slice(range) {
            Ok(s) => s,
            Err(e) => panic!("{e}"),
        }
    }

    /// Returns a subslice sharing the storage, or an error.
    ///
    /// # Errors
    ///
    /// Returns an error if the range is out of bounds.
    pub fn try_slice(
        &self,
        range: impl RangeBounds<usize>,
    ) -> Result<Self, SliceError<'_, Bytes, Wide<'a, u8, B>>> {
        let range = simplify(range, self.len()).map_err(|(kind, range)| SliceError {
            kind,
            range,
            source: self,
        })?;
        // SAFETY: in bounds, any cut is valid for bytes
        Ok(unsafe { self.slice_bytes(range) })
    }

    /// Returns a subslice without bound checks.
    ///
    /// # Safety
    ///
    /// The range must be in bounds.
    #[must_use]
    pub unsafe fn slice_unchecked(&self, range: impl RangeBounds<usize>) -> Self {
        let range = simplify(range, self.len()).unwrap_or_else(|(_, r)| r);
        // SAFETY: precondition
        unsafe { self.slice_bytes(range) }
    }
}

impl<'a, B: Backend> Hip<Utf8, Wide<'a, u8, B>> {
    /// Returns a substring sharing the storage (O(1); copied inline if small).
    ///
    /// # Panics
    ///
    /// Panics if the range is out of bounds or not at char boundaries.
    #[must_use]
    pub fn slice(&self, range: impl RangeBounds<usize>) -> Self {
        match self.try_slice(range) {
            Ok(s) => s,
            Err(e) => panic!("{e}"),
        }
    }

    /// Returns a substring sharing the storage, or an error.
    ///
    /// # Errors
    ///
    /// Returns an error if the range is out of bounds or not at char boundaries.
    pub fn try_slice(
        &self,
        range: impl RangeBounds<usize>,
    ) -> Result<Self, SliceError<'_, Utf8, Wide<'a, u8, B>>> {
        let error = |kind, range| SliceError {
            kind,
            range,
            source: self,
        };
        let range = simplify(range, self.len()).map_err(|(kind, range)| error(kind, range))?;
        if !self.as_str().is_char_boundary(range.start) {
            return Err(error(SliceErrorKind::StartNotACharBoundary, range));
        }
        if !self.as_str().is_char_boundary(range.end) {
            return Err(error(SliceErrorKind::EndNotACharBoundary, range));
        }
        // SAFETY: in bounds, at char boundaries
        Ok(unsafe { self.slice_bytes(range) })
    }

    /// Returns a substring without bound or boundary checks.
    ///
    /// # Safety
    ///
    /// The range must be in bounds and at char boundaries.
    #[must_use]
    pub unsafe fn slice_unchecked(&self, range: impl RangeBounds<usize>) -> Self {
        let range = simplify(range, self.len()).unwrap_or_else(|(_, r)| r);
        // SAFETY: precondition
        unsafe { self.slice_bytes(range) }
    }
}
