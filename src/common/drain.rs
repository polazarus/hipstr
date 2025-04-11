//! Generic draining iterator implementation for vectors.

use core::iter::FusedIterator;
use core::ops::{Range, RangeBounds};
use core::{fmt, mem, ptr, slice};

use super::traits::MutVector;
use super::RangeError;

/// A draining iterator for vectors.
///
/// This object is created by [`ThinVec::drain`], for instance. See its
/// documentation for more information.
///
/// # Example
///
/// ```
/// use hipstr::thin_vec;
/// let mut v = thin_vec![0, 1, 2];
/// let iter = v.drain(..);
/// ```
///
/// [`ThinVec::drain`]: crate::vecs::thin::ThinVec::drain
pub struct Drain<'a, V: MutVector> {
    vec: &'a mut V,
    tail_start: usize,
    tail_len: usize,
    range: Range<usize>,
}

impl<'a, V: MutVector> Drain<'a, V> {
    pub(crate) fn new(vec: &'a mut V, range: impl RangeBounds<usize>) -> Result<Self, RangeError> {
        let len = vec.len();
        let range = super::range(range, len)?;

        // SAFETY: start < len
        //
        // if drain is leaked, the length is at least memory safe but will leak
        // the tail
        unsafe {
            vec.set_len(range.start);
        }

        Ok(Self {
            vec,
            tail_start: range.end,
            tail_len: len - range.end,
            range,
        })
    }

    /// Returns the remaining items of this iterator as a slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::thin_vec;
    /// let mut v = thin_vec!['a', 'b', 'c'];
    /// let mut drain = v.drain(..);
    /// assert_eq!(drain.as_slice(), &['a', 'b', 'c']);
    /// let _ = drain.next().unwrap();
    /// assert_eq!(drain.as_slice(), &['b', 'c']);
    /// ```
    #[must_use]
    pub fn as_slice(&self) -> &[V::Item] {
        unsafe { slice::from_raw_parts(self.vec.as_ptr().add(self.range.start), self.range.len()) }
    }
}

impl<V: MutVector> Iterator for Drain<'_, V> {
    type Item = V::Item;

    fn next(&mut self) -> Option<Self::Item> {
        let index = self.range.next()?;
        let value = unsafe { self.vec.as_non_null().add(index).read() };
        Some(value)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.range.len();
        (len, Some(len))
    }
}

impl<V: MutVector> FusedIterator for Drain<'_, V> {}

impl<V: MutVector> ExactSizeIterator for Drain<'_, V> {
    fn len(&self) -> usize {
        self.range.len()
    }
}

impl<V: MutVector> DoubleEndedIterator for Drain<'_, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let index = self.range.next_back()?;
        let value = unsafe { self.vec.as_non_null().add(index).read() };
        Some(value)
    }
}

impl<V: MutVector> fmt::Debug for Drain<'_, V>
where
    V::Item: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Drain").field(&self.as_slice()).finish()
    }
}

impl<'a, V: MutVector> Drop for Drain<'a, V> {
    fn drop(&mut self) {
        if mem::needs_drop::<V::Item>() {
            unsafe {
                let slice = slice::from_raw_parts_mut(
                    self.vec.as_mut_ptr().add(self.range.start),
                    self.range.len(),
                );
                ptr::drop_in_place(slice);
            }
        }

        let ptr = self.vec.as_non_null();
        let start = self.vec.len();
        // SAFETY: type invariant
        unsafe {
            ptr.add(start)
                .copy_from(ptr.add(self.tail_start), self.tail_len);
            self.vec.set_len(start + self.tail_len);
        }
    }
}
