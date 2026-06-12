//! Splice implementation for vectors.

use core::ops::RangeBounds;

use crate::common::RangeError;
use crate::common::drain::Drain;
use crate::traits::{GrowableVector, MutableVector};

#[cfg(test)]
mod tests;

#[cfg(test)]
#[cfg(feature = "alloc")]
mod alloc_tests;

/// A splicing iterator for vectors.
///
/// This struct is created by the splice methods of all the vectors in this crate.
///
/// # Example
///
/// ```
/// use hipvec::thin_vec;
/// let mut v = thin_vec![0, 1, 2];
/// let iter = v.splice(1.., [9, 8]);
/// assert!(iter.eq([1, 2]));
/// assert_eq!(v, [0, 9, 8]);
/// ```
pub struct Splice<'a, V: GrowableVector, I: Iterator<Item = V::Item>> {
    drain: Drain<'a, V>,
    replace_with: I,
}

impl<'a, V: GrowableVector, I: Iterator<Item = V::Item>> Splice<'a, V, I> {
    /// Creates a new splice iterator.
    #[inline]
    pub(crate) fn new(
        vec: &'a mut V,
        range: impl RangeBounds<usize>,
        replace_with: impl IntoIterator<IntoIter = I>,
    ) -> Result<Self, RangeError> {
        Ok(Self {
            drain: Drain::new(vec, range)?,
            replace_with: replace_with.into_iter(),
        })
    }

    #[cfg(feature = "alloc")]
    fn slow_finish(&mut self) {
        use alloc::vec::Vec;
        let remainder: Vec<V::Item> = self.replace_with.by_ref().collect();
        if !remainder.is_empty() {
            move_tail(&mut self.drain, remainder.len());
            fill_hole(&mut self.drain, &mut remainder.into_iter());
        }
    }

    #[cfg(not(feature = "alloc"))]
    fn slow_finish(&mut self) {
        use core::mem::MaybeUninit;
        let mut buffer1 = MaybeUninit::uninit();
        let mut buffer512: [MaybeUninit<u8>; 512] = [const { MaybeUninit::uninit() }; 512];
        let mut buffer128: [MaybeUninit<V::Item>; 128] = [const { MaybeUninit::uninit() }; 128];

        let buffer: &mut [MaybeUninit<V::Item>] = match size_of::<V::Item>() {
            512.. => core::slice::from_mut(&mut buffer1),
            3..=511 => unsafe { buffer512.align_to_mut().1 },
            _ => &mut buffer128,
        };

        loop {
            // fill buffer with replacements, up to its capacity
            let count = buffer
                .iter_mut()
                .zip(self.replace_with.by_ref())
                .map(|(slot, value)| {
                    slot.write(value);
                })
                .count();

            // if no items were written, the iterator is exhausted and we are done
            if count == 0 {
                break;
            }

            // move tail
            move_tail(&mut self.drain, count);

            // copy buffer into hole
            // SAFETY: the buffer is initialized up to `count`
            unsafe {
                self.drain
                    .vec
                    .as_mut_ptr()
                    .add(self.drain.tail_start - count)
                    .copy_from(buffer.as_ptr().cast::<V::Item>(), count);
                self.drain.vec.set_len(self.drain.vec.len() + count);
            }
        }
    }
}

impl<V: GrowableVector, I: Iterator<Item = V::Item>> Iterator for Splice<'_, V, I> {
    type Item = V::Item;

    fn next(&mut self) -> Option<Self::Item> {
        self.drain.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.drain.size_hint()
    }
}

impl<V: GrowableVector, I: Iterator<Item = V::Item>> ExactSizeIterator for Splice<'_, V, I> {
    fn len(&self) -> usize {
        self.drain.len()
    }
}

impl<V: GrowableVector, I: Iterator<Item = V::Item>> DoubleEndedIterator for Splice<'_, V, I> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.drain.next_back()
    }
}

impl<V: GrowableVector, I: Iterator<Item = V::Item>> Drop for Splice<'_, V, I> {
    fn drop(&mut self) {
        self.drain.by_ref().for_each(drop);

        fill_hole(&mut self.drain, &mut self.replace_with);

        let (lower, _upper) = self.replace_with.size_hint();
        if lower > 0 {
            move_tail(&mut self.drain, lower);
            fill_hole(&mut self.drain, &mut self.replace_with);
        }

        self.slow_finish();
    }
}

/// Fills the hole left by the drained elements with items from the iterator.
///
/// In the end, either the hole is completely filled, or the iterator is exhausted.
fn fill_hole<V: MutableVector, I: Iterator<Item = V::Item>>(
    drain: &mut Drain<'_, V>,
    iter: &mut I,
) {
    let mut len = drain.vec.len();
    while len < drain.tail_start
        && let Some(value) = iter.next()
    {
        unsafe {
            drain.vec.as_mut_ptr().add(len).write(value);
            len += 1;
            drain.vec.set_len(len);
        }
    }
}

fn move_tail<V: GrowableVector>(drain: &mut Drain<'_, V>, count: usize) {
    let len = drain.tail_start + drain.tail_len + count;
    let current_len = drain.vec.len();
    let additional = len.saturating_sub(current_len);
    drain.vec.reserve(additional);

    let ptr = drain.vec.as_mut_ptr();
    unsafe {
        let src = ptr.add(drain.tail_start);
        let dst = ptr.add(drain.tail_start + count);
        src.copy_to(dst, drain.tail_len);
    }
    drain.tail_start += count;
}
