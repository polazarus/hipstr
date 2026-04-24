use core::ops::RangeBounds;

use crate::common::RangeError;
use crate::common::drain::Drain;
use crate::traits::{GrowableVector, MutableVector};

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

        let remainder: alloc::vec::Vec<V::Item> = self.replace_with.by_ref().collect();
        if !remainder.is_empty() {
            move_tail(&mut self.drain, remainder.len());
            fill_hole(&mut self.drain, &mut remainder.into_iter());
        }
    }
}

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

#[cfg(test)]
#[cfg(feature = "alloc")]
mod tests {
    use alloc::boxed::Box;
    use alloc::vec;

    use super::*;

    #[test]
    fn splice() {
        let mut v = vec![1, 2, 3, 4, 5];
        {
            let splice = Splice::new(&mut v, 1..4, [9, 8]).unwrap();
            assert!(splice.eq([2, 3, 4]));
        }
        assert_eq!(v, [1, 9, 8, 5]);

        let mut v = vec![1, 2, 3, 4, 5];
        {
            let splice = Splice::new(&mut v, 1..4, [9, 8, 7, 6]).unwrap();
            assert!(splice.eq([2, 3, 4]));
        }
        assert_eq!(v, [1, 9, 8, 7, 6, 5]);

        let mut v = vec![1, 2, 3, 4, 5];
        {
            let splice =
                Splice::new(&mut v, 1..4, [9, 8, 7, 6].into_iter().filter(|_| true)).unwrap();
            assert!(splice.eq([2, 3, 4]));
        }
        assert_eq!(v, [1, 9, 8, 7, 6, 5]);

        let mut v = vec![1, 2, 3, 4, 5];
        {
            let splice = Splice::new(&mut v, 0..0, [0]).unwrap();
            assert!(splice.eq([]));
        }
        assert_eq!(v, [0, 1, 2, 3, 4, 5]);
    }

    #[test]
    fn splice_boxed() {
        let mut v = [1, 2, 3, 4, 5].map(Box::new).to_vec();
        {
            let splice = Splice::new(&mut v, 1..4, [9, 8].map(Box::new)).unwrap();
            assert!(splice.eq([2, 3, 4].map(Box::new)));
        }
        assert_eq!(v, [1, 9, 8, 5].map(Box::new));

        let mut v = [1, 2, 3, 4, 5].map(Box::new).to_vec();
        {
            let splice = Splice::new(&mut v, 1..4, [9, 8, 7, 6].map(Box::new)).unwrap();
            assert!(splice.eq([2, 3, 4].map(Box::new)));
        }
        assert_eq!(v, [1, 9, 8, 7, 6, 5].map(Box::new));

        let mut v = [1, 2, 3, 4, 5].map(Box::new).to_vec();
        {
            let splice = Splice::new(
                &mut v,
                1..4,
                [9, 8, 7, 6].map(Box::new).into_iter().filter(|_| true),
            )
            .unwrap();
            assert!(splice.eq([2, 3, 4].map(Box::new)));
        }
        assert_eq!(v, [1, 9, 8, 7, 6, 5].map(Box::new));
    }
}
