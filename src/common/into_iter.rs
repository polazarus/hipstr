use core::mem::needs_drop;
use core::{ptr, slice};

use super::traits::MutVector;

pub struct IntoIter<V: MutVector> {
    vec: V,
    start: usize,
    end: usize,
}

impl<V: MutVector> IntoIter<V> {
    pub(crate) fn new(mut vec: V) -> Self {
        let len = vec.len();
        // SAFETY: at worst forget the vector's contents
        unsafe {
            vec.set_len(0);
        }
        Self {
            vec,
            start: 0,
            end: len,
        }
    }
}

impl<V: MutVector> Drop for IntoIter<V> {
    fn drop(&mut self) {
        if needs_drop::<V::Item>() {
            // SAFETY: we are dropping all remaining items
            unsafe {
                let start = self.vec.as_mut_ptr().add(self.start);
                let len = self.end - self.start;
                let slice = slice::from_raw_parts_mut(start, len);
                ptr::drop_in_place(slice);
            }
        }
    }
}

impl<V: MutVector> Iterator for IntoIter<V> {
    type Item = V::Item;

    fn next(&mut self) -> Option<Self::Item> {
        if self.start == self.end {
            None
        } else {
            // SAFETY: start < end
            unsafe {
                let ptr = self.vec.as_mut_ptr().add(self.start);
                self.start += 1;
                Some(ptr.read())
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.end - self.start;
        (len, Some(len))
    }
}

impl<V: MutVector> ExactSizeIterator for IntoIter<V> {
    fn len(&self) -> usize {
        self.end - self.start
    }
}

impl<V: MutVector> core::iter::FusedIterator for IntoIter<V> {}

impl<V: MutVector> core::iter::DoubleEndedIterator for IntoIter<V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.start == self.end {
            None
        } else {
            self.end -= 1;
            // SAFETY: start < end
            unsafe {
                let ptr = self.vec.as_mut_ptr().add(self.end);
                Some(ptr.read())
            }
        }
    }
}
