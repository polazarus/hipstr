use alloc::boxed::Box;
use alloc::vec;
use core::mem::MaybeUninit;
use core::ptr;
use std::vec::Vec;

use const_default::ConstDefault;
use typenum::U32;

use super::Bytes;
use crate::backend::tests::BoundedRc;
use crate::vecs::hip::{HipVec, Inline, SplitOffError};
use crate::vecs::inline::{InlineVec, PointerSize};
use crate::vecs::thin::{Reserved, ThinVec};
use crate::vecs::wide::WideVec;
use crate::{Arc, Unique};

#[test]
fn size_of_hipvec() {
    assert_eq!(
        size_of::<HipVec<'static, u8, Arc>>(),
        3 * size_of::<usize>()
    );

    assert_eq!(
        size_of::<HipVec<'static, usize, Arc>>(),
        3 * size_of::<usize>()
    );
}

#[test]
fn new() {
    let h = HipVec::<u8, Arc>::new();
    assert_eq!(h.len(), 0);
    assert!(!h.is_allocated());
    assert!(h.is_borrowed()); // for now, the empty hipvec is borrowed
}

#[test]
fn new_boxed() {
    let h = HipVec::<Box<u8>, Arc>::new();
    assert_eq!(h.len(), 0);
    assert!(!h.is_allocated());
    assert!(h.is_borrowed()); // for now, the empty hipvec is borrowed
}

#[test]
fn with_capacity() {
    let h = HipVec::<u8, Arc>::with_capacity(0);
    assert_eq!(h.len(), 0);
    assert!(!h.is_allocated());
    assert!(h.is_nil());

    let h = HipVec::<u8, Arc>::with_capacity(10);
    assert_eq!(h.len(), 0);
    assert!(h.is_inline());
    assert!(!h.is_borrowed());
    assert!(!h.is_allocated());

    let h = HipVec::<u8, Arc>::with_capacity(100);
    assert_eq!(h.len(), 0);
    assert!(h.is_thin());
    assert!(h.is_allocated());
    assert!(!h.is_borrowed());
    assert!(!h.is_inline());
}

#[test]
fn inline_copy() {
    let slice = &[];
    let h = HipVec::<u8, Arc>::inline_copy(slice);
    assert_eq!(h.len(), slice.len());
    assert!(h.is_inline());
    assert_eq!(h.as_slice(), slice);

    let slice = &[1, 2, 3, 4, 5];
    let h = HipVec::<u8, Arc>::inline_copy(slice);
    assert_eq!(h.len(), slice.len());
    assert!(h.is_inline());
    assert_eq!(h.as_slice(), slice);
}

#[test]
#[should_panic(expected = "required capacity exceeds inline capacity")]
fn inline_copy_panic() {
    let slice = &[42; 42];
    let _h = HipVec::<u8, Arc>::inline_copy(slice);
}

#[test]
fn try_inline_copy() {
    let slice = &[];
    let h = HipVec::<u8, Arc>::try_inline_copy(slice).unwrap();
    assert_eq!(h.len(), slice.len());
    assert!(h.is_inline());
    assert_eq!(h.as_slice(), slice);

    let slice = &[1, 2, 3, 4, 5];
    let h = HipVec::<u8, Arc>::try_inline_copy(slice).unwrap();
    assert_eq!(h.len(), slice.len());
    assert!(h.is_inline());
    assert_eq!(h.as_slice(), slice);

    let slice = &[42; 42];
    let h = HipVec::<u8, Arc>::try_inline_copy(slice);
    assert!(h.is_none());
}

#[test]
fn inline_array() {
    let h = HipVec::<u8, Arc>::inline_array([]);
    assert_eq!(h.len(), 0);
    assert!(h.is_inline());

    let h = HipVec::<u8, Arc>::inline_array([1, 2, 3, 4, 5]);
    assert_eq!(h.len(), 5);
    assert!(h.is_inline());
    assert_eq!(h.as_slice(), &[1, 2, 3, 4, 5]);
}

#[test]
#[should_panic(expected = "required capacity exceeds inline capacity")]
fn inline_array_panic() {
    let _h = HipVec::<u8, Arc>::inline_array([42; 42]);
}

#[test]
fn inline_empty() {
    let h = HipVec::<u8, Arc>::inline_empty();
    assert_eq!(h.len(), 0);
    assert!(h.is_inline());
    assert!(!h.is_nil());
}

#[test]
fn from_array_empty() {
    let h = HipVec::<u8, Arc>::from([]);
    assert_eq!(h.len(), 0);
    assert!(h.is_nil());
    assert!(h.as_slice().is_empty());
}

#[test]
fn from_array_inline() {
    let h = HipVec::<u8, Arc>::from([1, 2, 3, 4, 5]);
    assert_eq!(h.len(), 5);
    assert!(h.is_inline());
    assert!(!h.is_allocated());
    assert_eq!(h.as_slice(), &[1, 2, 3, 4, 5]);
}

#[test]
fn from_array_thin() {
    let h = HipVec::<u8, Arc>::from([42; 42]);
    assert_eq!(h.len(), 42);
    // assert!(!h.is_inline());
    // assert!(h.is_allocated());
    assert_eq!(h.as_slice(), &[42; 42]);
    assert!(h.is_thin());
    assert!(!h.is_wide());
    assert!(h.is_allocated());
}

#[test]
fn from_inline() {
    let inline = InlineVec::<u8, Bytes>::from([1, 2, 3, 4, 5]);
    let h = HipVec::<u8, Arc>::from_inline(inline);
    assert_eq!(h.len(), 5);
    assert!(h.is_inline());

    let inline = InlineVec::<u8, PointerSize>::from([1, 2]);
    let h = HipVec::<u8, Arc>::from_inline(inline);
    assert_eq!(h.len(), 2);
    assert!(h.is_inline());
}

#[test]
#[should_panic(expected = "this vector cannot be inlined")]
#[allow(clippy::assertions_on_constants)]
fn from_inline_panic() {
    let inline = InlineVec::<u128, U32>::from([1]);
    assert!(!HipVec::<u128, Arc>::MAY_INLINE);
    let _h = HipVec::<u128, Arc>::from_inline(inline);
}

#[test]
fn from_vec() {
    let h = HipVec::<u8, Arc>::from(vec![]);
    assert_eq!(h.len(), 0);
    assert!(h.is_borrowed()); // for now, the empty hipvec is borrowed

    let h = HipVec::<u8, Arc>::from(vec![1, 2, 3, 4, 5]);
    assert_eq!(h.len(), 5);
    assert!(h.is_wide());
    assert_eq!(h.as_slice(), &[1, 2, 3, 4, 5]);

    let h = HipVec::<u8, Arc>::from(vec![42; 42]);
    assert_eq!(h.len(), 42);
    assert!(h.is_wide());
    assert_eq!(h.as_slice(), &[42; 42]);
}

#[test]
fn from_thin_vec() {
    let h = HipVec::<u8, Arc>::from(ThinVec::<u8, Reserved>::new());
    assert!(h.is_empty());
    assert!(h.is_borrowed()); // for now, the empty hipvec is borrowed

    let t = ThinVec::<u8, Reserved>::from_array([1, 2, 3]);
    let p = t.as_ptr();
    let h = HipVec::<u8, Arc>::from(t);
    assert!(h.is_thin());
    assert_eq!(h.as_slice(), &[1, 2, 3]);
    assert_eq!(h.as_ptr(), p);
}

#[test]
fn from_thin_vec_incompatible() {
    struct P(#[allow(unused)] [usize; 2]);
    impl ConstDefault for P {
        const DEFAULT: Self = Self([0; 2]);
    }

    let h = HipVec::<u8, Arc>::from(ThinVec::<u8, P>::new());
    assert!(h.is_empty());
    assert!(h.is_borrowed()); // for now, the empty hipvec is borrowed

    let t = ThinVec::<u8, P>::from_array([1, 2, 3]);
    let h = HipVec::<u8, Arc>::from(t);
    assert!(h.is_inline());
    assert_eq!(h.as_slice(), &[1, 2, 3]);

    let t = ThinVec::<u8, P>::from_array([42; 42]);
    let h = HipVec::<u8, Arc>::from(t);
    assert!(h.is_thin());
    assert_eq!(h.as_slice(), &[42; 42]);
}

#[test]
fn from_slice_clone() {
    let h = HipVec::<u8, Arc>::from([].as_slice());
    assert_eq!(h.len(), 0);
    assert!(h.is_borrowed()); // for now, the empty hipvec is borrowed

    let h = HipVec::<u8, Arc>::from([1, 2, 3, 4, 5].as_slice());
    assert_eq!(h.len(), 5);
    assert!(h.is_inline());
    assert_eq!(h.as_slice(), &[1, 2, 3, 4, 5]);

    let h = HipVec::<u8, Arc>::from([42; 42].as_slice());
    assert_eq!(h.len(), 42);
    assert!(h.is_thin());
    assert_eq!(h.as_slice(), &[42; 42]);
}

#[test]
fn from_slice_copy() {
    let h = HipVec::<u8, Arc>::from_slice_copy([].as_slice());
    assert_eq!(h.len(), 0);
    assert!(h.is_borrowed()); // for now, the empty hipvec is borrowed

    let h = HipVec::<u8, Arc>::from_slice_copy([1, 2, 3, 4, 5].as_slice());
    assert_eq!(h.len(), 5);
    assert!(h.is_inline());
    assert_eq!(h.as_slice(), &[1, 2, 3, 4, 5]);

    let h = HipVec::<u8, Arc>::from_slice_copy([42; 42].as_slice());
    assert_eq!(h.len(), 42);
    assert!(h.is_thin());
    assert_eq!(h.as_slice(), &[42; 42]);
}

#[test]
fn try_split_off() {
    let mut h = HipVec::<u8, Arc>::from([1, 2, 3, 4, 5]);
    let other = h.try_split_off(2).unwrap();
    assert_eq!(h.len(), 2);
    assert_eq!(h.as_slice(), &[1, 2]);
    assert!(h.is_inline());
    assert_eq!(other.len(), 3);
    assert_eq!(other.as_slice(), &[3, 4, 5]);
    assert!(other.is_inline());

    let mut h = HipVec::<u8, Arc>::from([42; 42]);
    let other = h.try_split_off(10).unwrap();
    assert_eq!(h.len(), 10);
    assert_eq!(h.as_slice(), &[42; 10]);
    assert!(h.is_thin());
    assert_eq!(other.len(), 32);
    assert_eq!(other.as_slice(), &[42; 32]);
    assert!(other.is_thin());
    assert_eq!(other.as_ptr(), unsafe { h.as_ptr().add(10) });

    let mut h = HipVec::<u8, Arc>::from([1, 2, 3, 4, 5]);
    let other = h.try_split_off(5).unwrap();
    assert!(other.is_empty());

    let mut h = HipVec::<u8, Arc>::from([1, 2, 3, 4, 5]);
    assert_eq!(h.try_split_off(6).unwrap_err(), SplitOffError::OutOfBounds);

    let mut h = HipVec::<u8, BoundedRc<1>>::from([42; 42]);
    assert_eq!(
        h.try_split_off(10).unwrap_err(),
        SplitOffError::RefCountOverflow
    );
}

#[test]
fn split_off() {
    let mut h = HipVec::<u8, Arc>::from([1, 2, 3, 4, 5]);
    let other = h.split_off(2);
    assert_eq!(h.len(), 2);
    assert_eq!(h.as_slice(), &[1, 2]);
    assert!(h.is_inline());
    assert_eq!(other.len(), 3);
    assert_eq!(other.as_slice(), &[3, 4, 5]);
    assert!(other.is_inline());

    let mut h = HipVec::<u8, Arc>::from([42; 42]);
    let other = h.split_off(10);
    assert_eq!(h.len(), 10);
    assert_eq!(h.as_slice(), &[42; 10]);
    assert!(h.is_thin());
    assert_eq!(other.len(), 32);
    assert_eq!(other.as_slice(), &[42; 32]);
    assert!(other.is_thin());
    assert_eq!(other.as_ptr(), unsafe { h.as_ptr().add(10) });

    let mut h = HipVec::<u8, Arc>::from([1, 2, 3, 4, 5]);
    let other = h.split_off(5);
    assert!(other.is_empty());
}

#[test]
#[should_panic(expected = "split index out of bounds")]
fn split_off_oob() {
    let mut h = HipVec::<u8, Arc>::from([1, 2, 3, 4, 5]);
    // should panic
    let _h2 = h.split_off(6);
}

#[test]
fn truncate() {
    let mut h = HipVec::<u8, Arc>::from([1, 2, 3, 4, 5]);
    h.truncate(3);
    assert_eq!(h.len(), 3);
    assert_eq!(h.as_slice(), &[1, 2, 3]);
    assert!(h.is_inline());

    let mut h = HipVec::<u8, Arc>::from([42; 42]);
    assert!(h.is_thin());
    let h2 = h.clone();
    assert!(h.is_thin());
    h.truncate(10);
    assert_eq!(h.len(), 10);
    assert_eq!(h.as_slice(), &[42; 10]);
    assert!(h.is_thin());
    assert_eq!(h2.as_slice(), &[42; 42]);
    assert!(h2.is_thin());
    assert_eq!(h2.as_ptr(), h.as_ptr());
}

#[test]
fn clear() {
    let mut h = HipVec::<i32, Arc>::new();
    h.clear();
    assert!(h.is_empty());

    let mut h = HipVec::<i32, Arc>::from([1, 2]);
    h.clear();
    assert!(h.is_empty());

    let mut h = HipVec::<i32, Arc>::from([42; 42]);
    h.clear();
    assert!(h.is_empty());

    let mut h = HipVec::<i32, Arc>::from([42; 42]);
    h.clear();
    assert!(h.is_empty());
}

#[test]
fn from_vector_normalized() {
    let h = HipVec::<u8, Arc>::from_vector_normalized(vec![]);
    assert_eq!(h.len(), 0);
    assert!(h.is_borrowed()); // for now, the empty hipvec is borrowed

    let h = HipVec::<u8, Arc>::from_vector_normalized(vec![1, 2, 3, 4, 5]);
    assert_eq!(h.len(), 5);
    assert!(h.is_inline());
    assert_eq!(h.as_slice(), &[1, 2, 3, 4, 5]);

    let h = HipVec::<u8, Arc>::from_vector_normalized(vec![42; 42]);
    assert_eq!(h.len(), 42);
    assert!(h.is_thin());
    assert_eq!(h.as_slice(), &[42; 42]);
}

#[test]
fn is_unique() {
    let b = HipVec::<u8, Arc>::borrowed(b"abc");
    assert!(b.is_borrowed());
    assert!(!b.is_unique());

    let i = HipVec::<u8, Arc>::from([1, 2, 3]);
    assert!(i.is_inline());
    assert!(i.is_unique());

    let t = HipVec::<u8, Arc>::from([42; 42]);
    assert!(t.is_thin());
    assert!(t.is_unique());
    let t2 = t.clone();
    assert!(!t.is_unique());
    assert!(!t2.is_unique());

    let f = HipVec::<u8, Arc>::from(vec![1; 100]);
    assert!(f.is_wide());
    assert!(f.is_unique());
    let f2 = f.clone();
    assert!(!f.is_unique());
    assert!(!f2.is_unique());
}

#[test]
fn pop() {
    let mut h = HipVec::<u8, Arc>::DEFAULT;
    assert_eq!(h.pop(), None);

    let mut h = HipVec::<u8, Arc>::from([1, 2, 3]);
    assert!(h.is_inline());
    assert_eq!(h.pop(), Some(3));
    assert_eq!(h.len(), 2);
    assert_eq!(h.as_slice(), &[1, 2]);
    assert!(h.is_inline());

    let mut h = HipVec::<u8, Arc>::from([42; 42]);
    assert!(h.is_thin());
    {
        let h2 = h.clone();
        assert!(h.is_thin());
        assert_eq!(h.pop(), Some(42));
        assert_eq!(h.len(), 41);
        assert_eq!(h.as_slice(), &[42; 41]);
        assert!(h.is_thin());
        assert_eq!(h2.as_slice(), &[42; 42]);
        assert!(h2.is_thin());
        assert_eq!(h2.as_ptr(), h.as_ptr());
    }
    assert_eq!(h.len(), 41);
    assert_eq!(h.pop(), Some(42));
    assert_eq!(h.len(), 40);
    assert_eq!(h.as_slice(), &[42; 40]);
    assert!(h.is_thin());

    let mut h = HipVec::<u8, Arc>::from(vec![42; 42]);
    assert!(h.is_wide());
    {
        let h2 = h.clone();
        assert!(h.is_wide());
        assert_eq!(h.pop(), Some(42));
        assert_eq!(h.len(), 41);
        assert_eq!(h.as_slice(), &[42; 41]);
        assert!(h.is_wide());
        assert_eq!(h2.as_slice(), &[42; 42]);
        assert!(h2.is_wide());
        assert_eq!(h2.as_ptr(), h.as_ptr());
    }
    assert_eq!(h.len(), 41);
    assert_eq!(h.pop(), Some(42));
    assert_eq!(h.len(), 40);
    assert_eq!(h.as_slice(), &[42; 40]);
    assert!(h.is_wide());

    let mut h = HipVec::<u8, Arc>::from([1, 2, 3]);
    assert_eq!(h.pop(), Some(3));
    assert_eq!(h.pop(), Some(2));
    assert_eq!(h.pop(), Some(1));
    assert_eq!(h.pop(), None);
    assert_eq!(h.len(), 0);
    assert!(h.as_slice().is_empty());
    assert!(h.is_inline());
}

#[test]
fn slice_inline() {
    let h = HipVec::<u8, Arc>::from([1, 2, 3, 4, 5]);
    assert!(h.is_inline());
    assert_eq!(h.as_slice(), &[1, 2, 3, 4, 5]);

    let h1 = h.slice(..);
    assert!(h1.is_inline());
    assert_eq!(h1.as_slice(), &[1, 2, 3, 4, 5]);

    let h2 = h.slice(1..4);
    assert!(h2.is_inline());
    assert_eq!(h2.as_slice(), &[2, 3, 4]);
}

#[test]
fn slice_thin() {
    let h = HipVec::<u8, Arc>::from([42; 42]);
    assert!(h.is_thin());
    assert_eq!(h.as_slice(), &[42; 42]);

    let h1 = h.slice(..);
    assert!(h1.is_thin());
    assert_eq!(h1.as_slice(), &[42; 42]);

    let h2 = h.slice(1..40);
    assert!(h2.is_thin());
    assert_eq!(h2.as_slice(), &[42; 39]);
}

#[test]
fn slice_unique() {
    let h = HipVec::<u8, Unique>::from([42; 42]);
    assert!(h.is_thin());
    assert_eq!(h.as_slice(), &[42; 42]);
    let h2 = h.slice(1..40);
    assert!(h2.is_thin());
    assert!(h.is_unique());
    assert!(h2.is_unique());
    assert_eq!(h2.as_slice(), &[42; 39]);
}

#[test]
fn slice_empty() {
    let h = HipVec::<u8, Arc>::new();
    assert!(h.is_empty());
    assert!(h.as_slice().is_empty());

    let h1 = h.slice(..);
    assert!(h1.is_empty());
    assert!(h1.as_slice().is_empty());

    let h = HipVec::<u8, Arc>::from([1, 2, 3]);
    let h2 = h.slice(1..1);
    assert!(h2.is_empty());
    assert!(h2.is_borrowed());
    assert!(h2.as_slice().is_empty());
}

#[test]
fn slice_unchecked() {
    let h = HipVec::<i32, Arc>::borrowed(&[1, 2, 3]);
    let _h2 = unsafe { h.slice_unchecked(..) };
    let _h3 = unsafe { h.slice_unchecked(1..) };
    let _h4 = unsafe { h.slice_unchecked(1..2) };
}

#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "start index 4 is out of bounds for slice of length 3")]
fn slice_unchecked_debug_panic() {
    let h = HipVec::<i32, Arc>::from([1, 2, 3]);
    let _h2 = unsafe { h.slice_unchecked(4..) };
}

#[test]
fn push() {
    let mut h = HipVec::<u8, Arc>::from([1, 2, 3]);
    h.push(4);
    assert_eq!(h.as_slice(), [1, 2, 3, 4]);

    let mut h = HipVec::<u8, Arc>::new();
    h.push(1);
    assert_eq!(h.as_slice(), [1]);

    let mut h = HipVec::<u8, Arc>::from([42; 42]);
    h.push(42);
    assert_eq!(h.as_slice(), [42; 43]);
}

#[test]
fn push_boxed() {
    let mut h = HipVec::<Box<u8>, Arc>::from([1].map(Box::new));
    h.push(Box::new(2));
    assert_eq!(h.as_slice(), [1, 2].map(Box::new));

    let mut h = HipVec::<Box<u8>, Arc>::new();
    h.push(Box::new(1));
    assert_eq!(h.as_slice(), [Box::new(1)]);

    let mut h = HipVec::<Box<u8>, Arc>::from([42; 42].map(Box::new));
    h.push(Box::new(42));
    assert_eq!(h.as_slice(), [42; 43].map(Box::new));
}

#[test]
fn push_copy() {
    let mut h = HipVec::<u8, Arc>::from([1, 2, 3]);
    h.push_copy(4);
    assert_eq!(h.as_slice(), [1, 2, 3, 4]);

    let mut h = HipVec::<u8, Arc>::new();
    h.push_copy(1);
    assert_eq!(h.as_slice(), [1]);

    let mut h = HipVec::<u8, Arc>::from([42; 42]);
    h.push_copy(42);
    assert_eq!(h.as_slice(), [42; 43]);
}

#[test]
fn inline_ptr_is_inline() {
    let h = HipVec::<u8, Arc>::from([1, 2, 3]);
    let start: *const u8 = ptr::from_ref(&h).cast();
    let end: *const u8 = ptr::from_ref(&h).wrapping_add(1).cast();
    assert!((start..end).contains(&h.as_ptr()));
}

#[test]
fn capacity_wide() {
    let v = Vec::from([42; 100]);
    let h = HipVec::<u8, Arc>::from(v);
    let cap = h.capacity();
    assert!(cap >= 100);

    let h2 = h.slice(10..60);
    assert_eq!(h2.capacity(), cap);
}

#[test]
fn capacity_thin() {
    let h = HipVec::<u8, Arc>::from([42; 100]);
    let cap = h.capacity();
    assert!(cap >= 100);

    let h2 = h.slice(10..60);
    assert_eq!(h2.capacity(), cap);
}

#[test]
fn capacity_inline() {
    let h = HipVec::<u8, Arc>::from([1, 2, 3, 4, 5]);
    assert_eq!(h.capacity(), HipVec::<u8, Arc>::INLINE_CAP);

    let h2 = h.slice(1..3);
    assert_eq!(h2.capacity(), HipVec::<u8, Arc>::INLINE_CAP);
}

#[test]
fn capacity_empty() {
    // for now, the emtpy hipvec is borrowed
    let h = HipVec::<u8, Arc>::new();
    assert_eq!(h.capacity(), 0);

    let h2 = h.slice(..);
    assert_eq!(h2.capacity(), 0);
}

#[test]
fn capacity_borrowed() {
    let h = HipVec::<u8, Arc>::borrowed(b"hello");
    assert_eq!(h.capacity(), h.len());

    let h2 = h.slice(1..4);
    assert_eq!(h2.capacity(), h2.len());
}

#[test]
fn shrink_to_fit_empty() {
    let mut h = HipVec::<u8, Arc>::with_capacity(42);
    h.shrink_to_fit();
    assert_eq!(h.capacity(), 0);
    assert!(h.is_borrowed()); // empty is borrowed
}

#[test]
fn shrink_to_fit_inline() {
    let mut h = HipVec::<u8, Arc>::with_capacity(42);
    {
        let mut m = h.mutate();
        m.extend_from_slice_copy(&[0; 8]);
        m.shrink_to_fit();
    }
    assert!(h.capacity() >= 8);
    assert_eq!(h.capacity(), Inline::<u8>::CAPACITY);
    assert!(h.is_inline());
}

#[test]
fn shrink_to_fit_thin() {
    let mut h = HipVec::<u8, Arc>::with_capacity(100);
    {
        let mut m = h.mutate();
        m.extend_from_slice_copy(&[0; 50]);
        m.shrink_to_fit();
    }
    assert!(h.capacity() >= 50);
    assert!(h.capacity() < 100);
    assert!(h.is_thin());
}

#[test]
fn shrink_to_fit_wide() {
    let mut v = Vec::with_capacity(100);
    v.extend_from_slice(&[0; 50]);
    let mut h = HipVec::<u8, Arc>::from(v);
    assert!(h.is_wide());
    {
        let mut m = h.mutate();
        m.shrink_to_fit();
    }
    assert!(h.capacity() >= 50);
    assert!(h.is_thin());
}

#[test]
fn shrink_to_noop_larger_cap() {
    let mut h = HipVec::<u8, Arc>::with_capacity(100);
    let old_capacity = h.capacity();
    {
        let mut m = h.mutate();
        m.extend_from_slice_copy(&[0; 50]);
        m.shrink_to(150);
    }
    assert_eq!(h.capacity(), old_capacity);
    assert!(h.is_thin());
}

#[test]
fn shrink_to_noop_larger_len() {
    let mut h = HipVec::<u8, Arc>::with_capacity(100);
    let old_capacity = h.capacity();
    {
        let mut m = h.mutate();
        m.extend_from_slice_copy(&[0; 100]);
        m.shrink_to(50);
    }
    assert_eq!(h.capacity(), old_capacity);
    assert!(h.is_thin());
}

#[test]
fn shrink_to_zero() {
    let mut h = HipVec::<u8, Arc>::with_capacity(100);
    {
        let mut m = h.mutate();
        m.shrink_to(0);
    }
    assert_eq!(h.capacity(), 0);
    assert!(h.is_borrowed()); // empty is borrowed
}

#[test]
fn shrink_to_inline() {
    let mut h = HipVec::<u8, Arc>::with_capacity(100);
    {
        let mut m = h.mutate();
        m.extend_from_slice_copy(&[0; 8]);
        m.shrink_to(10);
    }
    assert!(h.capacity() >= 8);
    assert!(h.is_inline());
    assert_eq!(h.capacity(), Inline::<u8>::CAPACITY);
}

#[test]
fn shrink_to_thin() {
    let mut h = HipVec::<u8, Arc>::with_capacity(100);
    {
        let mut m = h.mutate();
        m.extend_from_slice_copy(&[0; 50]);
        m.shrink_to(60);
    }
    assert!(h.capacity() >= 60);
    assert!(h.capacity() < 100);
    assert!(h.is_thin());
}

#[test]
fn shrink_to_wide() {
    let mut v = Vec::with_capacity(150);
    v.extend_from_slice(&[0; 80]);
    let mut h = HipVec::<u8, Arc>::from(v);
    assert!(h.is_wide());
    {
        let mut m = h.mutate();
        m.shrink_to(90);
    }
    assert!(h.capacity() >= 90);
    assert!(h.capacity() < 150);
    assert!(h.is_thin());
}

#[test]
fn as_mut_slice_unchecked() {
    let mut h = HipVec::<u8, Arc>::from([1, 2, 3, 4, 5]);
    let slice = unsafe { h.as_mut_slice_unchecked() };
    slice[0] = 42;
    assert_eq!(h.as_slice(), &[42, 2, 3, 4, 5]);
}

#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "vector must be uniquely owned")]
fn as_mut_slice_unchecked_panic_borrowed() {
    let mut h = HipVec::<u8, Arc>::borrowed(b"hello");
    let _slice = unsafe { h.as_mut_slice_unchecked() };
}

#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "vector must be uniquely owned")]
fn as_mut_slice_unchecked_panic_shared() {
    let mut h = HipVec::<u8, Arc>::from(vec![1, 2, 3, 4, 5]);
    let h2 = h.clone();
    assert!(!h.is_unique());
    let _slice = unsafe { h.as_mut_slice_unchecked() };
    let _ = h2;
}

#[test]
fn into_borrowed() {
    let h = HipVec::<u8, Arc>::borrowed(b"hello");
    let b = h.into_borrowed().unwrap();
    assert_eq!(b, b"hello");

    let h = HipVec::<u8, Arc>::from([1, 2, 3]);
    assert!(h.into_borrowed().is_err());
}

#[test]
fn into_borrowed_unchecked() {
    let h = HipVec::<u8, Arc>::borrowed(b"hello");
    let b = unsafe { h.into_borrowed_unchecked() };
    assert_eq!(b, b"hello");
}

#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "vector should be borrowed")]
fn into_borrowed_unchecked_panic() {
    let h = HipVec::<u8, Arc>::from([1, 2, 3]);
    let _b = unsafe { h.into_borrowed_unchecked() };
}

#[test]
fn as_borrowed() {
    let h = HipVec::<u8, Arc>::borrowed(b"hello");
    let b = h.as_borrowed().unwrap();
    assert_eq!(b, b"hello");

    let h = HipVec::<u8, Arc>::from([1, 2, 3]);
    assert!(h.as_borrowed().is_none());
}

#[test]
fn from_wide_vec() {
    let v = vec![1u8; 200];
    let wv = WideVec::<u8, Arc>::from(v);
    let h = HipVec::<u8, Arc>::from(wv);
    assert_eq!(h.len(), 200);
    assert!(h.is_wide());
    assert_eq!(h.as_slice(), &[1u8; 200]);

    let v = vec![];
    let wv = WideVec::<u8, Arc>::from(v);
    let h = HipVec::<u8, Arc>::from(wv);
    assert_eq!(h.len(), 0);
    assert!(h.is_nil());
    assert!(!h.is_allocated());
}

#[test]
fn is_trimmed() {
    let h = HipVec::<u8, Arc>::new();
    assert!(h.is_trimmed());

    let h = HipVec::<u8, Arc>::from(vec![1, 2, 3]);
    assert!(h.is_allocated());
    assert!(h.is_trimmed());

    {
        let h2 = h.slice(0..2);
        assert!(!h2.is_trimmed());
    }

    {
        let h3 = h.slice(1..3);
        assert!(!h3.is_trimmed());
    }

    {
        let h4 = h.clone();
        assert!(h4.is_trimmed());
    }
}

#[test]
fn as_mut_ptr() {
    let mut h = HipVec::<u8, Arc>::new();
    assert_eq!(h.as_mut_ptr().unwrap(), ptr::dangling_mut());

    let mut h = HipVec::<u8, Arc>::from([1_u8, 2, 3]);
    {
        let p = h.as_mut_ptr().unwrap();
        unsafe {
            *p = 0;
        }
    }
    assert_eq!(h.as_slice(), [0_u8, 2, 3]);

    let mut h = HipVec::<u8, Arc>::from([0; 42]);
    {
        let p = h.as_mut_ptr().unwrap();
        unsafe {
            *p = 1;
        }
    }
    assert_eq!(h[0], 1);

    let mut h = HipVec::<u8, Arc>::borrowed(b"abc");
    assert!(h.as_mut_ptr().is_none());

    let mut h1 = HipVec::<u8, Arc>::from([42; 42]);
    let _h2 = h1.clone();
    assert!(h1.as_mut_ptr().is_none());
}

#[test]
#[should_panic(expected = "vector must be uniquely owned")]
fn as_mut_ptr_unchecked_debug_check() {
    let mut h = HipVec::<u8, Arc>::from(vec![1, 2, 3]);
    let _h2 = h.clone();
    assert!(!h.is_unique());
    let _p = unsafe { h.as_mut_ptr_unchecked() };
}

#[test]
fn as_mut_slice() {
    let mut h = HipVec::<u8, Arc>::borrowed(b"abc");
    assert!(h.as_mut_slice().is_none());

    let mut h = HipVec::<u8, Arc>::new();
    assert!(h.is_nil());
    assert!(h.as_mut_slice().unwrap().is_empty());

    let mut h = HipVec::<u8, Arc>::from([1, 2, 3]);
    assert!(h.is_inline());
    assert_eq!(h.as_mut_slice().unwrap(), &mut [1, 2, 3]);

    let mut h = HipVec::<u8, Arc>::from(vec![1, 2, 3]);
    assert!(h.is_wide());
    assert_eq!(h.as_mut_slice().unwrap(), &mut [1, 2, 3]);

    let mut h = HipVec::<u8, Arc>::from([0; 42]);
    h.truncate(3);
    assert!(h.is_thin());
    assert_eq!(h.as_mut_slice().unwrap(), &mut [0, 0, 0]);
}

#[test]
fn to_mut_slice() {
    let mut h = HipVec::<u8, Arc>::new();
    assert!(h.to_mut_slice().is_empty());

    let mut h = HipVec::<u8, Arc>::from([1, 2, 3]);
    assert_eq!(h.to_mut_slice(), [1, 2, 3]);

    let mut h = HipVec::<u8, Arc>::from([42; 42]);
    assert_eq!(h.to_mut_slice(), [42; 42]);

    let mut h2 = h.clone();
    assert!(!h.is_unique());
    assert!(!h2.is_unique());
    h2.to_mut_slice().fill(41);
    assert_eq!(h2.as_slice(), [41; 42]);
    assert!(h.is_unique());
    assert!(h2.is_unique());
}

#[test]
fn to_mut_slice_copy() {
    let mut h = HipVec::<u8, Arc>::new();
    assert!(h.to_mut_slice_copy().is_empty());

    let mut h = HipVec::<u8, Arc>::from([1, 2, 3]);
    assert_eq!(h.to_mut_slice_copy(), [1, 2, 3]);

    let mut h = HipVec::<u8, Arc>::from([42; 42]);
    assert_eq!(h.to_mut_slice_copy(), [42; 42]);

    let mut h2 = h.clone();
    assert!(!h.is_unique());
    assert!(!h2.is_unique());
    h2.to_mut_slice_copy().fill(41);
    assert_eq!(h2.as_slice(), [41; 42]);
    assert!(h.is_unique());
    assert!(h2.is_unique());
}

#[test]
fn repeat() {
    let h1 = HipVec::<u8, Arc>::new();
    let h2 = h1.repeat(5);
    assert_eq!(h2.len(), 0);

    let h1 = HipVec::<u8, Arc>::from([1, 2, 3]);
    let h2 = h1.repeat(3);
    assert_eq!(h2.as_slice(), [1, 2, 3, 1, 2, 3, 1, 2, 3]);

    let h1 = HipVec::<u8, Arc>::from([0; 7]);
    let h2 = h1.repeat(10);
    assert_eq!(h2.len(), 70);

    let h1 = HipVec::<u8, Arc>::from([42; 42]);
    let h2 = h1.repeat(2);
    assert_eq!(h2.as_slice(), [42; 84]);
    let h3 = h1.repeat(0);
    assert_eq!(h3.len(), 0);
    let h4 = h1.repeat(1);
    assert_eq!(h4.as_slice(), [42; 42]);
    assert_eq!(h1.as_ptr(), h4.as_ptr());
}

#[test]
fn repeat_copy() {
    let h1 = HipVec::<u8, Arc>::new();
    let h2 = h1.repeat_copy(5);
    assert_eq!(h2.len(), 0);

    let h1 = HipVec::<u8, Arc>::from([1, 2, 3]);
    let h2 = h1.repeat_copy(3);
    assert_eq!(h2.as_slice(), [1, 2, 3, 1, 2, 3, 1, 2, 3]);

    let h1 = HipVec::<u8, Arc>::from([0; 7]);
    let h2 = h1.repeat_copy(10);
    assert_eq!(h2.len(), 70);

    let h1 = HipVec::<u8, Arc>::from([42; 42]);
    let h2 = h1.repeat_copy(2);
    assert_eq!(h2.as_slice(), [42; 84]);
    let h3 = h1.repeat_copy(0);
    assert_eq!(h3.len(), 0);
    let h4 = h1.repeat_copy(1);
    assert_eq!(h4.as_slice(), [42; 42]);
    assert_eq!(h1.as_ptr(), h4.as_ptr());
}

#[test]
fn spare_capacity_mut() {
    #[track_caller]
    fn fill(n: usize) {
        let mut h = HipVec::<u8, Arc>::with_capacity(n);
        {
            let spare = h.spare_capacity_mut();
            assert!(spare.len() >= n);
            spare.fill(MaybeUninit::new(42));
        }
        unsafe {
            h.set_len(n);
        }
        assert_eq!(h.as_slice(), vec![42; n].as_slice());
    }

    #[track_caller]
    fn fill_vec(n: usize) {
        let mut h = HipVec::<u8, Arc>::from(Vec::with_capacity(n));
        {
            let spare = h.spare_capacity_mut();
            assert!(spare.len() >= n);
            spare.fill(MaybeUninit::new(42));
        }
        unsafe {
            h.set_len(n);
        }
        assert_eq!(h.as_slice(), vec![42; n].as_slice());
    }

    fill(0);
    fill(5);
    fill(42);
    fill(100);

    fill_vec(0);
    fill_vec(5);
    fill_vec(42);
    fill_vec(100);

    let mut h = HipVec::<u8, Arc>::from([42; 42]);
    let _h = h.clone();
    assert!(h.spare_capacity_mut().is_empty());
}

#[test]
fn slice_ref_copy() {
    // test with inline vector
    let h = HipVec::<u8, Arc>::from([1, 2, 3, 4, 5]);
    let slice = h.as_slice();
    let sr = h.slice_ref_copy(&slice[1..]).unwrap();
    assert_eq!(sr.as_slice(), &[2, 3, 4, 5]);

    let empty = h.slice_ref_copy(&slice[0..0]).unwrap();
    assert!(empty.as_slice().is_empty());

    assert!(h.slice_ref_copy(b"abc").is_none());

    // test with large vector
    let h = HipVec::<u8, Arc>::from([42; 100]);
    let slice = h.as_slice();
    let sr = h.slice_ref_copy(&slice[10..90]).unwrap();
    assert_eq!(sr.as_slice(), &[42; 80]);

    assert!(h.slice_ref_copy(&[42; 100]).is_none());

    // test with large vector (Unique)
    let h = HipVec::<u8, Unique>::from([42; 100]);
    let slice = h.as_slice();
    let sr = h.slice_ref_copy(&slice[10..90]).unwrap();
    assert_eq!(sr.as_slice(), &[42; 80]);

    // test with borrowed vector
    let h = HipVec::<u8, Arc>::borrowed(b"hello world");
    let slice = h.as_slice();
    let sr = h.slice_ref_copy(&slice[6..]).unwrap();
    assert_eq!(sr.as_slice(), b"world");
}
