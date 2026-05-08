use alloc::boxed::Box;
use alloc::string::String;
use core::cell::Cell;

use super::TryReserveError;
use crate::inline::InlineVec as V;
use crate::inline::layouts::{BasicLayout, Layout};
use crate::inline_vec as v;

#[test]
fn niche() {
    assert_eq!(size_of::<Option<V<()>>>(), size_of::<V<()>>());
    assert_eq!(size_of::<Option<V<i32>>>(), size_of::<V<i32>>());
    assert_eq!(size_of::<Option<V<i128>>>(), size_of::<V<i128>>());
}

#[test]
fn new() {
    let mut l = V::<i32>::new();
    assert_eq!(l.len(), 0);
    l.push(1);
    assert_eq!(l.len(), 1);
    assert_eq!(l.as_slice(), &[1]);
}

#[test]
fn as_ptr() {
    let mut l = V::<u8>::new();
    let p = l.as_ptr();
    assert_eq!(p, l.as_mut_ptr());
    assert_eq!(p, l.as_non_null().as_ptr());
}

#[test]
fn dst() {
    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
    struct Dst;

    assert_eq!(size_of::<Dst>(), 0);

    let mut l = V::<Dst>::new();
    assert_eq!(l.len(), 0);

    l.push(Dst);
    l.push(Dst);
    l.push(Dst);
    assert_eq!(l.len(), 3);

    assert_eq!(l.as_slice(), &[Dst, Dst, Dst]);

    assert_eq!(l.pop(), Some(Dst));
    assert_eq!(l.pop(), Some(Dst));
    assert_eq!(l.pop(), Some(Dst));
    assert_eq!(l.pop(), None);
    assert_eq!(l.len(), 0);

    assert_eq!(<BasicLayout as Layout<()>>::CAPACITY, usize::MAX >> 1);
    assert_eq!(V::<Dst>::CAPACITY, usize::MAX >> 1);
    assert_eq!(l.capacity(), usize::MAX >> 1);
}

#[test]
fn slice() {
    let mut l = V::<i32>::new();
    l.push(1);
    l.push(2);
    l.push(3);
    assert_eq!(l.as_slice(), &[1, 2, 3]);
    let slice = l.as_mut_slice();
    assert_eq!(slice, &[1, 2, 3]);
    slice[0] = 4;
    slice[1] = 5;
    slice[2] = 6;
    assert_eq!(l.as_slice(), &[4, 5, 6]);
}

#[test]
fn push_mut() {
    let mut l = V::<u8>::with_capacity(1);
    let p = l.as_ptr();
    let x = l.push_mut(42);
    assert_eq!(x, &42);
    assert_eq!(&raw const *x, p);
    *x += 1;
    assert_eq!(l.as_slice(), &[43]);
}

#[test]
#[should_panic(expected = "new length exceeds capacity")]
fn push_mut_panic() {
    let mut l = V::<u8>::new();
    let cap = l.capacity();
    for i in 0..cap {
        let _ = l.push_mut(i as u8);
    }
    let _ = l.push_mut(0);
}

#[test]
fn push_within_capacity() {
    let mut l = V::<u8>::new();
    let capacity = l.capacity() as u8;
    for i in 0..capacity {
        assert_eq!(l.push_within_capacity(i).unwrap(), &i);
    }
    assert_eq!(l.push_within_capacity(capacity), Err(capacity));
}

#[test]
fn push_within_capacity_boxed() {
    let mut l = V::<Box<usize>>::new();
    let capacity = l.capacity();
    for i in 0..capacity {
        assert_eq!(l.push_within_capacity(Box::new(i)).unwrap(), &Box::new(i));
    }
    assert_eq!(
        l.push_within_capacity(Box::new(capacity)),
        Err(Box::new(capacity))
    );
}

#[test]
fn insert() {
    let mut v = V::new();
    v.insert(0, 2_u8);
    assert_eq!(v.as_slice(), [2]);
    v.insert(0, 1);
    assert_eq!(v.as_slice(), [1, 2]);
    v.insert(2, 4);
    assert_eq!(v.as_slice(), [1, 2, 4]);
    v.insert(2, 3);
    assert_eq!(v.as_slice(), [1, 2, 3, 4]);
}

#[test]
#[should_panic(expected = "new length exceeds capacity")]
fn insert_panic_overflow() {
    let mut v: V<u8> = V::new();
    for i in 0..v.capacity() {
        v.insert(0, (i + 1) as u8);
    }
    v.insert(0, 0);
}

#[test]
#[should_panic(expected = "index out of bounds")]
fn insert_panic_out_of_bounds() {
    let mut v = v![1_u8, 2];
    v.insert(4, 5);
}

#[test]
fn insert_mut() {
    let mut v = V::new();
    {
        let r = v.insert_mut(0, 42_u8);
        assert_eq!(*r, 42);
        *r = 2;
        assert_eq!(v.as_slice(), [2]);
    }
    {
        let r = v.insert_mut(0, 42);
        assert_eq!(*r, 42);
        *r = 1;
        assert_eq!(v.as_slice(), [1, 2]);
    }
    let _ = v.insert_mut(2, 4);
    assert_eq!(v.as_slice(), [1, 2, 4]);
    let _ = v.insert_mut(2, 3);
    assert_eq!(v.as_slice(), [1, 2, 3, 4]);
}

#[test]
fn drop() {
    struct DropCounter<'a>(&'a Cell<usize>);
    impl Drop for DropCounter<'_> {
        fn drop(&mut self) {
            self.0.set(self.0.get() + 1);
        }
    }

    let count = Cell::new(0);
    {
        let mut l = V::<DropCounter<'_>>::new();
        assert_eq!(l.len(), 0);
        l.push(DropCounter(&count));
        assert_eq!(l.len(), 1);
        l.push(DropCounter(&count));
        assert_eq!(l.len(), 2);
        assert_eq!(count.get(), 0);
    }
    assert_eq!(count.get(), 2);
}

#[test]
fn capacity() {
    let l = V::<i32>::new();
    assert_eq!(V::<i32>::CAPACITY, <BasicLayout as Layout<i32>>::CAPACITY);
    assert_eq!(l.capacity(), V::<i32>::CAPACITY);
    assert_eq!(l.len(), 0);

    let mut l = V::<i32>::new();
    for i in 0..l.capacity() {
        l.push(i as i32);
        assert_eq!(l.len(), i + 1);
    }
    assert_eq!(l.len(), l.capacity());
}

#[test]
#[should_panic(expected = "new length exceeds capacity")]
fn push_panic() {
    let mut l = V::<i32>::new();
    for i in 0..=l.capacity() {
        l.push(i as i32);
    }
}

#[test]
fn from_array() {
    let l = V::<i32>::from([1, 2, 3]);
    assert_eq!(l.as_slice(), &[1, 2, 3]);
}

#[test]
fn from_array_empty() {
    let l = V::<i32>::from([]);
    assert!(l.as_slice().is_empty());
}

#[test]
#[should_panic(expected = "required capacity exceeds maximum")]
fn from_array_panic() {
    let _ = V::<i32>::from([0; <BasicLayout as Layout<i32>>::CAPACITY + 1]);
}

#[test]
fn clear() {
    let mut l = V::<u8>::from([1, 2, 3]);

    l.clear();
    assert!(l.is_empty());

    l.clear();
    assert!(l.is_empty());

    let mut l = V::<u8>::new();
    l.clear();
    assert!(l.is_empty());
}

#[test]
fn truncate() {
    let mut l = v![1_u8, 2, 3, 4];
    l.truncate(6);
    assert_eq!(l.as_slice(), [1, 2, 3, 4]);

    l.truncate(2);
    assert_eq!(l.as_slice(), [1, 2]);

    l.truncate(0);
    assert!(l.is_empty());
}

#[test]
fn split_off() {
    let mut l: V<u8> = v![1, 2, 3];
    let cap = l.capacity();
    let w = l.split_off(2);
    assert_eq!(l.as_slice(), [1, 2]);
    assert_eq!(w.as_slice(), [3]);
    assert_eq!(l.capacity(), cap);

    let mut l: V<u8> = v![1, 2, 3];
    let w = l.split_off(0);
    assert!(l.is_empty());
    assert_eq!(w.as_slice(), [1, 2, 3]);

    let mut l: V<u8> = v![1, 2, 3];
    let w = l.split_off(3);
    assert_eq!(l.as_slice(), [1, 2, 3]);
    assert!(w.is_empty());
}

#[test]
#[should_panic(expected = "index out of bounds")]
fn split_off_panic() {
    let mut l: V<u8> = v![1, 2, 3];
    let _ = l.split_off(4);
}

#[test]
fn resize() {
    let mut l = v![1_u8, 2];

    l.resize(5, 9);
    assert_eq!(l.as_slice(), [1, 2, 9, 9, 9]);

    l.resize(3, 0);
    assert_eq!(l.as_slice(), [1, 2, 9]);

    l.resize(0, 0);
    assert!(l.is_empty());
}

#[test]
fn drain() {
    let mut v: V<u8> = v![1, 2, 3, 4, 5];
    let drain = v.drain(1..4);
    assert_eq!(drain.as_slice(), [2, 3, 4]);
    assert!(drain.eq([2, 3, 4]));
    assert_eq!(v.as_slice(), [1, 5]);

    let mut v: V<u8> = v![1, 2, 3, 4, 5];
    assert!(v.drain(..).eq([1, 2, 3, 4, 5]));
    assert!(v.is_empty());
    assert_eq!(v.as_slice(), []);

    let mut v: V<u8> = v![1, 2, 3, 4, 5];
    assert_eq!(v.drain(2..2).count(), 0);
    assert_eq!(v.as_slice(), [1, 2, 3, 4, 5]);
}

#[test]
#[should_panic]
#[allow(clippy::reversed_empty_ranges)]
fn drain_invalid_range_panics() {
    let mut v: V<u8> = v![1, 2, 3, 4, 5];
    let _ = v.drain(4..1);
}

#[test]
#[cfg(feature = "std")]
fn resize_drop() {
    use std::sync::Mutex;

    #[derive(Clone)]
    struct X(#[allow(unused)] u8);
    impl Drop for X {
        fn drop(&mut self) {
            *DROP_COUNT.lock().unwrap() += 1;
        }
    }

    static TEST_MUTEX: Mutex<()> = Mutex::new(());
    static DROP_COUNT: Mutex<usize> = Mutex::new(0);

    let _mutex = TEST_MUTEX.lock().unwrap();

    let mut l = v![X(1), X(2)];
    l.resize(0, X(0));
    assert_eq!(*DROP_COUNT.lock().unwrap(), 3);
}

#[test]
fn resize_with() {
    let mut next = 2_u8;
    let mut l = v![1_u8];

    l.resize_with(4, || {
        let value = next;
        next += 2;
        value
    });
    assert_eq!(l.as_slice(), [1, 2, 4, 6]);

    l.resize_with(2, || unreachable!());
    assert_eq!(l.as_slice(), [1, 2]);
}

#[test]
fn remove() {
    let mut l = V::<i32>::from([10, 20, 30, 40]);
    let removed = l.remove(1);
    assert_eq!(removed, 20);
    assert_eq!(l.as_slice(), &[10, 30, 40]);
}

#[test]
fn remove_first() {
    let mut l = V::<i32>::from([10, 20, 30, 40]);
    let removed = l.remove(0);
    assert_eq!(removed, 10);
    assert_eq!(l.as_slice(), &[20, 30, 40]);
}

#[test]
fn remove_last() {
    let mut l = V::<i32>::from([10, 20, 30, 40]);
    let removed = l.remove(l.len() - 1);
    assert_eq!(removed, 40);
    assert_eq!(l.as_slice(), &[10, 20, 30]);
}

#[test]
#[should_panic(expected = "index out of bounds")]
fn remove_panic() {
    let mut l = V::<i32>::from([1, 2, 3]);
    let _ = l.remove(3);
}

#[test]
fn swap_remove() {
    let mut l = V::<i32>::from([10, 20, 30, 40]);
    let removed = l.swap_remove(1);
    assert_eq!(removed, 20);
    assert_eq!(l.as_slice(), &[10, 40, 30]);
}

#[test]
fn swap_remove_first() {
    let mut l = V::<i32>::from([10, 20, 30, 40]);
    let removed = l.swap_remove(0);
    assert_eq!(removed, 10);
    assert_eq!(l.as_slice(), &[40, 20, 30]);
}

#[test]
fn swap_remove_last() {
    let mut l = V::<i32>::from([10, 20, 30, 40]);
    let removed = l.swap_remove(l.len() - 1);
    assert_eq!(removed, 40);
    assert_eq!(l.as_slice(), &[10, 20, 30]);
}

#[test]
#[should_panic(expected = "index out of bounds")]
fn swap_remove_panic() {
    let mut l = V::<i32>::from([1, 2, 3]);
    let _ = l.swap_remove(3);
}

#[test]
fn from_slice() {
    let l = V::<i32>::from([1, 2, 3].as_slice());
    assert_eq!(l.as_slice(), &[1, 2, 3]);
}

#[test]
fn extend_from_slice() {
    let mut l = V::<i32>::from([1, 2]);

    l.extend_from_slice(&[3, 4]);
    assert_eq!(l.as_slice(), &[1, 2, 3, 4]);

    l.extend_from_slice(&[]);
    assert_eq!(l.as_slice(), &[1, 2, 3, 4]);
}

#[test]
#[should_panic(expected = "new length exceeds capacity")]
fn extend_from_slice_panic() {
    let mut l = V::<i32>::new();
    let too_many = [0; <BasicLayout as Layout<i32>>::CAPACITY + 1];
    l.extend_from_slice(&too_many);
}

#[test]
fn append() {
    let cap = V::<Box<u8>>::new().capacity();
    assert!(cap > 0);

    let mut left = V::<Box<u8>>::new();
    let mut expected = alloc::vec![];
    if cap > 1 {
        left.push(Box::new(1));
        expected.push(Box::new(1));
    }
    let mut right = V::<Box<u8>>::new();
    right.push(Box::new(2));
    expected.push(Box::new(2));
    left.append(&mut right);
    assert_eq!(left.as_slice(), expected.as_slice());
    assert!(right.is_empty());

    let mut left = V::<Box<u8>>::new();
    let mut expected = alloc::vec![];
    if cap > 1 {
        left.push(Box::new(3));
        expected.push(Box::new(3));
    }
    let mut right = alloc::vec![Box::new(4)];
    expected.push(Box::new(4));
    left.append(&mut right);
    assert_eq!(left.as_slice(), expected.as_slice());
    assert!(right.is_empty());

    let mut left = V::<Box<u8>>::new();
    let mut expected = alloc::vec![];
    if cap > 1 {
        left.push(Box::new(5));
        expected.push(Box::new(5));
    }
    let mut right = crate::thin_vec![Box::new(6)];
    expected.push(Box::new(6));
    left.append(&mut right);
    assert_eq!(left.as_slice(), expected.as_slice());
    assert!(right.is_empty());
}

#[test]
#[should_panic(expected = "new length exceeds capacity")]
fn append_panic() {
    let mut left = V::<String>::new();
    let cap = left.capacity();
    for _ in 0..(cap / 2 + 1) {
        left.push(String::from("l"));
    }

    let mut right = V::<String>::new();
    for _ in 0..(cap - left.len() + 1) {
        right.push(String::from("r"));
    }

    left.append(&mut right);
}

#[test]
fn const_append() {
    let cap = V::<Box<u8>>::new().capacity();
    assert!(cap > 0);

    let mut left = V::<Box<u8>>::new();
    let mut expected = alloc::vec![];
    if cap > 1 {
        left.push(Box::new(1));
        expected.push(Box::new(1));
    }
    let ptr = left.as_ptr();
    let mut right = V::<Box<u8>>::new();
    right.push(Box::new(2));
    expected.push(Box::new(2));
    left.const_append(&mut right);

    assert_eq!(left.as_slice(), expected.as_slice());
    assert_eq!(left.as_ptr(), ptr);
    assert!(right.is_empty());
}

#[test]
#[should_panic(expected = "new length exceeds capacity")]
fn const_append_panic() {
    let mut left = V::<String>::new();
    let cap = left.capacity();
    for _ in 0..(cap / 2 + 1) {
        left.push(String::from("l"));
    }

    let mut right = V::<String>::new();
    for _ in 0..(cap - left.len() + 1) {
        right.push(String::from("r"));
    }

    left.const_append(&mut right);
}

#[test]
fn with_capacity() {
    let l = V::<i32>::with_capacity(0);
    assert!(l.is_empty());
    assert_eq!(l.capacity(), V::<i32>::CAPACITY);

    let l = V::<i32>::with_capacity(V::<i32>::CAPACITY);
    assert!(l.is_empty());
}

#[test]
#[should_panic(expected = "capacity overflow")]
fn with_capacity_panic() {
    let _ = V::<i32>::with_capacity(V::<i32>::CAPACITY + 1);
}

#[test]
fn inline_vec_empty() {
    let l: V<i32> = v![];
    assert!(l.is_empty());
}

#[test]
fn inline_vec_list() {
    let l: V<i32> = v![1, 2, 3];
    assert_eq!(l.as_slice(), &[1, 2, 3]);
}

#[test]
fn inline_vec_list_trailing_comma() {
    let l: V<i32> = v![1, 2, 3,];
    assert_eq!(l.as_slice(), &[1, 2, 3]);
}

#[test]
fn inline_vec_repeat() {
    let l: V<i32> = v![7; 3];
    assert_eq!(l.as_slice(), &[7, 7, 7]);
}

#[test]
fn inline_vec_repeat_zero() {
    let mut side_effect = 0usize;
    let l: V<i32> = v![{ side_effect += 1; 42 }; 0];
    assert!(l.is_empty());
    assert_eq!(side_effect, 1);
}

#[test]
fn splice() {
    let mut v = v![1_u8, 2, 3, 4, 5];
    {
        let splice = v.splice(1..4, [9, 8]);
        assert!(splice.eq([2, 3, 4]));
    }
    assert_eq!(v.as_slice(), [1, 9, 8, 5]);

    let mut v = v![1_u8, 2, 3, 4, 5];
    {
        let splice = v.splice(1..3, [9, 8, 7, 6]);
        assert!(splice.eq([2, 3]));
    }
    assert_eq!(v.as_slice(), [1, 9, 8, 7, 6, 4, 5]);

    let mut v = v![1_u8, 2, 3, 4, 5];
    {
        let splice = v.splice(1..4, [9, 8, 7, 6].into_iter().filter(|_| true));
        assert!(splice.eq([2, 3, 4]));
    }
    assert_eq!(v.as_slice(), [1, 9, 8, 7, 6, 5]);

    let mut v = v![1_u8, 5];
    {
        let splice = v.splice(1..1, [2, 3, 4]);
        assert!(splice.eq([]));
    }
    assert_eq!(v.as_slice(), [1, 2, 3, 4, 5]);

    let mut v = v![1_u8, 2, 3, 4, 5];
    {
        let splice = v.splice(.., [9, 8]);
        assert!(splice.eq([1, 2, 3, 4, 5]));
    }
    assert_eq!(v.as_slice(), [9, 8]);

    let mut v = v![1_u8, 2, 3, 4, 5];
    {
        let splice = v.splice(.., []);
        assert!(splice.eq([1, 2, 3, 4, 5]));
    }
    assert!(v.is_empty());
}

#[test]
fn splice_boxed() {
    let mut v: V<Box<u8>> = v![Box::new(1)];
    {
        let splice = v.splice(.., [Box::new(2)]);
        assert!(splice.eq([Box::new(1)]));
    }
    assert_eq!(v.as_slice(), [Box::new(2)]);
}

#[test]
#[should_panic(expected = "start index 4 is greater than end index 1")]
#[allow(clippy::reversed_empty_ranges)]
fn splice_invalid_range_panics() {
    let mut v = v![1_u8, 2, 3, 4, 5];
    let _ = v.splice(4..1, [9, 8]);
}

#[test]
fn extend() {
    let mut v = V::<u8>::new();
    v.extend(std::iter::empty());
    assert!(v.as_slice().is_empty());

    v.extend([1, 2, 3]);
    assert_eq!(v.as_slice(), &[1, 2, 3]);

    v.extend([4, 5, 6].into_iter().filter(|_| true));
    assert_eq!(v.as_slice(), &[1, 2, 3, 4, 5, 6]);
}

#[test]
fn extend_boxed() {
    let mut v = V::<Box<i32>>::new();
    v.extend(std::iter::empty());
    assert!(v.as_slice().is_empty());

    v.extend([Box::new(1)]);
    assert_eq!(v.as_slice(), &[Box::new(1)]);

    v.extend([Box::new(2)].into_iter().filter(|_| true));
    assert_eq!(v.as_slice(), &[Box::new(1), Box::new(2)]);
}

#[test]
fn reserve() {
    let mut v = V::<u8>::new();
    assert_eq!(v.capacity(), V::<u8>::CAPACITY);
    v.reserve(5);
    assert_eq!(v.capacity(), V::<u8>::CAPACITY);
}

#[test]
#[should_panic(expected = "new length exceeds capacity")]
fn reserve_panic() {
    let mut v = V::<u8>::new();
    let cap = v.capacity();
    v.reserve(cap + 1);
}

#[test]
fn reserve_exact() {
    let mut v = V::<u8>::new();
    assert_eq!(v.capacity(), V::<u8>::CAPACITY);
    v.reserve_exact(5);
    assert_eq!(v.capacity(), V::<u8>::CAPACITY);
}

#[test]
#[should_panic(expected = "new length exceeds capacity")]
fn reserve_exact_panic() {
    let mut v = V::<u8>::new();
    let cap = v.capacity();
    v.reserve_exact(cap + 1);
}

#[test]
fn try_reserve() {
    let mut v = V::<u8>::new();
    assert_eq!(v.capacity(), V::<u8>::CAPACITY);
    assert_eq!(v.try_reserve(5), Ok(()));
    assert_eq!(v.capacity(), V::<u8>::CAPACITY);
    assert_eq!(v.try_reserve(v.capacity() + 1), Err(TryReserveError()));
}

#[test]
fn try_reserve_exact() {
    let mut v = V::<u8>::new();
    assert_eq!(v.capacity(), V::<u8>::CAPACITY);
    assert_eq!(v.try_reserve_exact(5), Ok(()));
    assert_eq!(v.capacity(), V::<u8>::CAPACITY);
    assert_eq!(
        v.try_reserve_exact(v.capacity() + 1),
        Err(TryReserveError())
    );
}
