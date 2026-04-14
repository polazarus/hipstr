use crate::common::tests::pointer_stability;
use crate::copy_thin_vec;
use crate::thin::CopyThinVec;

#[test]
fn new_and_default() {
    let new: CopyThinVec<i32> = CopyThinVec::new();
    assert!(new.is_empty());
    assert_eq!(new.len(), 0);

    let default: CopyThinVec<i32> = CopyThinVec::default();
    assert!(default.is_empty());
    assert_eq!(default.len(), 0);
}

#[test]
fn with_capacity() {
    let v: CopyThinVec<i32> = CopyThinVec::with_capacity(0);
    assert!(v.is_empty());
    assert_eq!(v.capacity(), 0);

    let v: CopyThinVec<i32> = CopyThinVec::with_capacity(8);
    assert!(v.is_empty());
    assert!(v.capacity() >= 8);
}

#[test]
fn from_array_and_slice() {
    let from_array: CopyThinVec<i32> = CopyThinVec::from([1, 2, 3]);
    assert_eq!(from_array.as_slice(), &[1, 2, 3]);

    let from_slice: CopyThinVec<i32> = CopyThinVec::from([4, 5, 6].as_slice());
    assert_eq!(from_slice.as_slice(), &[4, 5, 6]);
}

#[test]
fn macro_constructors() {
    let empty: CopyThinVec<i32> = copy_thin_vec![];
    assert!(empty.is_empty());

    let list: CopyThinVec<i32> = copy_thin_vec![1, 2, 3,];
    assert_eq!(list.as_slice(), &[1, 2, 3]);

    let repeated: CopyThinVec<i32> = copy_thin_vec![7; 3];
    assert_eq!(repeated.as_slice(), &[7, 7, 7]);
}

#[test]
fn push_pop() {
    let mut v: CopyThinVec<i32> = CopyThinVec::new();
    assert_eq!(v.pop(), None);

    v.push(10);
    v.push(20);
    v.push(30);
    assert_eq!(v.as_slice(), &[10, 20, 30]);

    assert_eq!(v.pop(), Some(30));
    assert_eq!(v.pop(), Some(20));
    assert_eq!(v.pop(), Some(10));
    assert_eq!(v.pop(), None);

    assert!(v.is_empty());
}

#[test]
fn as_slice() {
    let v: CopyThinVec<i32> = copy_thin_vec![1, 2, 3];
    assert_eq!(v.as_slice(), &[1, 2, 3]);
}

#[test]
fn deref() {
    let v: CopyThinVec<i32> = copy_thin_vec![1, 2, 3];
    let slice: &[i32] = &v;
    assert_eq!(slice, &[1, 2, 3]);
    assert_eq!(slice.as_ptr(), v.as_slice().as_ptr());
}

#[test]
fn reserve() {
    let mut v: CopyThinVec<i32> = CopyThinVec::with_capacity(0);
    v.reserve(10);
    assert!(v.capacity() >= 10);
    pointer_stability(&mut v);

    let mut v: CopyThinVec<i32> = CopyThinVec::with_capacity(64);
    v.reserve(65);
    assert!(v.capacity() >= 128);
    pointer_stability(&mut v);
}

#[test]
fn reserve_exact() {
    let mut v: CopyThinVec<i32> = CopyThinVec::with_capacity(0);
    v.reserve_exact(10);
    assert!(v.capacity() >= 10);
    pointer_stability(&mut v);

    let mut v: CopyThinVec<i32> = CopyThinVec::with_capacity(64);
    v.reserve_exact(65);
    assert!(v.capacity() >= 65);
    assert!(v.capacity() < 128);
    pointer_stability(&mut v);
}

#[test]
fn remove() {
    let mut v: CopyThinVec<i32> = copy_thin_vec![10, 20, 30, 40];
    let removed = v.remove(1);
    assert_eq!(removed, 20);
    assert_eq!(v.as_slice(), &[10, 30, 40]);
}

#[test]
fn remove_first() {
    let mut v: CopyThinVec<i32> = copy_thin_vec![10, 20, 30, 40];
    let removed = v.remove(0);
    assert_eq!(removed, 10);
    assert_eq!(v.as_slice(), &[20, 30, 40]);
}

#[test]
fn remove_last() {
    let mut v: CopyThinVec<i32> = copy_thin_vec![10, 20, 30, 40];
    let removed = v.remove(v.len() - 1);
    assert_eq!(removed, 40);
    assert_eq!(v.as_slice(), &[10, 20, 30]);
}

#[test]
#[should_panic(expected = "index out of bounds")]
fn remove_panic() {
    let mut v: CopyThinVec<i32> = copy_thin_vec![1, 2, 3];
    let _ = v.remove(3);
}

#[test]
fn swap_remove() {
    let mut v: CopyThinVec<i32> = copy_thin_vec![10, 20, 30, 40];
    let removed = v.swap_remove(1);
    assert_eq!(removed, 20);
    assert_eq!(v.as_slice(), &[10, 40, 30]);
}

#[test]
fn swap_remove_first() {
    let mut v: CopyThinVec<i32> = copy_thin_vec![10, 20, 30, 40];
    let removed = v.swap_remove(0);
    assert_eq!(removed, 10);
    assert_eq!(v.as_slice(), &[40, 20, 30]);
}

#[test]
fn swap_remove_last() {
    let mut v: CopyThinVec<i32> = copy_thin_vec![10, 20, 30, 40];
    let removed = v.swap_remove(v.len() - 1);
    assert_eq!(removed, 40);
    assert_eq!(v.as_slice(), &[10, 20, 30]);
}

#[test]
#[should_panic(expected = "index out of bounds")]
fn swap_remove_panic() {
    let mut v: CopyThinVec<i32> = copy_thin_vec![1, 2, 3];
    let _ = v.swap_remove(3);
}

#[test]
fn truncate() {
    let mut v: CopyThinVec<i32> = copy_thin_vec![1, 2, 3, 4, 5];
    let capacity = v.capacity();
    let ptr = v.as_ptr();

    v.truncate(10);
    assert_eq!(v.as_slice(), [1, 2, 3, 4, 5]);
    assert_eq!(v.capacity(), capacity);
    assert_eq!(v.as_ptr(), ptr);

    v.truncate(3);
    assert_eq!(v.as_slice(), [1, 2, 3]);
    assert_eq!(v.capacity(), capacity);
    assert_eq!(v.as_ptr(), ptr);

    v.truncate(0);
    assert!(v.is_empty());
    assert_eq!(v.capacity(), capacity);
    assert_eq!(v.as_ptr(), ptr);
}

#[test]
fn clear() {
    let mut v: CopyThinVec<i32> = copy_thin_vec![0; 100];
    let old_capacity = v.capacity();
    let ptr = v.as_ptr();
    v.clear();

    assert!(v.is_empty());
    assert_eq!(v.capacity(), old_capacity);
    assert_eq!(v.as_ptr(), ptr);
}

#[test]
fn resize() {
    let mut v: CopyThinVec<i32> = copy_thin_vec![1, 2];

    v.resize(5, 9);
    assert_eq!(v.as_slice(), [1, 2, 9, 9, 9]);

    let capacity = v.capacity();
    let ptr = v.as_ptr();
    v.resize(2, 0);
    assert_eq!(v.as_slice(), [1, 2]);
    assert_eq!(v.capacity(), capacity);
    assert_eq!(v.as_ptr(), ptr);
}

#[test]
fn resize_with() {
    let mut next = 1;
    let mut v: CopyThinVec<i32> = copy_thin_vec![10];

    v.resize_with(4, || {
        let value = next;
        next += 1;
        value
    });
    assert_eq!(v.as_slice(), [10, 1, 2, 3]);

    let capacity = v.capacity();
    let ptr = v.as_ptr();
    v.resize_with(2, || unreachable!());
    assert_eq!(v.as_slice(), [10, 1]);
    assert_eq!(v.capacity(), capacity);
    assert_eq!(v.as_ptr(), ptr);
}
