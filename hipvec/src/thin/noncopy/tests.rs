use crate::common::tests::pointer_stability;
use crate::thin::ThinVec;
use crate::thin_vec;

#[test]
fn new_and_default() {
    let new: ThinVec<i32> = ThinVec::new();
    assert!(new.is_empty());
    assert_eq!(new.len(), 0);

    let default: ThinVec<i32> = ThinVec::default();
    assert!(default.is_empty());
    assert_eq!(default.len(), 0);
}

#[test]
fn with_capacity() {
    let v: ThinVec<i32> = ThinVec::with_capacity(0);
    assert!(v.is_empty());
    assert_eq!(v.capacity(), 0);

    let v: ThinVec<i32> = ThinVec::with_capacity(8);
    assert!(v.is_empty());
    assert!(v.capacity() >= 8);
}

#[test]
fn from_array_and_slice() {
    let from_array: ThinVec<i32> = ThinVec::from([1, 2, 3]);
    assert_eq!(from_array.as_slice(), &[1, 2, 3]);

    let from_slice: ThinVec<i32> = ThinVec::from([4, 5, 6].as_slice());
    assert_eq!(from_slice.as_slice(), &[4, 5, 6]);
}

#[test]
fn macro_constructors() {
    let empty: ThinVec<i32> = thin_vec![];
    assert!(empty.is_empty());

    let list: ThinVec<i32> = thin_vec![1, 2, 3,];
    assert_eq!(list.as_slice(), &[1, 2, 3]);

    let repeated: ThinVec<i32> = thin_vec![7; 3];
    assert_eq!(repeated.as_slice(), &[7, 7, 7]);
}

#[test]
fn push_pop() {
    let mut v: ThinVec<i32> = ThinVec::new();
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
    let v: ThinVec<i32> = thin_vec![1, 2, 3];
    assert_eq!(v.as_slice(), &[1, 2, 3]);
}

#[test]
fn deref() {
    let v: ThinVec<i32> = thin_vec![1, 2, 3];
    let slice: &[i32] = &v;
    assert_eq!(slice, &[1, 2, 3]);
    assert_eq!(slice.as_ptr(), v.as_slice().as_ptr());
}

#[test]
fn reserve() {
    let mut v: ThinVec<i32> = ThinVec::with_capacity(0);
    v.reserve(10);
    assert!(v.capacity() >= 10);
    pointer_stability(&mut v);

    let mut v: ThinVec<i32> = ThinVec::with_capacity(64);
    v.reserve(65);
    assert!(v.capacity() >= 128);
    pointer_stability(&mut v);
}

#[test]
fn reserve_exact() {
    let mut v: ThinVec<i32> = ThinVec::with_capacity(0);
    v.reserve_exact(10);
    assert!(v.capacity() >= 10);
    pointer_stability(&mut v);

    let mut v: ThinVec<i32> = ThinVec::with_capacity(64);
    v.reserve_exact(65);
    assert!(v.capacity() >= 65);
    assert!(v.capacity() < 128);
    pointer_stability(&mut v);
}

#[test]
fn remove() {
    let mut v: ThinVec<i32> = thin_vec![10, 20, 30, 40];
    let removed = v.remove(1);
    assert_eq!(removed, 20);
    assert_eq!(v.as_slice(), &[10, 30, 40]);
}

#[test]
fn remove_first() {
    let mut v: ThinVec<i32> = thin_vec![10, 20, 30, 40];
    let removed = v.remove(0);
    assert_eq!(removed, 10);
    assert_eq!(v.as_slice(), &[20, 30, 40]);
}

#[test]
fn remove_last() {
    let mut v: ThinVec<i32> = thin_vec![10, 20, 30, 40];
    let removed = v.remove(v.len() - 1);
    assert_eq!(removed, 40);
    assert_eq!(v.as_slice(), &[10, 20, 30]);
}

#[test]
#[should_panic(expected = "index out of bounds")]
fn remove_panic() {
    let mut v: ThinVec<i32> = thin_vec![1, 2, 3];
    let _ = v.remove(3);
}

#[test]
fn swap_remove() {
    let mut v: ThinVec<i32> = thin_vec![10, 20, 30, 40];
    let removed = v.swap_remove(1);
    assert_eq!(removed, 20);
    assert_eq!(v.as_slice(), &[10, 40, 30]);
}

#[test]
fn swap_remove_first() {
    let mut v: ThinVec<i32> = thin_vec![10, 20, 30, 40];
    let removed = v.swap_remove(0);
    assert_eq!(removed, 10);
    assert_eq!(v.as_slice(), &[40, 20, 30]);
}

#[test]
fn swap_remove_last() {
    let mut v: ThinVec<i32> = thin_vec![10, 20, 30, 40];
    let removed = v.swap_remove(v.len() - 1);
    assert_eq!(removed, 40);
    assert_eq!(v.as_slice(), &[10, 20, 30]);
}

#[test]
#[should_panic(expected = "index out of bounds")]
fn swap_remove_panic() {
    let mut v: ThinVec<i32> = thin_vec![1, 2, 3];
    let _ = v.swap_remove(3);
}

#[test]
fn truncate() {
    let mut v: ThinVec<i32> = thin_vec![1, 2, 3, 4, 5];
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
    let mut v: ThinVec<i32> = thin_vec![0; 100];
    let old_capacity = v.capacity();
    let ptr = v.as_ptr();
    v.clear();

    assert!(v.is_empty());
    assert_eq!(v.capacity(), old_capacity);
    assert_eq!(v.as_ptr(), ptr);
}
