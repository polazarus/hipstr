use alloc::boxed::Box;
use alloc::format;
use alloc::string::String;

use crate::common::tests::pointer_stability;
use crate::thin::ThinVec as V;
use crate::thin_vec as v;

#[test]
fn new_and_default() {
    let new: V<i32> = V::new();
    assert!(new.is_empty());
    assert_eq!(new.len(), 0);

    let default: V<i32> = V::default();
    assert!(default.is_empty());
    assert_eq!(default.len(), 0);
}

#[test]
fn with_capacity() {
    let v: V<i32> = V::with_capacity(0);
    assert!(v.is_empty());
    assert_eq!(v.capacity(), 0);

    let v: V<i32> = V::with_capacity(8);
    assert!(v.is_empty());
    assert!(v.capacity() >= 8);
}

#[test]
fn from_array_and_slice() {
    let from_array: V<i32> = V::from([1, 2, 3]);
    assert_eq!(from_array.as_slice(), &[1, 2, 3]);

    let from_slice: V<i32> = V::from([4, 5, 6].as_slice());
    assert_eq!(from_slice.as_slice(), &[4, 5, 6]);
}

#[test]
fn macro_constructors() {
    let empty: V<i32> = v![];
    assert!(empty.is_empty());

    let list: V<i32> = v![1, 2, 3,];
    assert_eq!(list.as_slice(), &[1, 2, 3]);

    let repeated: V<i32> = v![7; 3];
    assert_eq!(repeated.as_slice(), &[7, 7, 7]);
}

#[test]
fn push_pop() {
    let mut v: V<i32> = V::new();
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
    let v: V<i32> = v![1, 2, 3];
    assert_eq!(v.as_slice(), &[1, 2, 3]);
}

#[test]
fn deref() {
    let v: V<i32> = v![1, 2, 3];
    let slice: &[i32] = &v;
    assert_eq!(slice, &[1, 2, 3]);
    assert_eq!(slice.as_ptr(), v.as_slice().as_ptr());
}

#[test]
fn reserve() {
    let mut v: V<i32> = V::with_capacity(0);
    v.reserve(10);
    assert!(v.capacity() >= 10);
    pointer_stability(&mut v);

    let mut v: V<i32> = V::with_capacity(64);
    v.reserve(65);
    assert!(v.capacity() >= 128);
    pointer_stability(&mut v);
}

#[test]
fn reserve_exact() {
    let mut v: V<i32> = V::with_capacity(0);
    v.reserve_exact(10);
    assert!(v.capacity() >= 10);
    pointer_stability(&mut v);

    let mut v: V<i32> = V::with_capacity(64);
    v.reserve_exact(65);
    assert!(v.capacity() >= 65);
    assert!(v.capacity() < 128);
    pointer_stability(&mut v);
}

#[test]
fn append() {
    let mut left: V<String> = v![String::from("a"), String::from("b")];
    let mut right: V<String> = v![String::from("c"), String::from("d")];
    left.append(&mut right);
    assert_eq!(
        left.as_slice(),
        &[
            String::from("a"),
            String::from("b"),
            String::from("c"),
            String::from("d"),
        ]
    );
    assert!(right.is_empty());

    let mut left: V<String> = v![String::from("a"), String::from("b")];
    let mut right = alloc::vec![String::from("c"), String::from("d")];
    left.append(&mut right);
    assert_eq!(
        left.as_slice(),
        &[
            String::from("a"),
            String::from("b"),
            String::from("c"),
            String::from("d"),
        ]
    );
    assert!(right.is_empty());

    let mut left: V<Box<u8>> = v![Box::new(1)];
    let mut right = crate::inline::InlineVec::<Box<u8>>::new();
    right.push(Box::new(2));
    if right.capacity() > 1 {
        right.push(Box::new(3));
    }
    left.append(&mut right);
    if left.len() == 2 {
        assert_eq!(left.as_slice(), &[Box::new(1), Box::new(2)]);
    } else {
        assert_eq!(left.as_slice(), &[Box::new(1), Box::new(2), Box::new(3)]);
    }
    assert!(right.is_empty());
}

#[test]
fn remove() {
    let mut v: V<i32> = v![10, 20, 30, 40];
    let removed = v.remove(1);
    assert_eq!(removed, 20);
    assert_eq!(v.as_slice(), &[10, 30, 40]);
}

#[test]
fn remove_first() {
    let mut v: V<i32> = v![10, 20, 30, 40];
    let removed = v.remove(0);
    assert_eq!(removed, 10);
    assert_eq!(v.as_slice(), &[20, 30, 40]);
}

#[test]
fn remove_last() {
    let mut v: V<i32> = v![10, 20, 30, 40];
    let removed = v.remove(v.len() - 1);
    assert_eq!(removed, 40);
    assert_eq!(v.as_slice(), &[10, 20, 30]);
}

#[test]
#[should_panic(expected = "index out of bounds")]
fn remove_panic() {
    let mut v: V<i32> = v![1, 2, 3];
    let _ = v.remove(3);
}

#[test]
fn swap_remove() {
    let mut v: V<i32> = v![10, 20, 30, 40];
    let removed = v.swap_remove(1);
    assert_eq!(removed, 20);
    assert_eq!(v.as_slice(), &[10, 40, 30]);
}

#[test]
fn swap_remove_first() {
    let mut v: V<i32> = v![10, 20, 30, 40];
    let removed = v.swap_remove(0);
    assert_eq!(removed, 10);
    assert_eq!(v.as_slice(), &[40, 20, 30]);
}

#[test]
fn swap_remove_last() {
    let mut v: V<i32> = v![10, 20, 30, 40];
    let removed = v.swap_remove(v.len() - 1);
    assert_eq!(removed, 40);
    assert_eq!(v.as_slice(), &[10, 20, 30]);
}

#[test]
#[should_panic(expected = "index out of bounds")]
fn swap_remove_panic() {
    let mut v: V<i32> = v![1, 2, 3];
    let _ = v.swap_remove(3);
}

#[test]
fn truncate() {
    let mut v: V<i32> = v![1, 2, 3, 4, 5];
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
    let mut v: V<i32> = v![0; 100];
    let old_capacity = v.capacity();
    let ptr = v.as_ptr();
    v.clear();

    assert!(v.is_empty());
    assert_eq!(v.capacity(), old_capacity);
    assert_eq!(v.as_ptr(), ptr);
}

#[test]
fn drain() {
    let mut v: V<i32> = v![1, 2, 3, 4, 5];
    let drain = v.drain(1..4);
    assert_eq!(drain.as_slice(), [2, 3, 4]);
    assert!(drain.eq([2, 3, 4]));
    assert_eq!(v.as_slice(), [1, 5]);

    let mut v: V<i32> = v![1, 2, 3, 4, 5];
    assert!(v.drain(..).eq([1, 2, 3, 4, 5]));
    assert!(v.is_empty());
    assert_eq!(v.as_slice(), []);

    let mut v: V<i32> = v![1, 2, 3, 4, 5];
    assert_eq!(v.drain(2..2).count(), 0);
    assert_eq!(v.as_slice(), [1, 2, 3, 4, 5]);
}

#[test]
#[should_panic]
fn drain_invalid_range_panics() {
    let mut v: V<i32> = v![1, 2, 3, 4, 5];
    let _ = v.drain(4..1);
}

#[test]
fn resize() {
    let mut v: V<String> = v![String::from("a"), String::from("b")];

    v.resize(5, String::from("x"));
    assert_eq!(
        v.as_slice(),
        &[
            String::from("a"),
            String::from("b"),
            String::from("x"),
            String::from("x"),
            String::from("x"),
        ]
    );

    let capacity = v.capacity();
    let ptr = v.as_ptr();
    v.resize(2, String::new());
    assert_eq!(v.as_slice(), &[String::from("a"), String::from("b")]);
    assert_eq!(v.capacity(), capacity);
    assert_eq!(v.as_ptr(), ptr);
}

#[test]
fn resize_with() {
    let mut next = 1;
    let mut v: V<String> = v![String::from("seed")];

    v.resize_with(4, || {
        let value = format!("v{next}");
        next += 1;
        value
    });
    assert_eq!(
        v.as_slice(),
        &[
            String::from("seed"),
            String::from("v1"),
            String::from("v2"),
            String::from("v3"),
        ]
    );

    let capacity = v.capacity();
    let ptr = v.as_ptr();
    v.resize_with(2, || unreachable!());
    assert_eq!(v.as_slice(), &[String::from("seed"), String::from("v1")]);
    assert_eq!(v.capacity(), capacity);
    assert_eq!(v.as_ptr(), ptr);
}

#[test]
fn splice() {
    let mut v = v![1, 2, 3, 4, 5];
    {
        let splice = v.splice(1..4, [9, 8]);
        assert!(splice.eq([2, 3, 4]));
    }
    assert_eq!(v.as_slice(), [1, 9, 8, 5]);

    let mut v = v![1, 2, 3, 4, 5];
    {
        let splice = v.splice(1..3, [9, 8, 7, 6]);
        assert!(splice.eq([2, 3]));
    }
    assert_eq!(v.as_slice(), [1, 9, 8, 7, 6, 4, 5]);

    let mut v = v![1, 2, 3, 4, 5];
    {
        let splice = v.splice(1..4, [9, 8, 7, 6].into_iter().filter(|_| true));
        assert!(splice.eq([2, 3, 4]));
    }
    assert_eq!(v.as_slice(), [1, 9, 8, 7, 6, 5]);

    let mut v = v![1, 5];
    {
        let splice = v.splice(1..1, [2, 3, 4]);
        assert!(splice.eq([]));
    }
    assert_eq!(v.as_slice(), [1, 2, 3, 4, 5]);

    let mut v = v![1, 2, 3, 4, 5];
    {
        let splice = v.splice(.., [9, 8]);
        assert!(splice.eq([1, 2, 3, 4, 5]));
    }
    assert_eq!(v.as_slice(), [9, 8]);

    let mut v = v![1, 2, 3, 4, 5];
    {
        let splice = v.splice(.., []);
        assert!(splice.eq([1, 2, 3, 4, 5]));
    }
    assert!(v.is_empty());
}

#[test]
fn splice_boxed() {
    let mut v: V<Box<u8>> = v![Box::new(1), Box::new(2), Box::new(3)];
    {
        let splice = v.splice(1..2, [Box::new(9), Box::new(8)]);
        assert!(splice.eq([Box::new(2)]));
    }
    assert_eq!(
        v.as_slice(),
        [Box::new(1), Box::new(9), Box::new(8), Box::new(3)]
    );
}

#[test]
#[should_panic(expected = "start index 4 is greater than end index 1")]
fn splice_invalid_range_panics() {
    let mut v = v![1, 2, 3, 4, 5];
    let _ = v.splice(4..1, [9, 8]);
}
