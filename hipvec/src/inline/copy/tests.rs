use super::*;
use crate::inline::layouts::{BasicLayout, Layout};

type Inline<T> = InlineVec<T, BasicLayout>;

#[test]
fn niche() {
    assert_eq!(size_of::<Option<Inline<()>>>(), size_of::<Inline<()>>());
    assert_eq!(size_of::<Option<Inline<i32>>>(), size_of::<Inline<i32>>());
    assert_eq!(size_of::<Option<Inline<i128>>>(), size_of::<Inline<i128>>());
}

#[test]
fn new() {
    let mut l = Inline::<i32>::new();
    assert_eq!(l.len(), 0);
    l.push(1);
    assert_eq!(l.len(), 1);
    assert_eq!(l.as_slice(), &[1]);
}

#[test]
fn dst() {
    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
    struct Dst;

    assert_eq!(size_of::<Dst>(), 0);

    let mut l = Inline::<Dst>::new();
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
    assert_eq!(Inline::<Dst>::CAPACITY, usize::MAX >> 1);
    assert_eq!(l.capacity(), usize::MAX >> 1);
}

#[test]
fn slice() {
    let mut l = Inline::<i32>::new();
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
fn capacity() {
    let l = Inline::<i32>::new();
    assert_eq!(
        Inline::<i32>::CAPACITY,
        <BasicLayout as Layout<i32>>::CAPACITY
    );
    assert_eq!(l.capacity(), Inline::<i32>::CAPACITY);
    assert_eq!(l.len(), 0);

    let mut l = Inline::<i32>::new();
    for i in 0..l.capacity() {
        l.push(i as i32);
        assert_eq!(l.len(), i + 1);
    }
    assert_eq!(l.len(), l.capacity());
}

#[test]
#[should_panic(expected = "new length exceeds capacity")]
fn push_panic() {
    let mut l = Inline::<i32>::new();
    for i in 0..=l.capacity() {
        l.push(i as i32);
    }
}

#[test]
fn from_array() {
    let l = Inline::<i32>::from([1, 2, 3]);
    assert_eq!(l.as_slice(), &[1, 2, 3]);
}

#[test]
fn from_array_empty() {
    let l = Inline::<i32>::from([]);
    assert!(l.as_slice().is_empty());
}

#[test]
#[should_panic(expected = "array length exceeds capacity")]
fn from_array_panic() {
    let _ = Inline::<i32>::from([0; <BasicLayout as Layout<i32>>::CAPACITY + 1]);
}

#[test]
fn clear() {
    let mut l = Inline::<i32>::from([1, 2, 3]);
    l.clear();
    assert!(l.is_empty());
    assert_eq!(l.len(), 0);
}

#[test]
fn from_slice() {
    let l = Inline::<i32>::from([1, 2, 3].as_slice());
    assert_eq!(l.as_slice(), &[1, 2, 3]);
}

#[test]
fn extend_from_slice() {
    let mut l = Inline::<i32>::from([1, 2]);

    l.extend_from_slice(&[3, 4]);
    assert_eq!(l.as_slice(), &[1, 2, 3, 4]);

    l.extend_from_slice(&[]);
    assert_eq!(l.as_slice(), &[1, 2, 3, 4]);
}

#[test]
#[should_panic(expected = "new length exceeds capacity")]
fn extend_from_slice_panic() {
    let mut l = Inline::<i32>::new();
    let too_many = [0; <BasicLayout as Layout<i32>>::CAPACITY + 1];
    l.extend_from_slice(&too_many);
}

#[test]
fn with_capacity() {
    let l = Inline::<i32>::with_capacity(0);
    assert!(l.is_empty());
    assert_eq!(l.capacity(), Inline::<i32>::CAPACITY);

    let l = Inline::<i32>::with_capacity(Inline::<i32>::CAPACITY);
    assert!(l.is_empty());
}

#[test]
#[should_panic(expected = "required capacity exceeds maximum")]
fn with_capacity_panic() {
    let _ = Inline::<i32>::with_capacity(Inline::<i32>::CAPACITY + 1);
}

#[test]
fn copy_inline_vec_empty() {
    let l: Inline<i32> = crate::copy_inline_vec![];
    assert!(l.is_empty());
}

#[test]
fn copy_inline_vec_list() {
    let l: Inline<i32> = crate::copy_inline_vec![1, 2, 3];
    assert_eq!(l.as_slice(), &[1, 2, 3]);
}

#[test]
fn copy_inline_vec_list_trailing_comma() {
    let l: Inline<i32> = crate::copy_inline_vec![1, 2, 3,];
    assert_eq!(l.as_slice(), &[1, 2, 3]);
}

#[test]
fn copy_inline_vec_repeat() {
    let l: Inline<i32> = crate::copy_inline_vec![7; 3];
    assert_eq!(l.as_slice(), &[7, 7, 7]);
}

#[test]
fn copy_inline_vec_repeat_zero() {
    let mut side_effect = 0usize;
    let l: Inline<i32> = crate::copy_inline_vec![{ side_effect += 1; 42 }; 0];
    assert!(l.is_empty());
    assert_eq!(side_effect, 1);
}
