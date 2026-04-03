use core::cell::Cell;

use crate::inline::InlineVec as Inline;
use crate::inline::layouts::{BasicLayout, Layout};
use crate::inline_vec;

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
fn push_mut() {
    let mut l = Inline::<u8>::with_capacity(1);
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
    let mut l = Inline::<u8>::new();
    let cap = l.capacity();
    for i in 0..cap {
        let _ = l.push_mut(i as u8);
    }
    let _ = l.push_mut(0);
}

#[test]
fn insert() {
    let mut v = Inline::new();
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
    let mut v: Inline<u8> = Inline::new();
    for i in 0..v.capacity() {
        v.insert(0, (i + 1) as u8);
    }
    v.insert(0, 0);
}

#[test]
#[should_panic(expected = "index out of bounds")]
fn insert_panic_out_of_bounds() {
    let mut v = inline_vec![1_u8, 2];
    v.insert(4, 5);
}

#[test]
fn insert_mut() {
    let mut v = Inline::new();
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
        let mut l = Inline::<DropCounter<'_>>::new();
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
    let mut l = Inline::<u8>::from([1, 2, 3]);

    l.clear();
    assert!(l.is_empty());

    l.clear();
    assert!(l.is_empty());

    let mut l = Inline::<u8>::new();
    l.clear();
    assert!(l.is_empty());
}

#[test]
fn truncate() {
    let mut l = inline_vec![1_u8, 2, 3, 4];
    l.truncate(6);
    assert_eq!(l.as_slice(), [1, 2, 3, 4]);

    l.truncate(2);
    assert_eq!(l.as_slice(), [1, 2]);

    l.truncate(0);
    assert!(l.is_empty());
}

#[test]
fn remove() {
    let mut l = Inline::<i32>::from([10, 20, 30, 40]);
    let removed = l.remove(1);
    assert_eq!(removed, 20);
    assert_eq!(l.as_slice(), &[10, 30, 40]);
}

#[test]
fn remove_first() {
    let mut l = Inline::<i32>::from([10, 20, 30, 40]);
    let removed = l.remove(0);
    assert_eq!(removed, 10);
    assert_eq!(l.as_slice(), &[20, 30, 40]);
}

#[test]
fn remove_last() {
    let mut l = Inline::<i32>::from([10, 20, 30, 40]);
    let removed = l.remove(l.len() - 1);
    assert_eq!(removed, 40);
    assert_eq!(l.as_slice(), &[10, 20, 30]);
}

#[test]
#[should_panic(expected = "index out of bounds")]
fn remove_panic() {
    let mut l = Inline::<i32>::from([1, 2, 3]);
    let _ = l.remove(3);
}

#[test]
fn swap_remove() {
    let mut l = Inline::<i32>::from([10, 20, 30, 40]);
    let removed = l.swap_remove(1);
    assert_eq!(removed, 20);
    assert_eq!(l.as_slice(), &[10, 40, 30]);
}

#[test]
fn swap_remove_first() {
    let mut l = Inline::<i32>::from([10, 20, 30, 40]);
    let removed = l.swap_remove(0);
    assert_eq!(removed, 10);
    assert_eq!(l.as_slice(), &[40, 20, 30]);
}

#[test]
fn swap_remove_last() {
    let mut l = Inline::<i32>::from([10, 20, 30, 40]);
    let removed = l.swap_remove(l.len() - 1);
    assert_eq!(removed, 40);
    assert_eq!(l.as_slice(), &[10, 20, 30]);
}

#[test]
#[should_panic(expected = "index out of bounds")]
fn swap_remove_panic() {
    let mut l = Inline::<i32>::from([1, 2, 3]);
    let _ = l.swap_remove(3);
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
fn inline_vec_empty() {
    let l: Inline<i32> = inline_vec![];
    assert!(l.is_empty());
}

#[test]
fn inline_vec_list() {
    let l: Inline<i32> = inline_vec![1, 2, 3];
    assert_eq!(l.as_slice(), &[1, 2, 3]);
}

#[test]
fn inline_vec_list_trailing_comma() {
    let l: Inline<i32> = inline_vec![1, 2, 3,];
    assert_eq!(l.as_slice(), &[1, 2, 3]);
}

#[test]
fn inline_vec_repeat() {
    let l: Inline<i32> = inline_vec![7; 3];
    assert_eq!(l.as_slice(), &[7, 7, 7]);
}

#[test]
fn inline_vec_repeat_zero() {
    let mut side_effect = 0usize;
    let l: Inline<i32> = inline_vec![{ side_effect += 1; 42 }; 0];
    assert!(l.is_empty());
    assert_eq!(side_effect, 1);
}
