use alloc::boxed::Box;
use alloc::{format, vec};
use core::hash::BuildHasher;
use core::mem::size_of;
use core::ptr;

use super::*;
use crate::{inline_vec, thin_vec};

const SMALL_CAP: usize = 7;
const SMALL_FULL: InlineVec<u8, SMALL_CAP> = InlineVec::from_array([1, 2, 3, 4, 5, 6, 7]);

#[test]
fn tagged_len() {
    let tagged = TaggedU8::<3, 0b101>::new(0b10);
    assert_eq!(tagged.0.get(), 0b10_101);
}

#[test]
#[should_panic(expected = "length exceeds maximal tagged length (`256 >> SHIFT`)")]
fn tagged_len_too_large() {
    let _ = TaggedU8::<3, 0b101>::new(0b1000_00);
}

#[test]
fn macros() {
    const CAP: usize = 7;
    let inline = inline_vec![CAP => 1, 2, 3];
    assert_eq!(inline.len(), 3);
    assert_eq!(inline.as_slice(), &[1, 2, 3]);

    let inline = inline_vec![CAP => 1; 3];
    assert_eq!(inline.len(), 3);
    assert_eq!(inline.as_slice(), &[1, 1, 1]);
}

#[test]
fn new() {
    const CAP: usize = 7;
    let mut inline = InlineVec::<u8, CAP>::new();
    assert_eq!(inline.len(), 0);
    assert_eq!(inline.capacity(), CAP);
    assert_eq!(inline.as_slice().len(), 0);
    assert_eq!(inline.as_mut_slice().len(), 0);
    assert_eq!(inline.spare_capacity_mut().len(), CAP);
}

#[test]
fn from_slice_copy() {
    const CAP: usize = 7;
    let slice = [1, 2, 3];
    let inline = InlineVec::<u8, CAP>::from_slice_copy(&slice);
    assert_eq!(inline.len(), slice.len());
    assert_eq!(inline.as_slice(), &slice);
}

#[test]
fn from_slice_clone() {
    const CAP: usize = 7;
    let slice: &[_] = &[1, 2, 3];
    let inline = InlineVec::<u8, CAP>::from_slice_clone(slice);
    assert_eq!(inline.len(), slice.len());
    assert_eq!(inline.as_slice(), slice);

    #[derive(Clone, PartialEq, Eq, Debug)]
    struct S(u8);
    let slice: &[_] = &[S(1), S(2), S(3)];
    let inline = InlineVec::<_, CAP>::from_slice_clone(&slice);
    assert_eq!(inline.len(), slice.len());
    assert_eq!(inline.as_slice(), slice);
}

#[test]
fn try_push() {
    const CAP: usize = 7;

    let array: [u8; CAP] = core::array::from_fn(|i| i as u8 + 1);
    let mut inline = InlineVec::<u8, CAP>::new();

    for i in 1..=CAP {
        assert_eq!(inline.try_push(i as u8), Ok(()));
        assert_eq!(inline.len(), i);
        assert_eq!(inline.as_slice(), &array[..i]);
    }

    let n = CAP as u8 + 1;
    assert_eq!(inline.try_push(n), Err(n));
}

#[test]
fn push_and_drop() {
    use core::cell::Cell;

    #[derive(PartialEq, Eq, Debug)]
    struct S<'a>(&'a Cell<usize>);
    impl Drop for S<'_> {
        fn drop(&mut self) {
            self.0.set(self.0.get() + 1);
        }
    }

    let counter = Cell::new(0);

    const CAP: usize = 7;
    {
        let mut inline = InlineVec::<S<'_>, CAP>::new();
        for _ in 0..CAP {
            inline.push(S(&counter));
            assert_eq!(counter.get(), 0);
        }
    } // drop inline
    assert_eq!(counter.get(), CAP);
}

#[test]
#[should_panic(expected = "inline vector is full")]
fn push_fail() {
    let mut inline = SMALL_FULL;
    inline.push(42);
}

#[test]
fn clear() {
    let mut inline = SMALL_FULL;
    inline.clear();
    assert_eq!(inline.len(), 0);
}

#[test]
fn truncate() {
    let mut inline = SMALL_FULL;
    inline.truncate(5);
    assert_eq!(inline.len(), 5);
    inline.truncate(SMALL_CAP);
    assert_eq!(inline.len(), 5);
    inline.truncate(3);
    assert_eq!(inline.len(), 3);
    assert_eq!(inline.as_slice(), &[1, 2, 3]);
}

#[test]
fn swap_remove() {
    const CAP: usize = 7;
    let mut inline = InlineVec::<u8, CAP>::new();
    for i in 1..=CAP {
        inline.push(i as u8);
        assert_eq!(inline.len(), i);
    }
    assert_eq!(inline.len(), CAP);
    assert_eq!(inline.swap_remove(0), 1);
    assert_eq!(inline.as_slice(), &[7, 2, 3, 4, 5, 6]);
    assert_eq!(inline.len(), CAP - 1);
}

#[test]
#[should_panic(expected = "index out of bounds")]
fn swap_remove_out_of_bounds() {
    const CAP: usize = 7;
    let mut inline = InlineVec::<u8, CAP>::new();
    for i in 1..=5 {
        inline.push(i as u8);
        assert_eq!(inline.len(), i);
    }
    assert_eq!(inline.len(), 5);
    inline.swap_remove(6);
}

#[test]
fn remove() {
    const CAP: usize = 7;
    let mut inline = InlineVec::<u8, CAP>::new();
    for i in 1..=CAP {
        inline.push(i as u8);
        assert_eq!(inline.len(), i);
    }
    assert_eq!(inline.len(), CAP);
    assert_eq!(inline.remove(2), 3);
    assert_eq!(inline.as_slice(), &[1, 2, 4, 5, 6, 7]);
}

#[test]
#[should_panic(expected = "index out of bounds")]
fn remove_out_of_bounds() {
    const CAP: usize = 7;
    let mut inline = InlineVec::<u8, CAP>::new();
    for i in 1..=5 {
        inline.push(i as u8);
        assert_eq!(inline.len(), i);
    }
    assert_eq!(inline.len(), 5);
    inline.remove(6);
}

#[test]
fn try_insert() {
    const CAP: usize = 7;
    let mut inline = InlineVec::<u8, CAP>::new();

    let err = inline.try_insert(1, 33).unwrap_err();
    assert_eq!(
        err,
        InsertError {
            value: 33,
            kind: InsertErrorKind::OutOfBounds,
        }
    );
    assert_eq!(format!("{err}"), InsertErrorKind::OutOfBounds.message());

    for i in 1..=CAP {
        assert_eq!(inline.try_insert(0, i as u8), Ok(()));
        assert_eq!(inline.len(), i);
    }
    let err = inline.try_insert(0, 42).unwrap_err();
    assert_eq!(
        err,
        InsertError {
            value: 42,
            kind: InsertErrorKind::Full,
        }
    );
    assert_eq!(format!("{err}"), InsertErrorKind::Full.message());

    let mut inline = InlineVec::<u8, CAP>::from_array([1, 2, 4, 5]);
    assert_eq!(inline.try_insert(2, 3), Ok(()));
    assert_eq!(inline.as_slice(), &[1, 2, 3, 4, 5]);
    assert_eq!(inline.len(), 5);
}

#[test]
fn insert() {
    const CAP: usize = 7;
    let mut inline = InlineVec::<u8, CAP>::new();

    for i in 1..=CAP {
        inline.insert(0, i as u8);
        assert_eq!(inline.len(), i);
    }
    assert_eq!(inline.len(), CAP);

    let mut inline = InlineVec::<u8, CAP>::from_array([1, 2, 4, 5]);
    inline.insert(2, 3);
    assert_eq!(inline.as_slice(), &[1, 2, 3, 4, 5]);
    assert_eq!(inline.len(), 5);
}

#[test]
#[should_panic(expected = "index out of bounds")]
fn insert_out_of_bounds() {
    const CAP: usize = 7;
    let mut inline = InlineVec::<u8, CAP>::new();
    inline.insert(1, 33);
}

#[test]
#[should_panic(expected = "inline vector is full")]
fn insert_full() {
    const CAP: usize = 7;
    let mut inline = InlineVec::<u8, CAP>::new();
    for i in 1..=CAP {
        inline.insert(0, i as u8);
    }
    assert_eq!(inline.len(), CAP);
    inline.insert(0, 42);
}

#[test]
fn pop() {
    const CAP: usize = 7;
    let mut inline = InlineVec::<u8, CAP>::new();
    assert_eq!(inline.pop(), None);
    inline.push(1);
    assert_eq!(inline.pop(), Some(1));
    assert_eq!(inline.len(), 0);
    assert_eq!(inline.pop(), None);
}

#[test]
fn pop_if() {
    let mut inline = SMALL_FULL;

    assert_eq!(inline.pop_if(|b| *b % 2 == 0), None);
    assert_eq!(inline.pop_if(|b| *b % 2 == 1), Some(7));

    assert_eq!(inline.pop_if(|b| *b % 2 == 1), None);
    assert_eq!(inline.pop_if(|b| *b % 2 == 0), Some(6));

    inline.clear();
    assert_eq!(inline.pop_if(|_| unreachable!()), None);
}

#[test]
fn niche() {
    assert_eq!(
        size_of::<InlineVec<u8, 7>>(),
        size_of::<Option<InlineVec<u8, 7>>>()
    );
    assert_eq!(
        size_of::<InlineVec<u8, 23>>(),
        size_of::<Option<InlineVec<u8, 23>>>()
    );
}

#[test]
fn zst() {
    const CAP: usize = TaggedU8::<SHIFT_DEFAULT, TAG_DEFAULT>::max();
    let mut inline = InlineVec::<(), CAP>::new();
    assert_eq!(size_of_val(&inline), 1);
    assert_eq!(inline.len(), 0);
    for i in 1..=CAP {
        assert_eq!(inline.try_push(()), Ok(()), "at {i} / {CAP}");
        assert_eq!(inline.len(), i);
    }
    assert_eq!(inline.try_push(()), Err(()));
}

#[test]
fn extend_from_slice() {
    const CAP: usize = 7;
    let mut inline = InlineVec::<u8, CAP>::new();
    let slice = &[1, 2, 3];
    inline.extend_from_slice(slice);
    assert_eq!(inline.len(), slice.len());
    assert_eq!(inline.as_slice(), slice);

    let slice = &[4, 5, 6];
    inline.extend_from_slice(slice);
    assert_eq!(inline.len(), slice.len() * 2);
    assert_eq!(inline.as_slice(), &[1, 2, 3, 4, 5, 6]);
}

#[test]
#[should_panic(expected = "new length exceeds capacity")]
fn extend_from_slice_full() {
    const CAP: usize = 7;
    let mut inline = InlineVec::<u8, CAP>::new();
    let slice: &[u8] = &[1, 2, 3, 4, 5, 6, 7];
    inline.extend_from_slice(slice);
    assert_eq!(inline.len(), slice.len());
    assert_eq!(inline.as_slice(), slice);

    let slice: &[u8] = &[9, 9, 10];
    inline.extend_from_slice(slice);
}

#[test]
fn extend_from_slice_copy() {
    const CAP: usize = 7;
    let mut inline = InlineVec::<u8, CAP>::new();
    let slice = &[1, 2, 3];
    inline.extend_from_slice_copy(slice);
    assert_eq!(inline.len(), slice.len());
    assert_eq!(inline.as_slice(), slice);

    let slice = &[4, 5, 6];
    inline.extend_from_slice_copy(slice);
    assert_eq!(inline.len(), slice.len() * 2);
    assert_eq!(inline.as_slice(), &[1, 2, 3, 4, 5, 6]);
}

#[test]
#[should_panic(expected = "new length exceeds capacity")]
fn extend_from_slice_copy_full() {
    const CAP: usize = 7;
    let mut inline = InlineVec::<u8, CAP>::new();
    let slice: &[u8] = &[1, 2, 3, 4, 5, 6, 7];
    inline.extend_from_slice_copy(slice);
    assert_eq!(inline.len(), slice.len());
    assert_eq!(inline.as_slice(), slice);

    let slice: &[u8] = &[8, 9, 10];
    inline.extend_from_slice_copy(slice);
}

#[test]
fn extend_from_array() {
    const CAP: usize = 7;
    let mut inline = InlineVec::<u8, CAP>::new();
    let array = [1, 2, 3];
    inline.extend_from_array(array);
    assert_eq!(inline.len(), array.len());
    assert_eq!(inline.as_slice(), &array);

    let array = [4, 5, 6];
    inline.extend_from_array(array);
    assert_eq!(inline.len(), array.len() * 2);
    assert_eq!(inline.as_slice(), &[1, 2, 3, 4, 5, 6]);
}

#[test]
#[should_panic(expected = "new length exceeds capacity")]
fn extend_from_array_full() {
    const CAP: usize = 7;
    let mut inline = InlineVec::<u8, CAP>::new();
    let array: [u8; 7] = [1, 2, 3, 4, 5, 6, 7];
    inline.extend_from_array(array);
    assert_eq!(inline.len(), array.len());
    assert_eq!(inline.as_slice(), &array);

    let array: [u8; 3] = [8, 0, 10];
    inline.extend_from_array(array);
}

#[test]
fn into_iter() {
    let inline = InlineVec::<u8, 7>::from_array([1, 2, 3]);
    let mut iter = inline.into_iter();
    assert_eq!(iter.len(), 3);
    assert_eq!(iter.size_hint(), (3, Some(3)));
    assert_eq!(iter.next(), Some(1));
    assert_eq!(iter.next_back(), Some(3));
    assert_eq!(iter.len(), 1);
    assert_eq!(iter.next(), Some(2));
    assert_eq!(iter.next(), None);
    assert_eq!(iter.next(), None);
    assert_eq!(iter.next_back(), None);
    assert_eq!(iter.next_back(), None);
    assert_eq!(iter.size_hint(), (0, Some(0)));

    let inline = InlineVec::<Box<u8>, 3>::from_array([Box::new(1), Box::new(2), Box::new(3)]);
    let mut iter = inline.into_iter();
    assert_eq!(iter.next(), Some(Box::new(1)));
    assert_eq!(iter.next_back(), Some(Box::new(3)));
    assert_eq!(iter.next(), Some(Box::new(2)));
    assert_eq!(iter.next(), None);
    assert_eq!(iter.next(), None);
    assert_eq!(iter.next_back(), None);
    assert_eq!(iter.next_back(), None);

    {
        let inline = InlineVec::<Box<u8>, 3>::from_array([Box::new(1), Box::new(2), Box::new(3)]);
        let mut iter = inline.into_iter();
        assert_eq!(iter.next(), Some(Box::new(1)));
    }
}

#[test]
fn compare() {
    let l = InlineVec::<u8, 7>::from_array([1, 2, 3]);
    assert!(l < inline_vec![15 => 2]);
    assert!(inline_vec![15 => 2] > l);
    assert!(l < inline_vec![15 => 1, 2, 3, 1]);
    assert!(inline_vec![15 => 1, 2, 3, 1] > l);
    assert!(l > inline_vec![15 => 1, 2]);
    assert!(inline_vec![15 => 1, 2] < l);
    assert!(l >= inline_vec![15 => 1, 2, 3]);
    assert!(inline_vec![15 => 1, 2, 3] <= l);
    assert_eq!(l, inline_vec![15 => 1, 2, 3]);

    assert!(l == inline_vec![15 => 1, 2, 3]);
    assert!(l == [1, 2, 3]);
    assert!(l == vec![1, 2, 3]);
    assert!(l == *[1, 2, 3].as_slice());
    assert!(l == [1, 2, 3].as_slice());

    assert!(inline_vec![15 => 1, 2, 3] == l);
    assert!([1, 2, 3] == l);
    assert!(vec![1, 2, 3] == l);
    assert!(*[1, 2, 3].as_slice() == l);
    assert!([1, 2, 3].as_slice() == l);

    assert!(l.eq(&inline_vec![15 => 1, 2, 3]));
    assert!(l.partial_cmp(&inline_vec![15 => 1, 2, 3]).unwrap().is_eq());
    assert!(l.cmp(&inline_vec![7 => 1, 2, 3]).is_eq());
    assert!(l.ne(&inline_vec![15 => 1, 3]));
    assert!(l.partial_cmp(&inline_vec![15 => 1, 3]).unwrap().is_lt());
    assert!(l.cmp(&inline_vec![7 => 1, 3]).is_lt());

    // NaN tests
    let i_f32 = InlineVec::<f32, 7>::from_array([f32::NAN]);
    assert_ne!(i_f32, inline_vec![1 => f32::NAN]);
    assert_ne!(i_f32, [f32::NAN]);
    assert!(!(i_f32 <= inline_vec![1 => f32::NAN]));
    assert!(!(i_f32 >= inline_vec![1 => f32::NAN]));
}

#[test]
fn non_null() {
    let mut inline = InlineVec::<u8, SMALL_CAP>::new();
    assert_eq!(inline.as_ptr(), inline.as_non_null().as_ptr());
}

#[test]
fn split_off() {
    let mut inline = SMALL_FULL;
    let inline2 = inline.split_off(3);
    assert_eq!(inline.len(), 3);
    assert_eq!(inline.as_slice(), &[1, 2, 3]);
    assert_eq!(inline2.len(), 4);
    assert_eq!(inline2.as_slice(), &[4, 5, 6, 7]);

    let inline3 = inline.split_off(3);
    assert!(inline3.is_empty());
}

#[test]
#[should_panic(expected = "index out of bounds")]
fn split_off_out_of_bounds() {
    const CAP: usize = 7;
    let mut inline = InlineVec::<u8, CAP>::new();
    for i in 1..=CAP {
        inline.push(i as u8);
        assert_eq!(inline.len(), i);
    }
    assert_eq!(inline.len(), CAP);
    let _ = inline.split_off(8);
}

#[test]
fn resize() {
    const CAP: usize = 7;
    let mut inline = InlineVec::<u8, CAP>::new();
    for i in 1..=CAP {
        inline.push(i as u8);
        assert_eq!(inline.len(), i);
    }
    assert_eq!(inline.len(), CAP);
    inline.resize(3, 0);
    assert_eq!(inline.len(), 3);
    assert_eq!(inline.as_slice(), &[1, 2, 3]);

    inline.resize(5, 42);
    assert_eq!(inline.len(), 5);
    assert_eq!(inline.as_slice(), &[1, 2, 3, 42, 42]);

    inline.resize(CAP, 33);
    assert_eq!(inline.len(), CAP);
    assert_eq!(inline.as_slice(), &[1, 2, 3, 42, 42, 33, 33]);
}

#[test]
#[should_panic(expected = "new length exceeds capacity")]
fn resize_exceeds_capacity() {
    const CAP: usize = 7;
    let mut inline = InlineVec::<u8, CAP>::new();
    inline.resize(CAP + 1, 0);
}

#[test]
fn deref() {
    let mut inline = InlineVec::<u8, 7>::from_array([1, 2, 3]);
    let slice: &[u8] = &inline;
    assert!(ptr::eq(slice, inline.as_slice()));
    let slice: &mut [u8] = &mut inline;
    assert!(ptr::eq(slice, inline.as_mut_slice()));
}

#[test]
fn as_ref() {
    let inline = InlineVec::<u8, 7>::from_array([1, 2, 3]);
    let slice: &[u8] = inline.as_ref();
    assert!(ptr::eq(slice, inline.as_slice()));
}

#[test]
fn as_mut() {
    let mut inline = InlineVec::<u8, 7>::from_array([1, 2, 3]);
    let slice: &mut [u8] = inline.as_mut();
    assert!(ptr::eq(slice, inline.as_mut_slice()));
}

#[test]
fn debug() {
    let inline = InlineVec::<u8, 7>::from_array([1, 2, 3]);
    let debug = format!("{:?}", inline);
    assert_eq!(debug, "[1, 2, 3]");

    let inline = InlineVec::<Box<u8>, 3>::from_array([Box::new(1), Box::new(2)]);
    let debug = format!("{:?}", inline);
    assert_eq!(debug, "[1, 2]");
}

#[test]
#[cfg(feature = "std")]
fn hash() {
    let slice: &[u8] = &[1, 2, 3];
    let inline = InlineVec::<u8, 7>::from_slice_copy(slice);
    let default_hasher = std::hash::BuildHasherDefault::<std::hash::DefaultHasher>::new();
    let value = default_hasher.hash_one(&inline);
    let expected = default_hasher.hash_one(slice);
    assert_eq!(value, expected);

    let empty: &[u8] = &[];
    let inline = InlineVec::<u8, 7>::from_slice_copy(empty);
    let default_hasher = std::hash::BuildHasherDefault::<std::hash::DefaultHasher>::new();
    let value = default_hasher.hash_one(&inline);
    let expected = default_hasher.hash_one(empty);
    assert_eq!(value, expected);
}

#[test]
fn clone() {
    let inline = InlineVec::<u8, 7>::from_array([1, 2, 3]);
    let clone = inline.clone();
    assert_eq!(inline.as_slice(), clone.as_slice());

    let inline = InlineVec::<Box<u8>, 3>::from_array([1, 2].map(Box::new));
    let clone = inline.clone();
    assert_eq!(inline.as_slice(), clone.as_slice());
    assert!(!ptr::eq(&inline[0], &clone[0]));
    assert!(!ptr::eq(&inline[1], &clone[1]));
}

#[test]
fn drain() {
    let mut inline = SMALL_FULL;
    {
        let mut drain = inline.drain(2..5);
        assert_eq!(drain.len(), 3);
        assert_eq!(drain.size_hint(), (3, Some(3)));
        assert_eq!(drain.next(), Some(3));
        assert_eq!(drain.len(), 2);
        assert_eq!(drain.next_back(), Some(5));
        assert_eq!(drain.next(), Some(4));
        assert_eq!(drain.next(), None);
        assert_eq!(drain.next(), None);
        assert_eq!(drain.next_back(), None);
        assert_eq!(drain.next_back(), None);
    }

    assert_eq!(inline.as_slice(), [1, 2, 6, 7]);
    assert_eq!(inline.len(), 4);

    let mut inline = InlineVec::<_, 7>::from_array([1, 2, 3, 4].map(Box::new));
    let _ = inline.drain(2..3);
    assert_eq!(inline.as_slice(), [1, 2, 4].map(Box::new));

    let v: Vec<_> = inline.drain(..).collect();
    assert_eq!(v, [1, 2, 4].map(Box::new));
    assert_eq!(inline.len(), 0);
}

#[test]
#[should_panic(expected = "start index 2 is greater than end index 1")]
fn drain_start_after_end() {
    let mut inline = SMALL_FULL;
    assert_eq!(inline.len(), SMALL_CAP);
    let _ = inline.drain(2..1);
}

#[test]
#[should_panic(expected = "end index 8 is out of bounds for slice of length 7")]
fn drain_end_out_of_bounds() {
    let mut inline = SMALL_FULL;
    assert_eq!(inline.len(), SMALL_CAP);
    let _ = inline.drain(2..8);
}

#[test]
fn append() {
    let mut inline = InlineVec::<u8, 7>::from_array([1, 2, 3]);
    let mut inline2 = InlineVec::<u8, 7>::from_array([4, 5, 6]);
    inline.append(&mut inline2);
    assert_eq!(inline.as_slice(), &[1, 2, 3, 4, 5, 6]);
    assert_eq!(inline.len(), 6);
    assert_eq!(inline2.len(), 0);

    let mut inline = InlineVec::<u8, 7>::from_array([1, 2, 3]);
    let mut v = vec![4, 5, 6];
    inline.append(&mut v);
    assert_eq!(inline.as_slice(), &[1, 2, 3, 4, 5, 6]);
    assert_eq!(inline.len(), 6);
    assert_eq!(v.len(), 0);

    let mut inline = InlineVec::<u8, 7>::from_array([1, 2, 3]);
    let mut v = thin_vec![4, 5, 6];
    inline.append(&mut v);
    assert_eq!(inline.as_slice(), &[1, 2, 3, 4, 5, 6]);
    assert_eq!(inline.len(), 6);
    assert_eq!(v.len(), 0);
}

#[test]
#[should_panic(expected = "new length exceeds capacity")]
fn append_overflows() {
    let mut inline = InlineVec::<u8, 7>::from_array([1, 2, 3, 4]);
    let mut inline2 = InlineVec::<u8, 7>::from_array([5, 6, 7, 8]);
    inline.append(&mut inline2);
}

#[test]
#[should_panic(expected = "new length exceeds capacity")]
fn append_vec_overflows() {
    let mut inline = InlineVec::<u8, 7>::from_array([1, 2, 3, 4]);
    let mut v = vec![5, 6, 7, 8];
    inline.append(&mut v);
}
#[test]
fn const_append() {
    let mut inline1 = InlineVec::<u8, 7>::from_array([1, 2, 3]);
    let mut inline2 = InlineVec::<u8, 7>::from_array([4, 5, 6]);
    inline1.const_append(&mut inline2);
    assert_eq!(inline1.len(), 6);
    assert_eq!(inline2.len(), 0);
}

#[test]
#[should_panic(expected = "new length exceeds capacity")]
fn const_append_panic() {
    let mut inline1 = InlineVec::<u8, 7>::from_array([1, 2, 3]);
    let mut inline2 = InlineVec::<u8, 7>::from_array([4, 5, 6, 7, 8]);
    assert_eq!(inline1.len(), 3);
    assert_eq!(inline2.len(), 5);
    inline1.const_append(&mut inline2);
}

#[test]
fn extend_from_within() {
    let mut inline = InlineVec::<u8, 7>::from_array([1, 2, 3]);
    inline.extend_from_within(..);
    assert_eq!(inline.as_slice(), &[1, 2, 3, 1, 2, 3]);
    assert_eq!(inline.len(), 6);
    inline.extend_from_within(0..1);
    assert_eq!(inline.as_slice(), &[1, 2, 3, 1, 2, 3, 1]);
    assert_eq!(inline.len(), 7);
}

#[test]
#[should_panic(expected = "new length exceeds capacity")]
fn extend_from_within_overflows() {
    let mut inline = InlineVec::<u8, SMALL_CAP>::from_array([1, 2, 3, 4]);
    inline.extend_from_within(..);
}

#[test]
#[should_panic(expected = "start index 1 is greater than end index 0")]
fn extend_from_within_bad_range() {
    let mut inline = InlineVec::<u8, SMALL_CAP>::from_array([1, 2, 3, 4]);
    inline.extend_from_within(1..0);
}

#[test]
fn extend_from_within_copy() {
    let mut inline = InlineVec::<u8, SMALL_CAP>::from_array([1, 2, 3]);
    inline.extend_from_within_copy(..);
    assert_eq!(inline.as_slice(), &[1, 2, 3, 1, 2, 3]);
    assert_eq!(inline.len(), 6);
    inline.extend_from_within_copy(0..1);
    assert_eq!(inline.as_slice(), &[1, 2, 3, 1, 2, 3, 1]);
    assert_eq!(inline.len(), 7);
}

#[test]
#[should_panic(expected = "new length exceeds capacity")]
fn extend_from_within_copy_overflows() {
    let mut inline = InlineVec::<u8, SMALL_CAP>::from_array([1, 2, 3, 4]);
    inline.extend_from_within_copy(..);
}

#[test]
#[should_panic(expected = "start index 1 is greater than end index 0")]
fn extend_from_within_copy_bad_range() {
    let mut inline = InlineVec::<u8, SMALL_CAP>::from_array([1, 2, 3, 4]);
    inline.extend_from_within_copy(1..0);
}

#[test]
fn extend() {
    let mut inline = InlineVec::<u8, SMALL_CAP>::from_array([1, 2, 3]);
    inline.extend(vec![4, 5, 6]);
    assert_eq!(inline.as_slice(), &[1, 2, 3, 4, 5, 6]);
    assert_eq!(inline.len(), 6);
}

#[test]
#[should_panic(expected = "inline vector is full")]
fn extend_overflows() {
    let mut inline = InlineVec::<u8, SMALL_CAP>::from_array([1, 2, 3, 4]);
    inline.extend([5, 6, 7, 8]);
}

#[test]
fn from_iter() {
    let inline = InlineVec::<u8, SMALL_CAP>::from_iter([1, 2, 3]);
    assert_eq!(inline.len(), 3);
    assert_eq!(inline.as_slice(), &[1, 2, 3]);
}

#[test]
#[should_panic(expected = "inline vector is full")]
fn from_iter_overflows() {
    let inline = InlineVec::<u8, SMALL_CAP>::from_iter([1, 2, 3, 4, 5, 6, 7, 8]);
    assert_eq!(inline.len(), 8);
    assert_eq!(inline.as_slice(), &[1, 2, 3, 4, 5, 6, 7, 8]);
}

#[test]
fn from_impls() {
    let boxed: Box<[u8]> = Box::new([1, 2, 3]);
    let inline = InlineVec::<u8, 7>::from(boxed);
    assert_eq!(inline.len(), 3);
    assert_eq!(inline.as_slice(), &[1, 2, 3]);

    let inline = InlineVec::<u8, 7>::from([1, 2, 3]);
    assert_eq!(inline.as_slice(), &[1, 2, 3]);

    let inline = InlineVec::<u8, 7>::from([1, 2, 3].as_slice());
    assert_eq!(inline.as_slice(), &[1, 2, 3]);

    let inline = InlineVec::<u8, 7>::from([1, 2, 3].as_mut_slice());
    assert_eq!(inline.as_slice(), &[1, 2, 3]);

    let inline = InlineVec::<u8, 7>::from(&[1, 2, 3]);
    assert_eq!(inline.as_slice(), &[1, 2, 3]);

    let inline = InlineVec::<u8, 7>::from(&mut [1, 2, 3]);
    assert_eq!(inline.as_slice(), &[1, 2, 3]);

    let inline = InlineVec::<u8, 7>::from(vec![1, 2, 3]);
    assert_eq!(inline.as_slice(), &[1, 2, 3]);

    let inline = InlineVec::<u8, 7>::from(thin_vec![1, 2, 3]);
    assert_eq!(inline.as_slice(), &[1, 2, 3]);

    let inline = InlineVec::<u8, 7>::from(Cow::Borrowed([1, 2, 3].as_slice()));
    assert_eq!(inline.as_slice(), &[1, 2, 3]);

    let inline = InlineVec::<u8, 7>::from(Cow::Owned(vec![1, 2, 3]));
    assert_eq!(inline.as_slice(), &[1, 2, 3]);

    let inline = InlineVec::<u8, 7>::from(thin_vec![1, 2, 3]);
    assert_eq!(inline.as_slice(), &[1, 2, 3]);

    let arr = [Box::new(1)];
    let p = &raw const *arr[0];
    let v = InlineVec::<Box<i32>, 3>::from(arr);
    assert_eq!(&raw const *v[0], p);

    let vec = vec![Box::new(1)];
    let p = &raw const *vec[0];
    let v = InlineVec::<Box<i32>, 3>::from(vec);
    assert_eq!(&raw const *v[0], p);

    let cow: Cow<'_, [Box<i32>]> = Cow::Owned(vec![Box::new(1)]);
    let p = &raw const *cow[0];
    let v = InlineVec::<Box<i32>, 3>::from(cow);
    assert_eq!(&raw const *v[0], p);
}

#[test]
#[should_panic(expected = "new length exceeds capacity")]
fn from_slice_panic() {
    let _ = InlineVec::<u8, 7>::from([1, 2, 3, 4, 5, 6, 7, 8].as_slice());
}

#[test]
#[should_panic(expected = "vector's length exceeds capacity")]
fn from_vec_panic() {
    let _ = InlineVec::<u8, 7>::from(vec![1, 2, 3, 4, 5, 6, 7, 8]);
}
