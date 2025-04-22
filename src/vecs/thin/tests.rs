#![allow(clippy::reversed_empty_ranges)]

use alloc::borrow::Cow;
use alloc::boxed::Box;
use alloc::vec::Vec;
use alloc::{format, vec};
use core::cmp::Ordering;
use core::num::NonZeroI32;
use core::ops::Bound;
use core::{iter, ptr};

use crate::common::traits::tests::test_mut_vector;
use crate::common::traits::MutVector;
use crate::common::{self, RangeError};
use crate::vecs::thin::{Reserved, ThinVec as GenericThinVec};
use crate::vecs::ThinVec;
use crate::{thin_vec, Arc};

#[test]
fn new() {
    let v = ThinVec::<()>::with_capacity(0);
    assert_eq!(v.capacity(), usize::MAX);
    assert_eq!(v.len(), 0);

    let v = ThinVec::<i32>::with_capacity(10);
    assert!(v.capacity() >= 10);
    assert_eq!(v.len(), 0);

    let v = ThinVec::<i32>::new();
    assert_eq!(v.len(), 0);
}

#[test]
fn froms() {
    let b: Box<[i32]> = Box::new([1, 2, 3]);
    let v = ThinVec::from(b);
    assert_eq!(v.as_slice(), &[1, 2, 3]);

    let v = ThinVec::from([1, 2, 3]);
    assert_eq!(v.as_slice(), &[1, 2, 3]);

    let v = ThinVec::from(&[1, 2, 3]);
    assert_eq!(v.as_slice(), &[1, 2, 3]);

    let v = ThinVec::from(&mut [1, 2, 3]);
    assert_eq!(v.as_slice(), &[1, 2, 3]);

    let v = ThinVec::from([1, 2, 3].as_slice());
    assert_eq!(v.as_slice(), &[1, 2, 3]);

    let v = ThinVec::from([1, 2, 3].as_mut_slice());
    assert_eq!(v.as_slice(), &[1, 2, 3]);

    let v = ThinVec::from(vec![1, 2, 3]);
    assert_eq!(v.as_slice(), &[1, 2, 3]);

    let v = ThinVec::from(Cow::Borrowed([1, 2, 3].as_slice()));
    assert_eq!(v.as_slice(), &[1, 2, 3]);

    let v = ThinVec::from(Cow::Owned(vec![1, 2, 3]));
    assert_eq!(v.as_slice(), &[1, 2, 3]);

    let v = ThinVec::from(crate::inline_vec![7 => 1, 2, 3]);
    assert_eq!(v.as_slice(), &[1, 2, 3]);

    let arr = [Box::new(1)];
    let p = &raw const *arr[0];
    let v = ThinVec::from(arr);
    assert_eq!(&raw const *v[0], p);

    let boxed: Box<[Box<i32>]> = Box::new([Box::new(1)]);
    let p = &raw const *boxed[0];
    let v = ThinVec::from(boxed);
    assert_eq!(&raw const *v[0], p);

    let vec = vec![Box::new(1)];
    let p = &raw const *vec[0];
    let v = ThinVec::from(vec);
    assert_eq!(&raw const *v[0], p);

    let cow: Cow<'_, [Box<i32>]> = Cow::Owned(vec![Box::new(1)]);
    let p = &raw const *cow[0];
    let v = ThinVec::from(cow);
    assert_eq!(&raw const *v[0], p);
}

#[test]
fn from_array() {
    let array: [_; 10] = core::array::from_fn(|i| Box::new(i));
    let _ = ThinVec::from_array(array);
}

#[test]
fn push_drop() {
    struct S<'a>(&'a mut i32);
    impl Drop for S<'_> {
        fn drop(&mut self) {
            *self.0 += 1;
        }
    }
    let mut a = 1;
    let mut b = 2;
    let mut c = 3;

    {
        let mut v = ThinVec::new();
        v.push(S(&mut a));
        v.push(S(&mut b));
        v.push(S(&mut c));
        assert_eq!(v.len(), 3);
    }

    assert_eq!(a, 2);
    assert_eq!(b, 3);
    assert_eq!(c, 4);
}

#[test]
fn push() {
    let mut v = ThinVec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    assert_eq!(v.as_slice(), [1, 2, 3]);
    assert_eq!(v.pop(), Some(3));
    assert_eq!(v.pop(), Some(2));
    assert_eq!(v.pop(), Some(1));
    assert_eq!(v.pop(), None);
}

#[test]
fn from_slice_copy() {
    let array: [_; 10] = core::array::from_fn(|i| i);
    let v = ThinVec::from_slice_copy(&array);
    assert_eq!(v.as_slice(), array);
}

#[test]
fn from_slice_clone() {
    let array: [_; 10] = core::array::from_fn(|i| i);
    let v = ThinVec::from_slice_clone(&array);
    assert_eq!(v.as_slice(), array);

    let array: [_; 10] = core::array::from_fn(|i| Box::new(i));
    let v = ThinVec::from_slice_clone(&array);
    assert_eq!(v.as_slice(), array);
}

#[test]
#[cfg(feature = "std")]
fn from_slice_clone_panic() {
    static CLONE_COUNT: std::sync::Mutex<usize> = std::sync::Mutex::new(0);
    static DROP_COUNT: std::sync::Mutex<usize> = std::sync::Mutex::new(0);

    struct S(bool);
    impl Drop for S {
        fn drop(&mut self) {
            // witness the drop
            *DROP_COUNT.lock().unwrap() += 1;
        }
    }
    impl Clone for S {
        fn clone(&self) -> Self {
            *CLONE_COUNT.lock().unwrap() += 1;
            if self.0 {
                panic!();
            }
            Self(self.0)
        }
    }

    *CLONE_COUNT.lock().unwrap() = 0;
    *DROP_COUNT.lock().unwrap() = 0;

    let array: [_; 4] = [false, false, true, false].map(S);
    let r = std::panic::catch_unwind(|| {
        let _ = ThinVec::from(array.as_slice());
    })
    .unwrap_err();

    assert_eq!(*CLONE_COUNT.lock().unwrap(), 3);
    assert_eq!(*DROP_COUNT.lock().unwrap(), 2);
}

#[test]
#[cfg(feature = "std")]
fn from_slice_clone_panic_non_drop() {
    #[derive(Debug)]
    struct S(bool);
    impl Clone for S {
        fn clone(&self) -> Self {
            if self.0 {
                panic!();
            }
            Self(self.0)
        }
    }
    let array: [_; 4] = [false, false, true, false].map(S);
    let _r = std::panic::catch_unwind(|| ThinVec::from(array.as_slice())).unwrap_err();
}

#[test]
#[should_panic]
fn with_capacity_overflow() {
    let _ = ThinVec::<u8>::with_capacity(isize::MAX as usize);
}

#[test]
fn reserve() {
    let mut v = thin_vec![1, 2, 3];
    v.reserve(100);
    assert!(v.capacity() >= 103);
    let p = v.as_ptr();
    v.reserve(100);
    assert_eq!(p, v.as_ptr());
}

#[test]
#[should_panic]
fn reserve_overflow() {
    let mut v = ThinVec::<u8>::new();
    v.reserve(isize::MAX as usize);
}

#[test]
fn reserve_exact() {
    let mut v = thin_vec![1, 2, 3];
    v.reserve_exact(100);
    assert!(v.capacity() >= 103);
    let p = v.as_ptr();
    v.reserve_exact(100);
    assert_eq!(p, v.as_ptr());
}

#[test]
#[should_panic]
fn reserve_exact_overflow() {
    let mut v = ThinVec::<u8>::new();
    v.reserve_exact(isize::MAX as usize);
}

#[test]
fn truncate() {
    let mut v = thin_vec![1, 2, 3];
    v.truncate(4);
    assert_eq!(v.as_slice(), &[1, 2, 3]);
    v.truncate(1);
    assert_eq!(v.as_slice(), &[1]);
    v.truncate(0);
    assert!(v.is_empty());
}

#[test]
fn insert() {
    let mut v = thin_vec!['a', 'c', 'd'];
    v.insert(1, 'b');
    assert_eq!(v, ['a', 'b', 'c', 'd']);
    v.insert(4, 'e');
    assert_eq!(v, ['a', 'b', 'c', 'd', 'e']);
}

#[test]
#[should_panic]
fn insert_out_of_bound() {
    let mut v = thin_vec!['a', 'b', 'c'];
    v.insert(4, 'e');
}

#[test]
fn drain() {
    let mut v = thin_vec![1, 2, 3, 4, 5];
    {
        let mut d = v.drain(1..4);
        assert_eq!(d.as_slice(), &[2, 3, 4]);
        assert_eq!(d.next(), Some(2));
        assert_eq!(d.next(), Some(3));
        assert_eq!(d.next(), Some(4));
        assert_eq!(d.next(), None);
    }
    assert_eq!(v.as_slice(), &[1, 5]);
}

#[test]
fn drain_debug() {
    let mut v = thin_vec![1, 2, 3, 4, 5];
    {
        let mut d = v.drain(1..4);
        assert_eq!(format!("{d:?}"), "Drain([2, 3, 4])");
    }
}

#[test]
fn drain_dst() {
    let mut v = thin_vec![(), (), ()];
    assert_eq!(v.drain(..).count(), 3);
    assert_eq!(v.len(), 0);

    let mut v = thin_vec![(), (), ()];
    assert_eq!(v.drain(1..2).count(), 1);
    assert_eq!(v.len(), 2);
}

#[test]
fn drain_drop() {
    struct S<'a>(&'a mut i32);
    impl Drop for S<'_> {
        fn drop(&mut self) {
            *self.0 += 1;
        }
    }
    let mut a = 1;
    let mut b = 2;
    let mut c = 3;

    {
        let mut v = thin_vec![S(&mut a), S(&mut b), S(&mut c)];
        let mut d = v.drain(..);
        let _ = d.next();
    }

    assert_eq!(a, 2);
    assert_eq!(b, 3);
    assert_eq!(c, 4);
}

#[test]
fn drain_dst_forget() {
    let mut v = thin_vec![(), (), ()];
    core::mem::forget(v.drain(..));
    assert_eq!(v.len(), 0);

    let mut v = thin_vec![(), (), ()];
    core::mem::forget(v.drain(1..2));
    assert_eq!(v.len(), 1);
}

#[test]
fn try_drain() {
    let mut v = thin_vec![1, 2, 3, 4, 5];
    {
        let mut d = v.try_drain(1..4).unwrap();
        assert_eq!(d.as_slice(), &[2, 3, 4]);
        assert_eq!(d.next(), Some(2));
        assert_eq!(d.next(), Some(3));
        assert_eq!(d.next(), Some(4));
        assert_eq!(d.next(), None);
    }
    assert_eq!(v.as_slice(), &[1, 5]);

    let mut v = thin_vec![1, 2, 3, 4, 5];
    let err = v.try_drain(4..1).unwrap_err();
    assert_eq!(err, RangeError::StartGreaterThanEnd { start: 4, end: 1 });
    let err = v.try_drain(4..10).unwrap_err();
    assert_eq!(err, RangeError::EndOutOfBounds { end: 10, len: 5 });
    let err = v
        .try_drain((Bound::Excluded(usize::MAX), Bound::Included(4)))
        .unwrap_err();
    assert_eq!(err, RangeError::StartOverflows);
    let err = v.try_drain(..=usize::MAX).unwrap_err();
    assert_eq!(err, RangeError::EndOverflows);
}

#[test]
fn split_off() {
    let mut v = thin_vec![1, 2, 3, 4, 5];
    let w = v.split_off(2);
    assert_eq!(v.as_slice(), &[1, 2]);
    assert_eq!(w.as_slice(), &[3, 4, 5]);

    let mut v = thin_vec![1, 2, 3];
    let w = v.split_off(0);
    assert!(v.is_empty());
    assert_eq!(w.as_slice(), &[1, 2, 3]);

    let mut v = thin_vec![1, 2, 3];
    let w = v.split_off(3);
    assert_eq!(v.as_slice(), &[1, 2, 3]);
    assert!(w.is_empty());
}

#[test]
#[should_panic(expected = "index out of bounds")]
fn split_off_bad_index() {
    let mut v = thin_vec![1, 2, 3];
    v.split_off(4);
}

#[test]
fn pointer() {
    let mut v = thin_vec![1, 2, 3];
    let p = v.as_ptr();
    assert_eq!(p, v.as_mut_ptr());
    assert_eq!(p, v.ptr().as_ptr());
    assert_eq!(p, v.as_slice().as_ptr());
}

#[test]
fn remove() {
    let mut v = thin_vec![1, 2, 3, 4, 5];
    assert_eq!(v.remove(2), 3);
    assert_eq!(v.as_slice(), &[1, 2, 4, 5]);
    assert_eq!(v.remove(3), 5);
    assert_eq!(v.as_slice(), &[1, 2, 4]);
    assert_eq!(v.remove(0), 1);
    assert_eq!(v.as_slice(), &[2, 4]);
}

#[test]
#[should_panic(expected = "index out of bounds")]
fn remove_out_of_bounds() {
    let mut v = thin_vec![1, 2, 3];
    v.remove(3);
}

#[test]
fn swap_remove() {
    let mut v = thin_vec![1, 2, 3, 4, 5];
    assert_eq!(v.swap_remove(2), 3);
    assert_eq!(v.as_slice(), &[1, 2, 5, 4]);
    assert_eq!(v.swap_remove(3), 4);
    assert_eq!(v.as_slice(), &[1, 2, 5]);
    assert_eq!(v.swap_remove(0), 1);
    assert_eq!(v.as_slice(), &[5, 2]);
    assert_eq!(v.swap_remove(0), 5);
    assert_eq!(v.as_slice(), &[2]);
    assert_eq!(v.swap_remove(0), 2);
    assert!(v.is_empty());
}

#[test]
#[should_panic(expected = "index out of bounds")]
fn swap_remove_out_of_bounds() {
    let mut v = thin_vec![1, 2, 3];
    v.swap_remove(3);
}

#[test]
fn append() {
    let mut a = thin_vec![1, 2, 3];
    let mut b = thin_vec![4, 5, 6];
    a.append(&mut b);
    assert_eq!(a.as_slice(), &[1, 2, 3, 4, 5, 6]);
    assert!(b.is_empty());

    let mut a = thin_vec![1, 2, 3];
    let mut b = vec![4, 5, 6];
    a.append(&mut b);
    assert_eq!(a.as_slice(), &[1, 2, 3, 4, 5, 6]);
    assert!(b.is_empty());
}

#[test]
fn clear() {
    let mut v = thin_vec![1, 2, 3];
    v.clear();
    assert!(v.is_empty());
}

#[test]
fn space_capacity_set_len() {
    let mut v = ThinVec::with_capacity(10);
    assert!(v.capacity() >= 10);
    v.push(1);
    {
        let spare = v.spare_capacity_mut();
        assert!(spare.len() >= 9);
        spare[0].write(2);
        spare[1].write(3);
    }
    unsafe {
        v.set_len(3);
    }
    assert_eq!(v, [1, 2, 3]);
}

#[test]
fn resize() {
    let mut v = thin_vec![1, 2, 3];
    v.resize(5, 0);
    assert_eq!(v.as_slice(), &[1, 2, 3, 0, 0]);
    v.resize(2, 0);
    assert_eq!(v.as_slice(), &[1, 2]);
    v.resize(0, 0);
    assert!(v.is_empty());
}

#[test]
fn extend_from_within() {
    let mut v = thin_vec![1, 2, 3];
    v.extend_from_within(0..3);
    assert_eq!(v, [1, 2, 3, 1, 2, 3]);
    v.extend_from_within(0..0);
    assert_eq!(v, [1, 2, 3, 1, 2, 3]);
    v.extend_from_within(0..1);
    assert_eq!(v, [1, 2, 3, 1, 2, 3, 1]);
}

#[test]
#[should_panic(expected = "end index 4 is out of bounds for slice of length 3")]
fn extend_from_within_bad_range() {
    let mut v = thin_vec![1, 2, 3];
    v.extend_from_within(0..4);
}

#[test]
fn try_extend_from_within() {
    let mut v = thin_vec![1, 2, 3];
    v.try_extend_from_within(0..3).unwrap();
    assert_eq!(v, [1, 2, 3, 1, 2, 3]);
    v.try_extend_from_within(0..0).unwrap();
    assert_eq!(v, [1, 2, 3, 1, 2, 3]);
    v.try_extend_from_within(0..1).unwrap();
    assert_eq!(v, [1, 2, 3, 1, 2, 3, 1]);
    assert_eq!(
        v.try_extend_from_within(1..0).unwrap_err(),
        RangeError::StartGreaterThanEnd { start: 1, end: 0 }
    );
}

#[test]
fn shrink_to_fit() {
    let mut v = ThinVec::<u64>::with_capacity(50);
    assert_eq!(v.capacity(), 50);
    v.push(1);
    v.shrink_to_fit();
    assert_eq!(v.capacity(), 1);
    assert_eq!(v, [1]);
    v.push(2);
    v.push(3);
    assert_eq!(v, [1, 2, 3]);
    let cap = v.capacity();

    v.shrink_to_fit();
    assert!(v.capacity() < cap);
    assert_eq!(v, [1, 2, 3]);

    let mut v = thin_vec![42; 128];
    v.shrink_to_fit();
    assert_eq!(v.capacity(), 128);
    v.shrink_to_fit(); // should do nothing
    assert_eq!(v.capacity(), 128);
}

#[test]
fn shrink_to() {
    // use u64 to avoid the roundup to word alignment
    let mut v = thin_vec![1_u64, 2, 3, 4, 5];
    v.shrink_to(3);
    let cap = v.capacity();
    assert!(v.capacity() >= 5);
    assert_eq!(v, [1, 2, 3, 4, 5]);

    v.push(6);
    v.shrink_to(7);
    assert_eq!(v.capacity(), 7);

    v.shrink_to(7); // should do nothing
    assert_eq!(v.capacity(), 7);
}

#[test]
fn extend() {
    let mut v = thin_vec![1, 2, 3];
    v.extend([4, 5, 6]);
    assert_eq!(v, [1, 2, 3, 4, 5, 6]);

    let mut v = thin_vec![];
    v.extend(iter::repeat_n(42, 42));
    assert_eq!(v.len(), 42);
    assert_eq!(v, [42; 42]);

    let mut v = thin_vec![1, 2, 3];
    v.extend(iter::empty());
    assert_eq!(v, [1, 2, 3]);

    let mut v = thin_vec![1, 2, 3];
    let iter = (0..).take_while(|n| *n < 10);
    assert_eq!(iter.size_hint(), (0, None));
    v.extend(iter);
    assert_eq!(v.len(), 13);
}

#[test]
fn eq() {
    const ARR: [i32; 3] = [1, 2, 3];
    #[derive(Debug)]
    struct S(i32);
    const ARR_S: [S; 3] = [S(1), S(2), S(3)];
    impl PartialEq<i32> for S {
        fn eq(&self, other: &i32) -> bool {
            self.0 == *other
        }
    }
    impl PartialEq<S> for i32 {
        fn eq(&self, other: &S) -> bool {
            *self == other.0
        }
    }

    let a = thin_vec![1, 2, 3];
    let b = ThinVec::from_array(ARR);

    assert_eq!(a, b);
    assert_eq!(a, ARR);
    assert_eq!(a, ARR.as_slice());
    let mut arr = ARR;
    assert_eq!(a, arr.as_mut_slice());
    assert_eq!(a, Vec::from(ARR));

    let c = ThinVec::from_array(ARR_S);
    assert_eq!(a, c);
    assert_eq!(a, ARR_S);
    assert_eq!(a, ARR_S.as_slice());
    let mut arr = ARR;
    assert_eq!(a, arr.as_mut_slice());
    assert_eq!(a, Vec::from(ARR_S));
}

#[test]
fn ord() {
    let a = thin_vec![1, 2, 3];
    assert!(a < thin_vec![1, 2, 3, 4]);
    assert!(a < thin_vec![1, 2, 4]);
    assert!(a <= thin_vec![1, 2, 3]);
    assert!(a > thin_vec![0]);
    assert!(a > thin_vec![1, 2, 2]);
    assert!(a >= thin_vec![1, 2, 3]);
    assert_eq!(a.partial_cmp(&thin_vec![1, 2, 3]).unwrap(), Ordering::Equal);
    assert_eq!(a.cmp(&thin_vec![1, 2, 3]), Ordering::Equal);

    let mut arr = [1, 2, 3];
    assert!(a.partial_cmp(&arr).unwrap() == Ordering::Equal);
    assert!(a.partial_cmp(arr.as_slice()).unwrap() == Ordering::Equal);
    assert!(a.partial_cmp(&arr.as_slice()).unwrap() == Ordering::Equal);
    assert!(a.partial_cmp(&arr.as_mut_slice()).unwrap() == Ordering::Equal);
    assert!(a.partial_cmp(&Vec::from(arr)).unwrap() == Ordering::Equal);
    assert!(a <= arr);
}

#[test]
fn deref_mut() {
    let mut v = thin_vec![1, 2, 3];
    let ptr: *const [i32] = v.as_slice();
    let slice: &mut [i32] = &mut v;
    assert!(ptr::eq(slice, ptr)); // stable deref
}

#[test]
fn prefix() {
    let v = thin_vec![1, 2, 3];
    let &Reserved::Reserved = v.prefix();

    let v: GenericThinVec<_, ()> = GenericThinVec::from([1, 2, 3]);
    let &() = v.prefix();
}

#[test]
fn extend_from_slice() {
    let mut v = thin_vec![1, 2, 3];
    v.extend_from_slice(&[4, 5, 6]);
    assert_eq!(v.as_slice(), &[1, 2, 3, 4, 5, 6]);

    let mut v = thin_vec![];
    v.extend_from_slice(&[42; 42]);
    assert_eq!(v.len(), 42);
    assert_eq!(v.as_slice(), [42; 42]);

    let mut v = thin_vec![1, 2, 3];
    v.extend_from_slice(&[]);
    assert_eq!(v.as_slice(), &[1, 2, 3]);
}

#[test]
fn extend_from_slice_copy() {
    let array: [_; 10] = core::array::from_fn(|i| i);
    let mut v = ThinVec::new();
    v.extend_from_slice_copy(&array);
    assert_eq!(v.as_slice(), array);
}

#[test]
fn debug() {
    let v = thin_vec![1, 2, 3];
    assert_eq!(format!("{v:?}"), "[1, 2, 3]");
    let v: GenericThinVec<i32, ()> = GenericThinVec::from([1, 2, 3]);
    assert_eq!(format!("{v:?}"), "[1, 2, 3]");
}

#[test]
fn generic_vector() {
    let mut v = thin_vec![1, 2, 3];
    let cap = v.capacity();
    let len = v.len();
    let ptr: *const i32 = v.as_ptr();

    test_mut_vector(v, cap, len, ptr);
}

#[test]
fn layout() {
    let (_, offset, capacity) = ThinVec::<u128>::layout(0).unwrap();
    assert_eq!(capacity, 0);
    assert_eq!(offset % align_of::<u128>(), 0);

    let (_, _, capacity) = ThinVec::<u8>::layout(1).unwrap();
    assert!(capacity > 1, "{capacity} should be rounded up");

    assert!(ThinVec::<u8>::layout(usize::MAX).is_none());
    assert!(ThinVec::<u128>::layout(usize::MAX / size_of::<u128>()).is_none());
}

#[test]
fn from_iterator() {
    let v: ThinVec<_> = (1..=10).collect();
    assert_eq!(v.as_slice(), &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);

    let v: ThinVec<_> = (1..=10).filter(|x| *x % 2 == 0).collect();
    assert_eq!(v.as_slice(), &[2, 4, 6, 8, 10]);
}

#[test]
fn clone() {
    let v: ThinVec<u8> = (1..=10).collect();
    let v2 = v.clone();
    assert_eq!(v.as_slice(), v2.as_slice());
    assert_ne!(v.as_ptr(), v2.as_ptr());

    let v: ThinVec<Box<u8>> = thin_vec![Box::new(1)];
    let p = &raw const *v[0];
    let v2 = v.clone();
    assert_eq!(v[0], v2[0]);
    assert_ne!(&raw const *v2[0], p);
}

#[test]
fn fresh_move() {
    #[derive(Default)]
    #[repr(u8)]
    enum DistinctLayout {
        A,
        #[default]
        B,
    }
    let v: ThinVec<u8> = (1..=10).collect();
    let p = v.as_ptr();
    let v2: GenericThinVec<u8, DistinctLayout> = v.fresh_move();
    assert_ne!(v2.as_ptr(), p);

    #[derive(Default)]
    #[repr(usize)]
    enum SameLayout {
        A,
        #[default]
        B,
    }

    let v: GenericThinVec<u8> = (1..=10).collect();
    let p = v.as_ptr();
    let v2: GenericThinVec<u8, SameLayout> = v.fresh_move();
    assert_eq!(v2.as_ptr(), p);
}

#[test]
#[cfg(feature = "std")]
fn fresh_move_drop_prefix() {
    use std::sync::Mutex;
    static WITNESS: Mutex<bool> = Mutex::new(false);
    #[derive(Default)]
    struct S;
    impl Drop for S {
        fn drop(&mut self) {
            *WITNESS.lock().unwrap() = true;
        }
    }
    *WITNESS.lock().unwrap() = false;

    let v: GenericThinVec<u8, S> = (1..=10).collect();
    let p = v.as_ptr();
    let v2: GenericThinVec<u8, ()> = v.fresh_move();
    assert_eq!(v2.as_ptr(), p);
    assert_eq!(v2.prefix(), &());
    assert!(*WITNESS.lock().unwrap());
}
