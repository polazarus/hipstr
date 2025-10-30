use alloc::vec;
use alloc::vec::Vec;
use core::ptr;
use core::sync::atomic::AtomicBool;

use const_default::ConstDefault;

use super::WideVec;
use crate::common::traits::Mutate;

type V<T> = WideVec<T, ()>;

#[test]
fn new() {
    let mut v: V<i32> = V::new();
    assert_eq!(v.len(), 0);
    assert_eq!(v.capacity(), 0);
    assert!(v.is_empty());

    assert!(v.0.is_null());
    assert!(v.prefix().is_none());
    assert!(v.prefix_mut().is_none());
}

#[test]
fn from_vec() {
    let vec = vec![1, 2, 3];
    let p = vec.as_ptr();

    let mut wide_vec: V<i32> = V::from(vec);
    assert_eq!(wide_vec.len(), 3);
    assert_eq!(wide_vec.as_slice(), &[1, 2, 3]);
    assert_eq!(wide_vec.as_ptr(), p);

    assert!(wide_vec.capacity() >= 3);

    assert_eq!(wide_vec.prefix(), Some(&()));
    assert_eq!(wide_vec.prefix_mut(), Some(&mut ()));
}

#[test]
fn from_vec_empty() {
    let vec = Vec::new();
    let mut wide_vec: V<i32> = V::from(vec);
    assert_eq!(wide_vec.len(), 0);
    assert!(wide_vec.is_empty());
    assert_eq!(wide_vec.as_ptr(), ptr::dangling());
    assert_eq!(wide_vec.capacity(), 0);
    assert!(wide_vec.0.is_null());

    assert!(wide_vec.prefix().is_none());
    assert!(wide_vec.prefix_mut().is_none());
}

#[test]
fn as_ptr() {
    let vec = vec![1, 2, 3];
    let p = vec.as_ptr();
    let mut wide_vec: V<i32> = V::from(vec);
    assert_eq!(wide_vec.as_mut_ptr().cast_const(), p);
    assert_eq!(wide_vec.as_ptr(), p);

    let mut wide_vec: V<i32> = V::new();
    assert_eq!(wide_vec.as_mut_ptr(), ptr::dangling_mut());
    assert_eq!(wide_vec.as_ptr(), ptr::dangling());
}

#[test]
fn as_slice() {
    let vec = vec![1, 2, 3];
    let p = vec.as_ptr();
    let wide_vec: V<i32> = V::from(vec);
    let slice = wide_vec.as_slice();
    assert_eq!(slice, &[1, 2, 3]);
    assert_eq!(slice.as_ptr(), p);
}

#[test]
fn as_mut_slice() {
    let vec = vec![1, 2, 3];
    let p = vec.as_ptr();
    let mut wide_vec: V<i32> = V::from(vec);
    let slice = wide_vec.as_mut_slice();
    assert_eq!(slice, &[1, 2, 3]);
    assert_eq!(slice.as_ptr(), p);
}

#[test]
fn set_len() {
    let vec = Vec::with_capacity(10);
    let p = vec.as_ptr();
    let mut wide_vec: V<i32> = V::from(vec);
    assert_eq!(wide_vec.len(), 0);
    assert_eq!(wide_vec.as_ptr(), p);
    unsafe {
        wide_vec.as_mut_ptr().add(0).write(1);
        wide_vec.as_mut_ptr().add(1).write(2);
        wide_vec.as_mut_ptr().add(2).write(3);
        wide_vec.as_mut_ptr().add(3).write(4);
        wide_vec.as_mut_ptr().add(4).write(5);
        wide_vec.set_len(5);
    }
    assert_eq!(wide_vec.as_ptr(), p);
}

#[test]
fn set_len_empty() {
    let mut wide_vec: V<i32> = V::DEFAULT;
    assert_eq!(wide_vec.len(), 0);
    unsafe {
        wide_vec.set_len(0);
    }
    assert_eq!(wide_vec.len(), 0);
}

#[test]
#[should_panic(expected = "new length out of bounds")]
fn set_len_out_of_bounds() {
    let vec = Vec::with_capacity(5);
    let mut wide_vec: V<i32> = V::from(vec);
    unsafe {
        wide_vec.set_len(10);
    }
}

#[test]
#[should_panic(expected = "new length out of bounds")]
fn set_len_out_of_bounds_empty() {
    let mut wide_vec: V<i32> = V::DEFAULT;
    unsafe {
        wide_vec.set_len(1);
    }
}

#[test]
fn spare_capacity_mut() {
    let vec = Vec::with_capacity(10);
    let p = vec.as_ptr();
    let mut wide_vec: V<i32> = V::from(vec);
    assert_eq!(wide_vec.len(), 0);
    assert_eq!(wide_vec.as_ptr(), p);
    let spare_capacity = wide_vec.spare_capacity_mut();
    assert_eq!(spare_capacity.len(), 10);
    assert_eq!(spare_capacity.as_ptr(), p.cast());

    for i in 0..10 {
        spare_capacity[i].write((i + 1) as i32);
    }
    unsafe {
        wide_vec.set_len(10);
    }
    assert_eq!(wide_vec.as_ptr(), p);
    assert_eq!(wide_vec.as_slice(), &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
}

#[test]
fn mutate() {
    let v = vec![10, 20];
    let p = v.as_ptr();
    let mut vec: V<i32> = V::from(v);

    {
        let mut ref_mut = vec.mutate();
        ref_mut[0] = 100;
        ref_mut[1] = 200;
        assert_eq!(ref_mut.as_ptr(), p);
    }

    assert_eq!(vec.len(), 2);
    assert_eq!(vec[0], 100);
    assert_eq!(vec[1], 200);
    assert_eq!(vec.as_ptr(), p);
}

#[test]
fn mutate_realloc() {
    let v = vec![0];
    let p = v.as_ptr();
    let mut vec: V<i32> = V::from(v);

    {
        let mut ref_mut = vec.mutate();
        for i in 1..100 {
            ref_mut.push(i);
        }
    }

    assert_eq!(vec.as_slice(), (0..100).collect::<Vec<_>>().as_slice());
    assert_ne!(vec.as_ptr(), p);
}

#[test]
fn mutate_trait() {
    let v = vec![10, 20];
    let p = v.as_ptr();
    let mut vec: V<i32> = V::from(v);
    {
        let mut ref_mut = Mutate::mutate(&mut vec);
        ref_mut[0] = 100;
        ref_mut[1] = 200;
        assert_eq!(ref_mut.as_ptr(), p);
    }
}

#[test]
fn fresh_move_empty() {
    let vec: V<i32> = V::new();
    let vec_moved: WideVec<i32, u32> = vec.fresh_move();
    assert_eq!(vec_moved.len(), 0);
    assert!(vec_moved.is_empty());
    assert_eq!(vec_moved.as_ptr(), ptr::dangling());
    assert_eq!(vec_moved.capacity(), 0);
    assert!(vec_moved.0.is_null());
    assert_eq!(vec_moved.prefix(), None);
}

#[test]
fn fresh_move_non_empty_incompatible() {
    let v = vec![1, 2, 3];
    let p = v.as_ptr();
    let vec: V<i32> = V::from(v);
    let vec_moved: WideVec<i32, u32> = vec.fresh_move();
    assert_eq!(vec_moved.len(), 3);
    assert_eq!(vec_moved.as_slice(), &[1, 2, 3]);
    assert_eq!(vec_moved.as_ptr(), p);
    assert!(vec_moved.capacity() >= 3);
    assert_eq!(vec_moved.prefix(), Some(&0));
}

#[test]
fn fresh_move_non_empty_compatible() {
    let v = vec![1, 2, 3];
    let p = v.as_ptr();
    let mut vec: WideVec<i32, u32> = WideVec::from(v);
    *vec.prefix_mut().unwrap() = 1;

    let vec_moved: WideVec<i32, i32> = vec.fresh_move();
    assert_eq!(vec_moved.len(), 3);
    assert_eq!(vec_moved.as_slice(), &[1, 2, 3]);
    assert_eq!(vec_moved.as_ptr(), p);
    assert!(vec_moved.capacity() >= 3);
    assert_eq!(vec_moved.prefix(), Some(&0));
}

#[test]
#[cfg(feature = "std")]
fn fresh_move_non_empty_compatible_with_drop() {
    use std::sync::atomic::Ordering::SeqCst;
    use std::sync::Mutex;

    #[repr(transparent)]
    struct P(i32);
    impl Drop for P {
        fn drop(&mut self) {
            DROPPED.store(true, SeqCst);
        }
    }
    impl ConstDefault for P {
        const DEFAULT: Self = P(i32::MAX);
    }

    // mutex to ensure there is no multiple instance of this test running at the same time
    static MUTEX: Mutex<()> = Mutex::new(());
    static DROPPED: AtomicBool = AtomicBool::new(false);

    {
        let _lock = MUTEX.lock();
        DROPPED.store(false, SeqCst);

        let v = vec![1, 2, 3];
        let p = v.as_ptr();
        let vec: WideVec<i32, P> = WideVec::from(v);
        let vec_moved: WideVec<i32, i32> = vec.fresh_move();
        assert_eq!(vec_moved.len(), 3);
        assert_eq!(vec_moved.as_ptr(), p);
        assert!(vec_moved.capacity() >= 3);
        assert_eq!(vec_moved.prefix(), Some(&0));
        assert_eq!(DROPPED.load(SeqCst), true);
    }
}

#[test]
fn prefix() {
    let v = vec![1, 2, 3];
    let mut wide_vec: WideVec<i32, u32> = WideVec::from(v);
    assert_eq!(wide_vec.prefix(), Some(&0));
    assert_eq!(wide_vec.prefix_mut(), Some(&mut 0));

    *wide_vec.prefix_mut().unwrap() = 42;
    assert_eq!(wide_vec.prefix(), Some(&42));
}
