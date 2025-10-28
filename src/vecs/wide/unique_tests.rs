use alloc::vec;
use alloc::vec::Vec;
use core::ptr;

use const_default::ConstDefault;

use super::WideVec;
use crate::common::traits::Mutate;

type V<T> = WideVec<T, ()>;

#[test]
fn new() {
    let v: V<i32> = V::new();
    assert_eq!(v.len(), 0);
    assert_eq!(v.capacity(), 0);
    assert!(v.is_empty());

    assert!(v.0.is_null());
}

#[test]
fn from_vec() {
    let vec = vec![1, 2, 3];
    let p = vec.as_ptr();

    let wide_vec: V<i32> = V::from(vec);
    assert_eq!(wide_vec.len(), 3);
    assert_eq!(wide_vec[0], 1);
    assert_eq!(wide_vec[1], 2);
    assert_eq!(wide_vec[2], 3);
    assert_eq!(wide_vec.as_ptr(), p);
    assert!(wide_vec.capacity() >= 3);
}

#[test]
fn from_vec_empty() {
    let vec = Vec::new();
    let wide_vec: V<i32> = V::from(vec);
    assert_eq!(wide_vec.len(), 0);
    assert!(wide_vec.is_empty());
    assert_eq!(wide_vec.as_ptr(), ptr::dangling());
    assert_eq!(wide_vec.capacity(), 0);
    assert!(wide_vec.0.is_null());
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
fn set_len_empty() {
    let mut vec: V<i32> = V::DEFAULT;
    assert_eq!(vec.len(), 0);
    unsafe {
        vec.set_len(0);
    }
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
