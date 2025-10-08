use alloc::vec;
use alloc::vec::Vec;
use core::{mem, ptr};

use super::SmartFatVec;
use crate::backend::PanickyUnique;
use crate::common::traits::Mutate;
use crate::{Arc, Unique};

#[test]
fn new_vec() {
    let vec: SmartFatVec<i32, Arc> = SmartFatVec::new();
    assert_eq!(vec.len(), 0);
    assert!(vec.is_empty());
    assert_ne!(vec.as_ptr(), ptr::null());
    assert_eq!(vec.capacity(), 0);
}

#[test]
fn clone() {
    let vec: SmartFatVec<i32, Arc> = SmartFatVec::from(vec![1, 2, 3]);
    let p = vec.as_ptr();
    assert!(vec.is_unique());

    let vec2 = vec.clone();
    assert_eq!(vec2.as_slice(), &[1, 2, 3]);
    assert_eq!(vec2.as_ptr(), p);
    assert!(!vec.is_unique());
    assert!(!vec2.is_unique());

    drop(vec);
    assert!(vec2.is_unique());
}

#[test]
fn as_mut() {
    let mut vec: SmartFatVec<i32, Arc> = SmartFatVec::from(vec![1, 2, 3]);
    assert!(vec.is_unique());
    assert!(vec.as_mut().is_some());

    {
        let _vec2 = vec.clone();
        assert!(!vec.is_unique());
        assert!(vec.as_mut().is_none());
    }

    {
        let mut v = vec.as_mut().unwrap();
        v.push(4);
    }

    assert_eq!(vec.as_slice(), [1, 2, 3, 4]);
}

#[test]
fn from_vec() {
    let vec = vec![1, 2, 3];
    let p = vec.as_ptr();

    let smart_vec: SmartFatVec<i32, Arc> = SmartFatVec::from(vec);
    assert_eq!(smart_vec.len(), 3);
    assert_eq!(smart_vec[0], 1);
    assert_eq!(smart_vec[1], 2);
    assert_eq!(smart_vec[2], 3);
    assert_eq!(smart_vec.as_ptr(), p);
    assert!(smart_vec.capacity() >= 3);
}

#[test]
fn from_vec_empty() {
    let vec: Vec<i32> = Vec::new();

    let smart_vec: SmartFatVec<i32, Arc> = SmartFatVec::from(vec);
    assert_eq!(smart_vec.len(), 0);
    assert!(smart_vec.is_empty());
    assert_eq!(smart_vec.as_ptr(), ptr::dangling());
    assert_eq!(smart_vec.capacity(), 0);
}

#[test]
fn mutate_unique_empty() {
    let mut vec: SmartFatVec<i32, Arc> = SmartFatVec::new();
    {
        let mut v = vec.mutate();
        v.push(10);
        v.push(20);
        assert_eq!(v.len(), 2);
    }
    assert_eq!(vec.len(), 2);
    assert_eq!(vec[0], 10);
    assert_eq!(vec[1], 20);
}

#[test]
fn mutate_unique_nonempty() {
    let vec = vec![1, 2, 3];
    let capacity = vec.capacity();
    let mut vec: SmartFatVec<i32, Arc> = SmartFatVec::from(vec);

    let p = vec.as_ptr();

    {
        let mut v = vec.mutate();
        assert_eq!(v.as_ptr(), p);
        v.extend_from_slice(&[4, 5, 6, 7, 8, 9, 10]);
        assert_eq!(v.len(), 10);
    }
    assert_eq!(vec.len(), 10);
    assert_eq!(vec.as_slice(), &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
    if capacity >= 10 {
        assert_eq!(vec.as_ptr(), p);
    } else {
        assert_ne!(vec.as_ptr(), p);
    }
}

#[test]
fn mutate_nonunique_nonempty() {
    let mut vec: SmartFatVec<i32, Arc> = SmartFatVec::from(vec![1, 2, 3]);
    let p = vec.as_ptr();

    {
        let vec2 = vec.clone();
        assert_eq!(vec2.as_ptr(), p);

        let mut v = vec.mutate();
        assert_ne!(v.as_ptr(), p);
        v.push(4);
        assert_eq!(v.len(), 4);
    }
    assert_eq!(vec.len(), 4);
    assert_eq!(vec.as_slice(), &[1, 2, 3, 4]);
    assert_ne!(vec.as_ptr(), p);
}

#[test]
fn mutate_nonunique_empty() {
    let mut vec: SmartFatVec<i32, Arc> = SmartFatVec::new();
    let _vec2 = vec.clone();

    {
        let mut v = vec.mutate();
        v.push(10);
        v.push(20);
        assert_eq!(v.len(), 2);
    }
    assert_eq!(vec.len(), 2);
    assert_eq!(vec[0], 10);
    assert_eq!(vec[1], 20);
}

#[test]
fn mutate_swap_nonempty_empty() {
    let mut vec: SmartFatVec<i32, Arc> = SmartFatVec::from(vec![1, 2, 3]);

    {
        let mut ref_mut = vec.mutate();
        let _ = mem::take(&mut *ref_mut);
    }

    assert_eq!(vec.len(), 0);
    assert_eq!(vec.capacity(), 0);
    assert_eq!(vec.as_ptr(), ptr::dangling());
}

#[test]
fn mutate_swap_empty_empty() {
    let mut vec: SmartFatVec<i32, Arc> = SmartFatVec::new();

    {
        let mut ref_mut = vec.mutate();
        let _ = mem::take(&mut *ref_mut);
    }

    assert_eq!(vec.len(), 0);
    assert_eq!(vec.capacity(), 0);
    assert_eq!(vec.as_ptr(), ptr::dangling());
}

#[test]
fn mutate_swap_empty_nonempty() {
    let mut vec: SmartFatVec<i32, Arc> = SmartFatVec::new();

    {
        let mut ref_mut = vec.mutate();
        let _ = mem::replace(&mut *ref_mut, vec![1, 2, 3]);
    }

    assert_eq!(vec.len(), 3);
    assert_eq!(vec.as_slice(), &[1, 2, 3]);
}

#[test]
fn mutate_swap_nonempty_nonempty() {
    let mut vec: SmartFatVec<i32, Arc> = SmartFatVec::from(vec![1, 2, 3]);

    {
        let mut ref_mut = vec.mutate();
        let _ = mem::replace(&mut *ref_mut, vec![4, 5]);
    }

    assert_eq!(vec.len(), 2);
    assert_eq!(vec.as_slice(), &[4, 5]);
}

#[test]
fn mutate_copy_unique_empty() {
    let mut vec: SmartFatVec<i32, Arc> = SmartFatVec::new();
    {
        let mut v = vec.mutate_copy();
        v.push(10);
        v.push(20);
        assert_eq!(v.len(), 2);
    }
    assert_eq!(vec.len(), 2);
    assert_eq!(vec[0], 10);
    assert_eq!(vec[1], 20);
}

#[test]
fn mutate_copy_unique_nonempty() {
    let mut vec = vec![1, 2, 3];
    vec.reserve(1); // make the pointer stable

    let mut vec: SmartFatVec<i32, Arc> = SmartFatVec::from(vec);
    let p = vec.as_ptr();

    {
        let mut v = vec.mutate_copy();
        assert_eq!(v.as_ptr(), p);
        v.push(4);
        assert_eq!(v.len(), 4);
    }
    assert_eq!(vec.len(), 4);
    assert_eq!(vec.as_slice(), &[1, 2, 3, 4]);
    assert_eq!(vec.as_ptr(), p);
}

#[test]
fn mutate_copy_nonunique_nonempty() {
    let mut vec = vec![1, 2, 3];
    vec.reserve(1); // make the pointer stable

    let mut vec: SmartFatVec<i32, Arc> = SmartFatVec::from(vec);
    let p = vec.as_ptr();

    {
        let vec2 = vec.clone();
        assert_eq!(vec2.as_ptr(), p);

        let mut v = vec.mutate_copy();
        assert_ne!(v.as_ptr(), p);
        v.push(4);
        assert_eq!(v.len(), 4);
    }
    assert_eq!(vec.len(), 4);
    assert_eq!(vec.as_slice(), &[1, 2, 3, 4]);
    assert_ne!(vec.as_ptr(), p);
}

#[test]
fn mutate_copy_nonunique_empty() {
    let mut vec: SmartFatVec<i32, Arc> = SmartFatVec::new();
    let _vec2 = vec.clone();

    {
        let mut v = vec.mutate_copy();
        v.push(10);
        v.push(20);
        assert_eq!(v.len(), 2);
    }
    assert_eq!(vec.len(), 2);
    assert_eq!(vec[0], 10);
    assert_eq!(vec[1], 20);
}

#[test]
fn deref() {
    let vec: SmartFatVec<i32, Arc> = SmartFatVec::from(vec![1, 2, 3]);
    let slice: &[i32] = &vec;
    assert_eq!(slice.len(), 3);
    assert_eq!(slice, [1, 2, 3]);
}

#[test]
fn try_clone_arc() {
    let vec: SmartFatVec<i32, Arc> = SmartFatVec::from(vec![1, 2, 3]);
    let p = vec.as_ptr();
    assert!(vec.is_unique());

    let vec2 = vec.try_clone().unwrap();
    assert_eq!(vec2.as_slice(), &[1, 2, 3]);
    assert_eq!(vec2.as_ptr(), p);
    assert!(!vec.is_unique());
    assert!(!vec2.is_unique());

    drop(vec);
    assert!(vec2.is_unique());
}

#[test]
fn try_clone_unique() {
    let vec: SmartFatVec<i32, Unique> = SmartFatVec::from(vec![1, 2, 3]);
    assert!(vec.is_unique());
    assert!(vec.try_clone().is_none());
}

#[test]
#[should_panic(expected = "count overflow")]
fn clone_panic() {
    let vec: SmartFatVec<i32, PanickyUnique> = SmartFatVec::from(vec![1, 2, 3]);
    assert!(vec.is_unique());

    #[allow(clippy::redundant_clone)]
    let _other = vec.clone();
}

#[test]
fn clone_unique() {
    let vec: SmartFatVec<i32, Unique> = SmartFatVec::from(vec![1, 2, 3]);
    assert!(vec.is_unique());
    let vec2 = vec.clone();
    assert_eq!(vec2.as_slice(), &[1, 2, 3]);
    assert!(vec.is_unique());
    assert!(vec2.is_unique());
    assert_ne!(vec.as_ptr(), vec2.as_ptr());
}

#[test]
fn mutate_trait() {
    let mut vec = vec![1, 2, 3];
    vec.reserve(10); // make the pointer stable
    let p = vec.as_ptr();

    let mut vec: SmartFatVec<i32, Unique> = SmartFatVec::from(vec);
    assert!(vec.is_unique());

    {
        let mut r = Mutate::mutate(&mut vec);
        r.push(4);
        assert_eq!(r.as_ptr(), p);
    }

    assert_eq!(vec.as_slice(), [1, 2, 3, 4]);

    let mut vec2 = vec.clone();
    {
        let mut r = Mutate::mutate(&mut vec2);
        r.push(5);
        assert_ne!(r.as_ptr(), p);
    }

    assert_eq!(vec.as_slice(), [1, 2, 3, 4]);
    assert_eq!(vec2.as_slice(), [1, 2, 3, 4, 5]);
}
