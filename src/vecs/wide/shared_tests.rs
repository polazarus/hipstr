use alloc::vec;
use alloc::vec::Vec;
use core::{mem, ptr};

use super::SmartWideVec;
use crate::backend::PanickyUnique;
use crate::common::traits::Mutate;
use crate::common::ZeroUsize;
use crate::vecs::wide::WideVec;
use crate::{Arc, Unique};

#[test]
fn new_vec() {
    let vec: SmartWideVec<i32, Arc> = SmartWideVec::new();
    assert_eq!(vec.len(), 0);
    assert!(vec.is_empty());
    assert_ne!(vec.as_ptr(), ptr::null());
    assert_eq!(vec.capacity(), 0);
}

#[test]
fn clone() {
    let vec: SmartWideVec<i32, Arc> = SmartWideVec::from(vec![1, 2, 3]);
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
    let mut vec: SmartWideVec<i32, Arc> = SmartWideVec::from(vec![1, 2, 3]);
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

    let smart_vec: SmartWideVec<i32, Arc> = SmartWideVec::from(vec);
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

    let smart_vec: SmartWideVec<i32, Arc> = SmartWideVec::from(vec);
    assert_eq!(smart_vec.len(), 0);
    assert!(smart_vec.is_empty());
    assert_eq!(smart_vec.as_ptr(), ptr::dangling());
    assert_eq!(smart_vec.capacity(), 0);
}

#[test]
fn mutate_unique_empty() {
    let mut vec: SmartWideVec<i32, Arc> = SmartWideVec::new();
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
    let mut vec: SmartWideVec<i32, Arc> = SmartWideVec::from(vec);
    {
        let mut v = vec.mutate();
        v.extend_from_slice(&[4, 5, 6, 7, 8, 9, 10]);
        assert_eq!(v.len(), 10);
    }
    assert_eq!(vec.len(), 10);
    assert_eq!(vec.as_slice(), &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
}

#[test]
fn mutate_nonunique_nonempty() {
    let mut vec: SmartWideVec<i32, Arc> = SmartWideVec::from(vec![1, 2, 3]);
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
    let mut vec: SmartWideVec<i32, Arc> = SmartWideVec::new();
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
    let mut vec: SmartWideVec<i32, Arc> = SmartWideVec::from(vec![1, 2, 3]);

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
    let mut vec: SmartWideVec<i32, Arc> = SmartWideVec::new();

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
    let mut vec: SmartWideVec<i32, Arc> = SmartWideVec::new();

    {
        let mut ref_mut = vec.mutate();
        let _ = mem::replace(&mut *ref_mut, vec![1, 2, 3]);
    }

    assert_eq!(vec.len(), 3);
    assert_eq!(vec.as_slice(), &[1, 2, 3]);
}

#[test]
fn mutate_swap_nonempty_nonempty() {
    let mut vec: SmartWideVec<i32, Arc> = SmartWideVec::from(vec![1, 2, 3]);

    {
        let mut ref_mut = vec.mutate();
        let _ = mem::replace(&mut *ref_mut, vec![4, 5]);
    }

    assert_eq!(vec.len(), 2);
    assert_eq!(vec.as_slice(), &[4, 5]);
}

#[test]
fn mutate_copy_unique_empty() {
    let mut vec: SmartWideVec<i32, Arc> = SmartWideVec::new();
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

    let mut vec: SmartWideVec<i32, Arc> = SmartWideVec::from(vec);
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

    let mut vec: SmartWideVec<i32, Arc> = SmartWideVec::from(vec);
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
    let mut vec: SmartWideVec<i32, Arc> = SmartWideVec::new();
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
    let vec: SmartWideVec<i32, Arc> = SmartWideVec::from(vec![1, 2, 3]);
    let slice: &[i32] = &vec;
    assert_eq!(slice.len(), 3);
    assert_eq!(slice, [1, 2, 3]);
}

#[test]
fn try_clone_arc() {
    let vec: SmartWideVec<i32, Arc> = SmartWideVec::from(vec![1, 2, 3]);
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
    let vec: SmartWideVec<i32, Unique> = SmartWideVec::from(vec![1, 2, 3]);
    assert!(vec.is_unique());
    assert!(vec.try_clone().is_none());
}

#[test]
#[should_panic(expected = "count overflow")]
fn clone_panic() {
    let vec: SmartWideVec<i32, PanickyUnique> = SmartWideVec::from(vec![1, 2, 3]);
    assert!(vec.is_unique());

    #[allow(clippy::redundant_clone)]
    let _other = vec.clone();
}

#[test]
fn clone_unique() {
    let vec: SmartWideVec<i32, Unique> = SmartWideVec::from(vec![1, 2, 3]);
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

    let mut vec: SmartWideVec<i32, Unique> = SmartWideVec::from(vec);
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

#[test]
fn from_wide_vec_incompatible() {
    let v = vec![1, 2, 3, 4, 5];
    let p = v.as_ptr();
    let wide_vec: WideVec<i32, ()> = WideVec::from(v);
    let wide_vec: SmartWideVec<i32, Arc> = SmartWideVec::from_wide_vec(wide_vec);
    assert_eq!(wide_vec.len(), 5);
    assert_eq!(wide_vec.as_slice(), &[1, 2, 3, 4, 5]);
    assert_eq!(wide_vec.as_ptr(), p);
}

#[test]
fn from_wide_vec_compatible() {
    let v = vec![1, 2, 3, 4, 5];
    let p = v.as_ptr();
    let wide_vec: WideVec<i32, ZeroUsize> = WideVec::from(v);
    let wide_vec: SmartWideVec<i32, Arc> = SmartWideVec::from_wide_vec(wide_vec);
    assert_eq!(wide_vec.len(), 5);
    assert_eq!(wide_vec.as_slice(), &[1, 2, 3, 4, 5]);
    assert_eq!(wide_vec.as_ptr(), p);
}

#[test]
fn as_mut_wide_vec_unique() {
    let mut v = vec![1, 2, 3, 4, 5];
    v.reserve(10); // make the pointer stable
    let p = v.as_ptr();
    let mut wide_vec: SmartWideVec<i32, Arc> = SmartWideVec::from(v);

    {
        let wide_ref = wide_vec.as_mut_wide_vec().unwrap();
        let mut wide_mut = wide_ref.mutate();
        for i in 6..=10 {
            wide_mut.push(i);
        }
    }

    assert_eq!(wide_vec.len(), 10);
    assert_eq!(wide_vec.as_slice(), &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
    assert_eq!(wide_vec.as_ptr(), p);
}

#[test]
fn as_mut_wide_vec_nonunique() {
    let v = vec![1, 2, 3, 4, 5];
    let mut wide_vec: SmartWideVec<i32, Arc> = SmartWideVec::from(v);
    let _wide_vec2 = wide_vec.clone();
    assert!(wide_vec.as_mut_wide_vec().is_none());
}

#[test]
fn as_mut_slice_unique() {
    let v = vec![1, 2, 3, 4, 5];
    let p = v.as_ptr();
    let mut wide_vec: SmartWideVec<i32, Arc> = SmartWideVec::from(v);
    {
        let slice_mut = wide_vec.as_mut_slice().unwrap();
        slice_mut[0] = 10;
        slice_mut[1] = 20;
    }
    assert_eq!(wide_vec.as_slice(), &[10, 20, 3, 4, 5]);
    assert_eq!(wide_vec.as_ptr(), p);
}

#[test]
fn as_mut_slice_nonunique() {
    let v = vec![1, 2, 3, 4, 5];
    let mut wide_vec: SmartWideVec<i32, Arc> = SmartWideVec::from(v);
    let _wide_vec2 = wide_vec.clone();
    assert!(wide_vec.as_mut_slice().is_none());
}
