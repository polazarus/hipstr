#![allow(clippy::redundant_clone)]

use alloc::vec;
use alloc::vec::Vec;
use core::borrow::Borrow;
use core::cmp::Ordering;
use core::ptr;

use super::*;
use crate::backend::PanickyUnique;
use crate::{smart_thin_vec, thin_vec, Arc, Rc, Unique};

#[test]
fn new() {
    let v = SmartThinVec::<u8, Arc>::new();
    assert_eq!(v.len(), 0);
    assert!(v.is_empty());
    assert!(v.is_unique());

    let v = SmartThinVec::<u8, Rc>::default();
    assert_eq!(v.len(), 0);
    assert!(v.is_empty());
    assert!(v.is_unique());
}

#[test]
fn refs() {
    let tv = thin_vec![Box::new(1_i32), Box::new(2)];
    let stv = SmartThinVec::<Box<i32>, Arc>::from(tv);
    let p = &raw const stv;

    let r: &ThinVec<_, _> = stv.as_ref();
    assert_eq!(ptr::from_ref(r).cast::<()>(), p.cast::<()>());

    let r2: &ThinVec<_, _> = stv.borrow();
    assert_eq!(ptr::from_ref(r2).cast::<()>(), p.cast::<()>());

    let sl: &[Box<i32>] = stv.as_ref();
    assert_eq!(sl.as_ptr(), stv.as_ptr());

    let sl2: &[Box<i32>] = stv.borrow();
    assert_eq!(sl2.as_ptr(), stv.as_ptr());
}

#[test]
fn clone_empty() {
    let v1 = SmartThinVec::<u8, Arc>::new();
    assert_eq!(v1.len(), 0);
    assert!(v1.is_empty());
    assert!(v1.is_unique());

    let v2 = v1.clone();
    assert_eq!(v2.len(), 0);
    assert!(v1.is_empty());
    assert!(v2.is_unique());
}

#[test]
fn clone() {
    let v1 = SmartThinVec::<u8, Arc>::from_array([1, 2]);
    assert_eq!(v1.len(), 2);
    assert!(!v1.is_empty());
    assert_eq!(v1.as_slice(), &[1, 2]);

    assert!(v1.is_unique());

    let v2 = v1.clone();
    assert_eq!(v2.len(), 2);
    assert!(!v2.is_empty());
    assert_eq!(v1.as_slice(), v2.as_slice());
    assert_eq!(v1.as_ptr(), v2.as_ptr());

    assert!(!v2.is_unique());
    assert!(!v1.is_unique());
}

#[test]
fn clone_unique() {
    let v1 = smart_thin_vec![Unique : 1, 2, 3];
    assert_eq!(v1.len(), 3);
    assert!(v1.is_unique());

    let v2 = v1.clone();
    assert_eq!(v2.len(), 3);
    assert!(v2.is_unique());

    assert_ne!(v1.as_ptr(), v2.as_ptr());
}

#[test]
#[should_panic(expected = "count overflow")]
fn clone_panic() {
    let v1 = SmartThinVec::<u8, PanickyUnique>::from_array([1, 2]);
    assert_eq!(v1.len(), 2);
    assert!(v1.is_unique());

    let _v2 = v1.clone();
}

#[test]
fn with_capacity() {
    let v = SmartThinVec::<u8, Arc>::with_capacity(10);
    assert_eq!(v.len(), 0);
    assert!(v.capacity() >= 10);

    let v = SmartThinVec::<u8, Rc>::with_capacity(0);
    assert_eq!(v.len(), 0);
    assert_eq!(v.capacity(), 0); // strictly zero
}

#[test]
fn deref() {
    let v = SmartThinVec::<u8, Arc>::new();
    let d: &ThinVec<u8, _> = &v;
    let a: &_ = v.as_thin_vec();
    assert!(ptr::eq(d, a));
}

#[test]
fn as_ref() {
    let v = SmartThinVec::<u8, Arc>::new();

    let s: &[u8] = v.as_thin_vec();
    assert!(ptr::eq(s, v.as_slice()));

    let t: &ThinVec<u8, _> = v.as_thin_vec();
    assert!(ptr::eq(t, v.as_thin_vec()));
}

#[test]
fn as_mut() {
    let mut v = SmartThinVec::<u8, Arc>::from_array([1, 2]);
    assert!(v.is_unique());
    assert!(v.as_mut().is_some());

    let _v2 = v.clone();
    assert!(!v.is_unique());
    assert!(v.as_mut().is_none());
}

#[test]
fn from_impls() {
    let v = SmartThinVec::<u8, Arc>::from(vec![1, 2]);
    assert_eq!(v.as_slice(), &[1, 2]);
    let v = SmartThinVec::<u8, Arc>::from(thin_vec![1, 2]);
    assert_eq!(v.as_slice(), &[1, 2]);
    let v = SmartThinVec::<u8, Arc>::from([1, 2]);
    assert_eq!(v.as_slice(), &[1, 2]);
    let v = SmartThinVec::<u8, Arc>::from([1, 2].as_slice());
    assert_eq!(v.as_slice(), &[1, 2]);
    let v = SmartThinVec::<u8, Arc>::from([1, 2].as_mut_slice());
    assert_eq!(v.as_slice(), &[1, 2]);
    let v = SmartThinVec::<u8, Arc>::from(&[1, 2]);
    assert_eq!(v.as_slice(), &[1, 2]);
    let v = SmartThinVec::<u8, Arc>::from(&mut [1, 2]);
    assert_eq!(v.as_slice(), &[1, 2]);
    let v = SmartThinVec::<u8, Arc>::from(vec![1, 2].into_boxed_slice());
    assert_eq!(v.as_slice(), &[1, 2]);

    let arr = [Box::new(1), Box::new(2)];
    let p = &raw const *arr[0];
    let stv = SmartThinVec::<_, Arc>::from(arr);
    assert_eq!(p, &raw const *stv[0]);

    let boxed: Box<[Box<i32>]> = Box::new([Box::new(1), Box::new(2)]);
    let p = &raw const *boxed[0];
    let stv = SmartThinVec::<_, Arc>::from(boxed);
    assert_eq!(p, &raw const *stv[0]);

    let vec = vec![Box::new(1), Box::new(2)];
    let p = &raw const *vec[0];
    let stv = SmartThinVec::<_, Arc>::from(vec);
    assert_eq!(p, &raw const *stv[0]);

    let slice = &[Box::new(1), Box::new(2)];
    let p = &raw const *slice[0];
    let stv = SmartThinVec::<_, Arc>::from(slice);
    assert_ne!(p, &raw const *stv[0]);
}

#[test]
fn mutate() {
    let mut v = SmartThinVec::<u8, Arc>::with_capacity(3);
    let p = v.as_ptr();
    assert!(v.is_unique());
    {
        let m = v.mutate();
        m.push(1);
        m.push(2);
        m.push(3);
    }
    assert_eq!(v.as_slice(), [1, 2, 3]);
    assert_eq!(v.as_ptr(), p);

    let _v2 = v.clone();
    assert!(!v.is_unique());
    {
        let m = v.mutate();
        m.push(4);
        m.push(5);
    }
    assert!(v.is_unique());
    assert_eq!(v.as_slice(), [1, 2, 3, 4, 5]);
    assert_ne!(v.as_ptr(), p);
}

#[test]
fn mutate_copy() {
    let mut v = SmartThinVec::<u8, Arc>::with_capacity(3);
    let p = v.as_ptr();
    assert!(v.is_unique());
    {
        let m = v.mutate_copy();
        m.push(1);
        m.push(2);
        m.push(3);
    }
    assert_eq!(v.as_slice(), [1, 2, 3]);
    assert_eq!(v.as_ptr(), p);

    let _v2 = v.clone();
    assert!(!v.is_unique());
    {
        let m = v.mutate_copy();
        m.push(4);
        m.push(5);
    }
    assert!(v.is_unique());
    assert_eq!(v.as_slice(), [1, 2, 3, 4, 5]);
    assert_ne!(v.as_ptr(), p);
}

#[test]
fn try_clone() {
    let v = smart_thin_vec![1, 2, 3];
    let v2 = v.try_clone().unwrap();
    assert_eq!(v.as_slice(), v2.as_slice());
    assert_eq!(v.as_ptr(), v2.as_ptr());

    let v = smart_thin_vec![Unique : 1, 2, 3];
    assert!(v.try_clone().is_none());
}

#[test]
fn into_thin_vec() {
    let v = smart_thin_vec![1, 2, 3];
    let w = v.into_thin_vec().unwrap();
    assert_eq!(w, [1, 2, 3]);

    let v1 = smart_thin_vec![1, 2, 3];
    let v2 = v1.clone();
    let v3 = v1.into_thin_vec().unwrap_err();
    assert_eq!(v3.as_ptr(), v2.as_ptr());
    assert_eq!(v3.as_slice(), v2.as_slice());
}

#[test]
fn try_into_impls() {
    let v = smart_thin_vec![1, 2, 3];
    let w: ThinVec<_> = v.try_into().unwrap();
    assert_eq!(w, [1, 2, 3]);

    let v1 = smart_thin_vec![1, 2, 3];
    let v2 = v1.clone();
    let result: Result<ThinVec<i32>, _> = v1.try_into();
    let v3 = result.unwrap_err();
    assert_eq!(v3.as_ptr(), v2.as_ptr());
    assert_eq!(v3.as_slice(), v2.as_slice());
}

#[test]
fn eq() {
    assert_eq!(smart_thin_vec![Rc : 1, 2, 3], smart_thin_vec![Arc: 1, 2, 3]);

    assert_eq!(smart_thin_vec![1, 2, 3], thin_vec![1, 2, 3]);
    assert_eq!(smart_thin_vec![1, 2, 3], vec![1, 2, 3]);
    assert_eq!(smart_thin_vec![1, 2, 3], [1, 2, 3]);
    assert_eq!(smart_thin_vec![1, 2, 3], [1, 2, 3].as_slice());
    assert_eq!(smart_thin_vec![1, 2, 3], [1, 2, 3].as_mut_slice());
    assert_eq!(smart_thin_vec![1, 2, 3], *[1, 2, 3].as_slice());
    assert_eq!(smart_thin_vec![1, 2, 3], *[1, 2, 3].as_mut_slice());

    assert_eq!(thin_vec![1, 2, 3], smart_thin_vec![1, 2, 3]);
    assert_eq!(vec![1, 2, 3], smart_thin_vec![1, 2, 3]);
    assert_eq!([1, 2, 3], smart_thin_vec![1, 2, 3]);
    assert_eq!([1, 2, 3].as_slice(), smart_thin_vec![1, 2, 3]);
    assert_eq!([1, 2, 3].as_mut_slice(), smart_thin_vec![1, 2, 3]);
    assert_eq!(*[1, 2, 3].as_slice(), smart_thin_vec![1, 2, 3]);
    assert_eq!(*[1, 2, 3].as_mut_slice(), smart_thin_vec![1, 2, 3]);
}
#[test]
fn cmp() {
    const SLICES: &[&[i32]] = &[&[1, 2, 3], &[1, 2, 3, 4], &[0], &[], &[1, 2, 2], &[1, 2, 5]];
    for &a in SLICES {
        for &b in SLICES {
            let a_stv = SmartThinVec::<_, Arc>::from(a);
            let b_stv = SmartThinVec::<_, Arc>::from(b);

            // self
            assert_eq!(a_stv.cmp(&b_stv), a.cmp(b));
            assert_eq!(b_stv.cmp(&a_stv), b.cmp(a));

            // slice
            assert_eq!(a_stv.partial_cmp(&b).unwrap(), a.cmp(b));
            assert_eq!(b_stv.partial_cmp(&a).unwrap(), b.cmp(a));
            assert_eq!(a.partial_cmp(&b_stv).unwrap(), a.cmp(b));
            assert_eq!(b.partial_cmp(&a_stv).unwrap(), b.cmp(a));

            let mut a_vec = Vec::from(a);
            let mut b_vec = Vec::from(b);

            let a_mut_slice = a_vec.as_mut_slice();
            let b_mut_slice = b_vec.as_mut_slice();

            // mut slice
            assert_eq!(a_stv.partial_cmp(b_mut_slice).unwrap(), a.cmp(b));
            assert_eq!(a_mut_slice.partial_cmp(&b_stv).unwrap(), a.cmp(b));
            assert_eq!(b_stv.partial_cmp(a_mut_slice).unwrap(), b.cmp(a));
            assert_eq!(b_mut_slice.partial_cmp(&a_stv).unwrap(), b.cmp(a));

            // Vec
            assert_eq!(a_stv.partial_cmp(&b_vec).unwrap(), a.cmp(b));
            assert_eq!(b_vec.partial_cmp(&a_stv).unwrap(), b.cmp(a));
            assert_eq!(b_stv.partial_cmp(&a_vec).unwrap(), b.cmp(a));
            assert_eq!(a_vec.partial_cmp(&b_stv).unwrap(), a.cmp(b));

            let a_thin = ThinVec::<_, Reserved>::from(a);
            let b_thin = ThinVec::<_, Reserved>::from(b);

            // ThinVec
            assert_eq!(a_stv.partial_cmp(&b_thin).unwrap(), a.cmp(b));
            assert_eq!(b_thin.partial_cmp(&a_stv).unwrap(), b.cmp(a));
            assert_eq!(b_stv.partial_cmp(&a_thin).unwrap(), b.cmp(a));
            assert_eq!(a_thin.partial_cmp(&b_stv).unwrap(), a.cmp(b));
        }
    }

    let v = smart_thin_vec![1, 2, 3];

    // array
    assert_eq!(v.partial_cmp(&[1, 2, 3]).unwrap(), Ordering::Equal);
    assert_eq!(v.partial_cmp(&[1, 2]).unwrap(), Ordering::Greater);
    assert_eq!([1, 2].partial_cmp(&v).unwrap(), Ordering::Less);
    assert_eq!([1, 2, 3].partial_cmp(&v).unwrap(), Ordering::Equal);
}

#[test]
fn push() {
    let mut v = SmartThinVec::<u8, Arc>::new();
    assert!(v.is_unique());
    v.push(1);
    let v2 = v.clone();
    assert!(!v.is_unique());
    v.push(2);
    assert!(v.is_unique());
    assert_eq!(v.as_slice(), &[1, 2]);
    assert_eq!(v2.as_slice(), &[1]);
}

#[test]
fn push_copy() {
    let mut v = SmartThinVec::<u8, Arc>::new();
    assert!(v.is_unique());
    v.push_copy(1);
    let v2 = v.clone();
    assert!(!v.is_unique());
    v.push_copy(2);
    assert!(v.is_unique());
    assert_eq!(v.as_slice(), &[1, 2]);
    assert_eq!(v2.as_slice(), &[1]);
}

#[test]
fn pop() {
    let mut v = SmartThinVec::<u8, Arc>::from_array([1, 2]);
    assert!(v.is_unique());
    let x = v.pop();
    assert_eq!(x, Some(2));
    assert!(v.is_unique());
    let v2 = v.clone();
    assert!(!v.is_unique());
    let x = v.pop();
    assert_eq!(x, Some(1));
    assert!(v.is_unique());
    assert!(v.is_empty());
    assert_eq!(v2.as_slice(), &[1]);
    let x = v.pop();
    assert_eq!(x, None);
}

#[test]
fn pop_copy() {
    let mut v = SmartThinVec::<u8, Arc>::from_array([1, 2]);
    assert!(v.is_unique());
    let x = v.pop_copy();
    assert_eq!(x, Some(2));
    assert!(v.is_unique());
    let v2 = v.clone();
    assert!(!v.is_unique());
    let x = v.pop_copy();
    assert_eq!(x, Some(1));
    assert!(v.is_unique());
    assert!(v.is_empty());
    assert_eq!(v2.as_slice(), &[1]);
    let x = v.pop_copy();
    assert_eq!(x, None);
}

#[test]
fn pop_if() {
    let mut v = SmartThinVec::<u8, Arc>::from_array([1, 2, 3, 4]);
    assert!(v.is_unique());
    assert!(v.pop_if(|x| *x % 2 == 1).is_none());
    assert_eq!(v.pop_if(|x| *x % 2 == 0), Some(4));
    assert!(v.is_unique());

    let v2 = v.clone();
    assert!(!v.is_unique());
    assert_eq!(v.pop_if(|x| *x % 2 != 0), Some(3));
    assert!(v.is_unique());

    assert_eq!(v.as_slice(), &[1, 2]);
    assert_eq!(v2.as_slice(), &[1, 2, 3]);

    assert_eq!(v.pop_if(|_| true), Some(2));
    assert_eq!(v.pop_if(|_| true), Some(1));
    assert_eq!(v.pop_if(|_| true), None);
}

#[test]
fn pop_if_copy() {
    let mut v = SmartThinVec::<u8, Arc>::from_array([1, 2, 3, 4]);
    assert!(v.is_unique());
    assert!(v.pop_if_copy(|x| *x % 2 == 1).is_none());
    assert_eq!(v.pop_if_copy(|x| *x % 2 == 0), Some(4));
    assert!(v.is_unique());

    let v2 = v.clone();
    assert!(!v.is_unique());
    assert_eq!(v.pop_if_copy(|x| *x % 2 != 0), Some(3));
    assert!(v.is_unique());

    assert_eq!(v.as_slice(), &[1, 2]);
    assert_eq!(v2.as_slice(), &[1, 2, 3]);

    assert_eq!(v.pop_if_copy(|_| true), Some(2));
    assert_eq!(v.pop_if_copy(|_| true), Some(1));
    assert_eq!(v.pop_if_copy(|_| true), None);
}

#[test]
fn extend_from_slice() {
    let mut v = SmartThinVec::<u8, Arc>::from_array([1, 2]);
    assert!(v.is_unique());
    v.extend_from_slice(&[3, 4]);
    assert!(v.is_unique());
    assert_eq!(v.as_slice(), &[1, 2, 3, 4]);

    let v2 = v.clone();
    assert!(!v.is_unique());
    v.extend_from_slice(&[]);
    assert!(!v.is_unique());
    assert_eq!(v.as_slice(), &[1, 2, 3, 4]);

    v.extend_from_slice(&[5, 6]);
    assert!(v.is_unique());
    assert_eq!(v.as_slice(), &[1, 2, 3, 4, 5, 6]);
    assert_eq!(v2.as_slice(), &[1, 2, 3, 4]);
}

#[test]
fn extend_from_slice_copy() {
    let mut v = SmartThinVec::<u8, Arc>::from_array([1, 2]);
    assert!(v.is_unique());
    v.extend_from_slice_copy(&[3, 4]);
    assert!(v.is_unique());
    assert_eq!(v.as_slice(), &[1, 2, 3, 4]);
    let v2 = v.clone();
    assert!(!v.is_unique());
    v.extend_from_slice_copy(&[]);
    assert!(!v.is_unique());
    assert_eq!(v.as_slice(), &[1, 2, 3, 4]);
    v.extend_from_slice_copy(&[5, 6]);
    assert!(v.is_unique());
    assert_eq!(v.as_slice(), &[1, 2, 3, 4, 5, 6]);
    assert_eq!(v2.as_slice(), &[1, 2, 3, 4]);
}

#[test]
fn append() {
    let mut v1 = SmartThinVec::<u8, Arc>::from_array([1, 2]);
    let mut v2 = SmartThinVec::<u8, Arc>::from_array([3, 4]);
    assert!(v1.is_unique());
    assert!(v2.is_unique());

    v1.append(&mut v2);
    assert!(v1.is_unique());
    assert!(v2.is_empty());
    assert_eq!(v1.as_slice(), &[1, 2, 3, 4]);

    let mut v3 = v1.clone();
    assert!(!v1.is_unique());
    assert!(!v3.is_unique());

    v1.append(&mut v3);
    assert!(v1.is_unique());
    assert!(v3.is_empty());
    assert_eq!(v1.as_slice(), &[1, 2, 3, 4, 1, 2, 3, 4]);
}

#[test]
fn append_vec() {
    let mut v1 = SmartThinVec::<u8, Arc>::from_array([1, 2]);
    let mut v2 = vec![3, 4];
    assert!(v1.is_unique());

    v1.append(&mut v2);
    assert!(v1.is_unique());
    assert!(v2.is_empty());
    assert_eq!(v1.as_slice(), &[1, 2, 3, 4]);

    let mut v3 = vec![5, 6];
    let v1_clone = v1.clone();
    assert!(!v1.is_unique());
    v1.append(&mut v3);
    assert!(v1.is_unique());
    assert!(v3.is_empty());
    assert_eq!(v1.as_slice(), &[1, 2, 3, 4, 5, 6]);
    assert_eq!(v1_clone.as_slice(), &[1, 2, 3, 4]);
}

#[test]
fn from_slice_clone() {
    let arr = [Box::new(1), Box::new(2)];
    let p = &raw const *arr[0];
    let stv = SmartThinVec::<_, Arc>::from(&arr[..]); // calls from_slice_clone
    assert_ne!(p, &raw const *stv[0]);

    let stv = SmartThinVec::<u8, Rc>::from(&[]);
    assert!(stv.is_empty());
    assert_eq!(stv.capacity(), 0);
}

#[test]
fn from_slice_copy() {
    let arr = [1_u8, 2];
    let stv = SmartThinVec::<_, Arc>::from_slice_copy(&arr[..]);
    assert_eq!(arr.as_slice(), stv.as_slice());

    let stv = SmartThinVec::<u8, Rc>::from(&[]);
    assert!(stv.is_empty());
    assert_eq!(stv.capacity(), 0);
}

#[test]
fn from_iter() {
    let stv: SmartThinVec<_, Arc> = (1..4).collect();
    assert_eq!(stv.as_slice(), &[1, 2, 3]);

    let stv: SmartThinVec<i32, Rc> = core::iter::empty().collect();
    assert!(stv.is_empty());
    assert_eq!(stv.capacity(), 0);
}
