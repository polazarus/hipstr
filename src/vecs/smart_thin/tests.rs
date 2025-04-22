#![allow(clippy::redundant_clone)]

use alloc::vec;
use alloc::vec::Vec;
use core::cmp::Ordering;

use super::*;
use crate::backend::PanickyUnique;
use crate::{smart_thin_vec, thin_vec, Arc, Rc, Unique};

#[test]
fn new() {
    let v = SmartThinVec::<u8, Arc>::new();
    assert_eq!(v.len(), 0);
    assert!(v.is_unique());

    let v = SmartThinVec::<u8, Rc>::default();
    assert_eq!(v.len(), 0);
    assert!(v.is_unique());
}

#[test]

fn clone() {
    let v1 = SmartThinVec::<u8, Arc>::new();
    assert_eq!(v1.len(), 0);
    assert!(v1.is_unique());

    let v2 = v1.clone();
    assert_eq!(v2.len(), 0);
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
    let v1 = SmartThinVec::<u8, PanickyUnique>::new();
    assert_eq!(v1.len(), 0);
    assert!(v1.is_unique());

    let _v2 = v1.clone();
}

#[test]
fn with_capacity() {
    let v = SmartThinVec::<u8, Arc>::with_capacity(10);
    assert_eq!(v.len(), 0);
    assert!(v.capacity() >= 10);
}

#[test]
fn deref() {
    let v = SmartThinVec::<u8, Arc>::new();
    let d: &ThinVec<u8, _> = v.deref();
    let a: &_ = v.as_thin_vec();
    assert!(ptr::eq(d, a));
}

#[test]
fn as_ref() {
    let v = SmartThinVec::<u8, Arc>::new();

    let s: &[u8] = &v.as_ref();
    assert!(ptr::eq(s, v.as_slice()));

    let t: &ThinVec<u8, _> = &v.as_ref();
    assert!(ptr::eq(t, v.as_thin_vec()));
}

#[test]
fn as_mut() {
    let mut v = SmartThinVec::<u8, Arc>::new();
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
