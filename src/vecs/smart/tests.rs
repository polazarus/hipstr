use alloc::vec;

use super::SmartVec;
use crate::smart::Smart;
use crate::{smart_thin_vec, Arc, Unique};

#[test]
fn new() {
    let v = SmartVec::<i32, Arc>::new();
    assert!(v.is_empty());
    assert_eq!(v.len(), 0);
    assert!(v.is_thin());
    assert!(!v.is_fat());
}

#[test]
fn with_capacity() {
    let v = SmartVec::<i32, Arc>::with_capacity(10);
    assert!(v.is_empty());
    assert!(v.is_thin());
    assert!(!v.is_fat());
    assert!(v.capacity() >= 10);
}

#[test]
fn capacity_fat() {
    let fat = Smart::new(vec![1, 2, 3]);
    let v = SmartVec::<i32, Arc>::from_fat(fat);
    assert!(v.is_fat());
    assert!(!v.is_thin());
    assert!(v.capacity() >= 3);
}

#[test]
fn from_fat() {
    let fat = Smart::new(vec![1, 2, 3]);
    let p = fat.as_ptr();
    let v = SmartVec::<i32, Arc>::from_fat(fat);
    assert_eq!(v.as_slice(), &[1, 2, 3]);
    assert_eq!(v.len(), 3);
    assert!(v.is_fat());
    assert!(!v.is_thin());
    assert_eq!(v.as_ptr(), p);
}

#[test]
fn from_thin() {
    let thin = smart_thin_vec![Arc : 1, 2, 3];
    let p = thin.as_ptr();
    let v = SmartVec::<i32, Arc>::from_thin(thin);
    assert_eq!(v.as_slice(), &[1, 2, 3]);
    assert_eq!(v.len(), 3);
    assert!(v.is_thin());
    assert!(!v.is_fat());
    assert_eq!(v.as_ptr(), p);
}

#[test]
fn len_is_empty() {
    let v = SmartVec::<i32, Arc>::new();
    assert!(v.is_empty());
    assert_eq!(v.len(), 0);
    assert!(v.is_thin());
    assert!(!v.is_fat());

    let v = SmartVec::<i32, Arc>::from_fat(Smart::new(vec![1, 2, 3]));
    assert!(!v.is_empty());
    assert_eq!(v.len(), 3);
    assert!(v.is_fat());
    assert!(!v.is_thin());

    let v = SmartVec::<i32, Arc>::from_thin(smart_thin_vec![Arc : 1, 2, 3]);
    assert!(!v.is_empty());
    assert_eq!(v.len(), 3);
    assert!(v.is_thin());
    assert!(!v.is_fat());
}

#[test]
fn clone() {
    let thin = smart_thin_vec![Arc : 1, 2, 3];
    let p = thin.as_ptr();
    let v = SmartVec::<i32, Arc>::from_thin(thin);
    let v2 = v.clone();
    assert_eq!(v2.as_slice(), &[1, 2, 3]);
    assert_eq!(v2.len(), 3);
    assert!(v2.is_thin());
    assert!(!v2.is_fat());
    assert_eq!(v2.as_ptr(), p);
}

#[test]
fn is_unique_thin() {
    let thin = smart_thin_vec![Arc : 1, 2, 3];
    let v = SmartVec::<i32, Arc>::from_thin(thin);
    assert!(v.is_unique());
    assert_eq!(v.len(), 3);
    assert!(v.is_thin());
    assert!(!v.is_fat());

    let _w = v.clone();
    assert!(!v.is_unique());
}

#[test]
fn is_unique_fat() {
    let fat = Smart::new(vec![1, 2, 3]);
    let v = SmartVec::<i32, Arc>::from_fat(fat);
    assert!(v.is_unique());
    assert_eq!(v.len(), 3);
    assert!(v.is_fat());
    assert!(!v.is_thin());

    let _w = v.clone();
    assert!(!v.is_unique());
}

#[test]
fn try_clone() {
    let v = SmartVec::<i32, Arc>::new();
    let w = v.try_clone().unwrap();
    assert_eq!(v.as_ptr(), w.as_ptr());

    let v = SmartVec::<i32, Unique>::new();
    assert!(v.try_clone().is_none());
}

#[test]
fn force_clone_arc() {
    let v = SmartVec::<i32, Arc>::new();
    let w = v.force_clone();
    assert_eq!(v.as_ptr(), w.as_ptr());
}

#[test]
fn force_clone_unique_thin() {
    let v = SmartVec::<i32, Unique>::new();
    assert!(v.is_thin());
    let w = v.force_clone();
    assert_ne!(v.as_ptr(), w.as_ptr());
}

#[test]
fn force_clone_unique_fat() {
    let fat = Smart::new(vec![1, 2, 3]);
    let v = SmartVec::<i32, Unique>::from_fat(fat);
    assert!(v.is_fat());

    let w = v.force_clone();
    assert_ne!(v.as_ptr(), w.as_ptr());
}
