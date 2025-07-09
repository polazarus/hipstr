use std::borrow::Cow;
use std::cell::Cell;
use std::hint::black_box;
use std::marker::PhantomData;

use hipstr::{HipByt, HipStr};

#[inline(never)]
pub fn new(slice: &str) -> HipStr<'static> {
    HipStr::from(slice)
}

#[inline(never)]
pub fn new_inline(slice: &str) -> HipStr<'static> {
    assert!(slice.len() < HipStr::inline_capacity());
    HipStr::from(slice)
}

#[inline(never)]
pub fn klone<'a>(slice: &HipByt<'a>) -> HipByt<'a> {
    slice.clone()
}

#[test]
fn test_new() {
    assert_eq!(new("abc"), new_inline("abc"));
    assert_eq!(new(&"a".repeat(100)), "a".repeat(100));
}

#[test]
fn test_eq() {
    let h = HipStr::from("abc");
    let h2 = black_box(h.clone());
    assert_eq!(h, h2);
    let h3 = h.strip_prefix("a").unwrap();
    assert_eq!(h3, "bc");
}

#[test]
fn test_borrow() {
    let s = String::from("abc");
    let c = Cow::Borrowed(&s[..]);
    let h = HipStr::from(c);
    assert!(h.is_borrowed());
    let h_arr = [h, HipStr::borrowed("abc")];
    assert!(h_arr[1].is_borrowed());
}

#[test]
fn test_clone() {
    let h: HipByt<'static> = b"a".into();
    let _ = black_box(klone(&h));
}

// use pointer because they are cheaper to optimize away than cell reference
struct IsCopy<T>(*mut bool, PhantomData<T>);

impl<T> Clone for IsCopy<T> {
    #[inline(always)]
    fn clone(&self) -> Self {
        if let Some(r) = unsafe { self.0.as_mut() } {
            *r = false;
        }
        IsCopy(self.0, self.1)
    }
}

impl<T: Copy> Copy for IsCopy<T> {}

#[inline(always)]
fn is_copy<T>() -> bool {
    let mut result = true;
    {
        let array = [IsCopy::<T>(&raw mut result, PhantomData)];
        let _ = array.clone();
    }
    result
}

#[inline(never)]
#[unsafe(no_mangle)]
pub extern "C" fn is_copy_i32() -> bool {
    is_copy::<i32>()
}

#[inline(never)]
#[unsafe(no_mangle)]
pub extern "C" fn is_copy_vec_i32() -> bool {
    is_copy::<Vec<i32>>()
}

#[test]
#[inline(never)]
pub fn test_clone_copy() {
    assert!(is_copy::<[i32; 4]>());
    assert!(!is_copy::<Vec<i32>>());
}
