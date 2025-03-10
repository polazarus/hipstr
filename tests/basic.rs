use std::borrow::Cow;
use std::hint::black_box;

use hipstr::vecs::inline::InlineVec;
use hipstr::vecs::{SmartThinVec, ThinVec};
use hipstr::{inline_vec, smart_thin_vec, thin_vec, HipByt, HipStr, Rc};

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

#[test]
fn test_thin() {
    let _t = thin_vec![1, 2, 3];
    let _t = thin_vec![1; 3];
    let _t: ThinVec<i32> = thin_vec![];
}

#[test]
fn test_smart_thin() {
    let _t = smart_thin_vec![1, 2, 3];
    let _t = smart_thin_vec![1; 3];
    let _t: SmartThinVec<i32, _> = smart_thin_vec![];

    let _t = smart_thin_vec![Rc: 1, 2, 3];
    let _t = smart_thin_vec![Rc: 1; 3];
    let _t: SmartThinVec<i32, _> = smart_thin_vec![Rc:];
}

#[test]
#[inline(never)]
pub fn asm_inline_vec() {
    const {
        assert!(size_of::<InlineVec<u8, 7>>() == size_of::<u8>() * 7 + size_of::<u8>());
    }
    const ARR: [u8; 3] = [1, 2, 3];
    let _: InlineVec<u8, 7> = black_box(InlineVec::from_array(ARR));
    let _: InlineVec<u8, 7> = black_box(const { inline_vec![1, 2, 3] });

    const N: usize = size_of::<Vec<u8>>() - 1;
    let _: InlineVec<u8, N> = black_box(InlineVec::from_array(ARR));
    let _: InlineVec<u8, N> = black_box(const { inline_vec![1, 2, 3] });
}
