use std::borrow::Cow;
use std::hint::black_box;

use hipstr::HipStr;

#[inline(never)]
pub fn new(slice: &str) -> HipStr<'static> {
    HipStr::from(slice)
}

#[inline(never)]
pub fn new_inline(slice: &str) -> HipStr<'static> {
    assert!(slice.len() < HipStr::inline_capacity());
    HipStr::from(slice)
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
