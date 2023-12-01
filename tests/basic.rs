use std::borrow::Cow;
use std::hint::black_box;

use hipstr::HipStr;

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
