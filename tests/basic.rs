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
