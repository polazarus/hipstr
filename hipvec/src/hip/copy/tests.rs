use super::HipVec;
use crate::Rc;
use crate::thin::ThinVec;

type V<'a, T> = HipVec<'a, T, Rc>;

#[test]
fn miri_test() {
    let v = V::<u8>::new();
    assert!(!v.as_ptr().is_null());

    // let v = V::<u8>::from(ThinVec::with_capacity(100));
    // assert!(!v.as_ptr().is_null());
}
