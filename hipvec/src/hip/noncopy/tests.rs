use std::boxed::Box;

use super::HipVec;
use crate::Rc;

type V<'a, T> = HipVec<'a, T, Rc>;

#[test]
fn miri_test() {
    let v = V::<u8>::new();
    assert!(!v.as_ptr().is_null());

    let v = V::<u8>::with_capacity(100);
    assert!(!v.as_ptr().is_null());

    let v = V::<Box<u8>>::new();
    assert!(!v.as_ptr().is_null());

    let t = crate::thin_vec![Box::new(1), Box::new(2), Box::new(3),];

    let v = V::from(t);

    assert_eq!(v.as_slice(), [Box::new(1), Box::new(2), Box::new(3)]);

    assert!(!v.as_ptr().is_null());

    let t = [Box::new(1), Box::new(2), Box::new(3)];
    let mut v = V::borrowed(&t);
    assert_eq!(v.as_slice(), [Box::new(1), Box::new(2), Box::new(3)]);
    assert!(!v.as_ptr().is_null());
    assert_eq!(v.as_ptr(), t.as_ptr());

    v.mutate().push(Box::new(4));
    assert_eq!(
        v.as_slice(),
        [Box::new(1), Box::new(2), Box::new(3), Box::new(4)]
    );
}
