use super::*;
use crate::Rc;

type R = HipByt<'static, Rc>;

#[test]
fn test_niche() {
    type O = Option<R>;
    assert_eq!(size_of::<O>(), size_of::<R>());
}

#[cfg(debug_assertions)]
#[should_panic(expected = "mutable slice of borrowed string")]
#[test]
fn test_to_mut_slice_unchecked_panic() {
    let mut r = R::borrowed(b"abc");
    unsafe {
        let _sl = r.as_mut_slice_unchecked();
    }
}
