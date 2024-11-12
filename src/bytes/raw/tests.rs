use super::*;
use crate::Rc;

type R = HipByt<'static, Rc>;

#[test]
fn test_niche() {
    type O = Option<R>;
    assert_eq!(size_of::<O>(), size_of::<R>());
}

#[test]
fn test_union() {
    let union = Union {
        inline: Inline::empty(),
    };
    let _: R = union.into_raw();

    let union = Union {
        allocated: Allocated::new([42].repeat(42)),
    };
    let _: R = union.into_raw();

    let union: Union<'static, Rc> = Union {
        borrowed: Borrowed::new(b"abc"),
    };
    let _: R = union.into_raw();
}

#[cfg(debug_assertions)]
#[should_panic]
#[test]
fn test_to_mut_slice_unchecked_panic() {
    let mut r = R::borrowed(b"abc");
    unsafe {
        let _sl = r.as_mut_slice_unchecked();
    }
}
