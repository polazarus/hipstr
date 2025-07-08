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
        inline: ManuallyDrop::new(InlineVec::new()),
    };
    let _: R = union.into_raw();

    let union = Union {
        allocated: Allocated::from_vec([42].repeat(42)),
    };
    let _: R = union.into_raw();

    let union: Union<'static, Rc> = Union {
        borrowed: Borrowed::new(b"abc"),
    };
    let _: R = union.into_raw();
}

#[cfg(debug_assertions)]
#[should_panic(expected = "mutable slice of borrowed string")]
#[test]
fn test_to_mut_slice_unchecked_panic() {
    let mut r = R::borrowed(b"abc");
    assert!(r.is_borrowed());
    assert!(!r.is_allocated());
    unsafe {
        let _sl = r.as_mut_slice_unchecked();
    }
}
