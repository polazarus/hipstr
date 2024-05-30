use super::*;
use crate::Local;

type R = Raw<'static, Local>;

#[test]
fn test_niche() {
    type O = Option<R>;
    assert_eq!(size_of::<O>(), size_of::<R>())
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

    let union: Union<'static, Local> = Union {
        borrowed: Borrowed::new(b"abc"),
    };
    let _: R = union.into_raw();
}
