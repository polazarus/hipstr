use alloc::vec;
use alloc::vec::Vec;

use super::Drain;

#[test]
fn drain_none() {
    let mut v = vec![1, 2, 3];
    {
        let drain = Drain::new(&mut v, 0..0).unwrap();
        assert!(drain.eq([]));
    }
    assert_eq!(v, [1, 2, 3]);

    let mut v = vec![1, 2, 3];
    {
        let drain = Drain::new(&mut v, 3..3).unwrap();
        assert!(drain.eq([]));
    }
    assert_eq!(v, [1, 2, 3]);
}

#[test]
fn drain_all() {
    let mut v = vec![1, 2, 3];
    {
        let drain = Drain::new(&mut v, ..).unwrap();
        assert!(drain.eq([1, 2, 3]));
    }
    assert!(v.is_empty());

    let mut v: Vec<u32> = vec![];
    {
        let drain = Drain::new(&mut v, ..).unwrap();
        assert!(drain.eq([]));
    }
    assert!(v.is_empty());
}

#[test]
fn drain_part() {
    let mut v = vec![1, 2, 3, 4, 5];
    {
        let drain = Drain::new(&mut v, 1..4).unwrap();
        assert!(drain.eq([2, 3, 4]));
    }
    assert_eq!(v, [1, 5]);

    let mut v = vec![1, 2, 3, 4, 5];
    {
        let drain = Drain::new(&mut v, ..3).unwrap();
        assert!(drain.eq([1, 2, 3]));
    }
    assert_eq!(v, [4, 5]);

    let mut v = vec![1, 2, 3, 4, 5];
    {
        let drain = Drain::new(&mut v, 2..).unwrap();
        assert!(drain.eq([3, 4, 5]));
    }
    assert_eq!(v, [1, 2]);
}

#[test]
#[expect(
    clippy::reversed_empty_ranges,
    reason = "intentionally testing of reversed range"
)]
fn bad_drain() {
    let mut v = vec![1, 2, 3];
    assert!(Drain::new(&mut v, 4..).is_err());
    assert!(Drain::new(&mut v, ..=3).is_err());
    assert!(Drain::new(&mut v, 2..1).is_err());
    assert!(Drain::new(&mut v, ..4).is_err());
}
