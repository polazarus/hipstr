use alloc::boxed::Box;
use alloc::vec;
use alloc::vec::Vec;
use core::hint::black_box;

use super::*;

#[test]
fn splice() {
    let mut v = vec![1, 2, 3, 4, 5];
    {
        let splice = Splice::new(&mut v, 1..4, [9, 8]).unwrap();
        assert!(splice.eq([2, 3, 4]));
    }
    assert_eq!(v, [1, 9, 8, 5]);

    let mut v = vec![1, 2, 3, 4, 5];
    {
        let splice = Splice::new(&mut v, 1..4, [9, 8, 7, 6]).unwrap();
        assert!(splice.eq([2, 3, 4]));
    }
    assert_eq!(v, [1, 9, 8, 7, 6, 5]);

    let mut v = vec![1, 2, 3, 4, 5];
    {
        let splice = Splice::new(&mut v, 1..4, [9, 8, 7, 6].into_iter().filter(|_| true)).unwrap();
        assert!(splice.eq([2, 3, 4]));
    }
    assert_eq!(v, [1, 9, 8, 7, 6, 5]);

    let mut v = vec![1, 2, 3, 4, 5];
    {
        let splice = Splice::new(&mut v, 0..0, [0]).unwrap();
        assert!(splice.eq([]));
    }
    assert_eq!(v, [0, 1, 2, 3, 4, 5]);
}

#[test]
fn splice_boxed() {
    let mut v = [1, 2, 3, 4, 5].map(Box::new).to_vec();
    {
        let splice = Splice::new(&mut v, 1..4, [9, 8].map(Box::new)).unwrap();
        assert!(splice.eq([2, 3, 4].map(Box::new)));
    }
    assert_eq!(v, [1, 9, 8, 5].map(Box::new));

    let mut v = [1, 2, 3, 4, 5].map(Box::new).to_vec();
    {
        let splice = Splice::new(&mut v, 1..4, [9, 8, 7, 6].map(Box::new)).unwrap();
        assert!(splice.eq([2, 3, 4].map(Box::new)));
    }
    assert_eq!(v, [1, 9, 8, 7, 6, 5].map(Box::new));

    let mut v = [1, 2, 3, 4, 5].map(Box::new).to_vec();
    {
        let splice = Splice::new(
            &mut v,
            1..4,
            [9, 8, 7, 6].map(Box::new).into_iter().filter(|_| true),
        )
        .unwrap();
        assert!(splice.eq([2, 3, 4].map(Box::new)));
    }
    assert_eq!(v, [1, 9, 8, 7, 6, 5].map(Box::new));

    let mut v = [1, 2, 3, 4, 5].map(Box::new).to_vec();
    {
        let mut splice = Splice::new(&mut v, 1..4, [6, 7].map(Box::new)).unwrap();
        assert!(splice.by_ref().take(1).eq([2].map(Box::new)));
        assert_eq!(splice.drain.as_slice(), [3, 4].map(Box::new));
    }
    assert_eq!(v, [1, 6, 7, 5].map(Box::new));

    let mut v = [1, 2, 3, 4, 5].map(Box::new).to_vec();
    {
        let mut splice = Splice::new(
            &mut v,
            ..,
            (1..42).map(Box::new).filter(|_| black_box(true)),
        )
        .unwrap();
        assert!(splice.by_ref().take(2).eq([1, 2].map(Box::new)));
        assert_eq!(splice.drain.as_slice(), [3, 4, 5].map(Box::new));
    }
    assert_eq!(v, (1..42).map(Box::new).collect::<Vec<_>>());
}
