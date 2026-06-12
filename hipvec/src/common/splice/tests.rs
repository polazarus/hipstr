use super::Splice;
use crate::inline::InlineVec;
use crate::inline_vec;

#[test]
fn splice_no_std_inlinevec() {
    let mut v: InlineVec<u8> = inline_vec![1, 2, 3, 4, 5];
    let cap = v.capacity();
    {
        let splice = Splice::new(&mut v, 1..4, [9, 8]).unwrap();
        assert!(splice.eq([2, 3, 4]));
    }
    assert_eq!(v.as_slice(), [1, 9, 8, 5]);
    assert_eq!(v.capacity(), cap);

    let mut v: InlineVec<u8> = inline_vec![1, 2, 3, 4, 5];
    let cap = v.capacity();
    {
        let splice = Splice::new(&mut v, .., [9, 8]).unwrap();
        assert!(splice.eq([1, 2, 3, 4, 5]));
    }
    assert_eq!(v.as_slice(), [9, 8]);
    assert_eq!(v.capacity(), cap);
}

#[test]
fn splice_no_alloc_inlinevec_unknown_size_iter() {
    let mut v: InlineVec<u8> = inline_vec![1, 2, 3, 4, 5];
    let cap = v.capacity();
    {
        let splice = Splice::new(&mut v, 1..3, [9, 8, 7, 6].into_iter().filter(|_| true)).unwrap();
        assert!(splice.eq([2, 3]));
    }
    assert_eq!(v.as_slice(), [1, 9, 8, 7, 6, 4, 5]);
    assert_eq!(v.capacity(), cap);
}
