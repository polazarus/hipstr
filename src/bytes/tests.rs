use core::ops::Bound;
use core::ptr;
#[cfg(feature = "std")]
use std::collections::HashSet;

// cspell:ignore fastrand
use fastrand::Rng;

use super::SliceErrorKind;
use crate::alloc::vec::Vec;
use crate::alloc::{format, vec};
use crate::HipByt;

const INLINE_CAPACITY: usize = HipByt::inline_capacity();

#[test]
fn test_new_default() {
    let new = HipByt::new();
    assert_eq!(new, &[]);
    assert!(new.is_empty());

    let new = HipByt::default();
    assert_eq!(new, &[]);
    assert!(new.is_empty());
}

#[test]
#[cfg(feature = "std")]
fn test_borrow_and_hash() {
    let mut set = HashSet::new();
    set.insert(HipByt::from(b"a"));
    set.insert(HipByt::from(b"b"));

    assert!(set.contains(b"a".as_slice()));
    assert!(!set.contains(b"c".as_slice()));
}

#[test]
fn test_debug() {
    let slice = &[1, 2, 3];
    let bytes = HipByt::from(slice);
    assert_eq!(format!("{slice:?}"), format!("{bytes:?}"));
}

#[test]
fn test_from_vec() {
    let v = vec![42; 42];
    let bytes = HipByt::from(v);
    assert!(!bytes.is_inline());
    assert!(!bytes.is_borrowed());
    assert!(bytes.is_allocated());
    assert_eq!(bytes.len(), 42);
    assert_eq!(bytes.as_slice(), [42; 42]);

    let v = vec![0; 3];
    let bytes = HipByt::from(v);
    assert!(bytes.is_inline());
    assert!(!bytes.is_borrowed());
    assert!(!bytes.is_allocated());
    assert_eq!(bytes.len(), 3);
    assert_eq!(bytes.as_slice(), [0; 3]);
}

#[test]
fn test_borrowed() {
    static V: &[u8] = &[42; 1024];

    for size in [0, 1, INLINE_CAPACITY, INLINE_CAPACITY + 1, 256, 1024] {
        let bytes = HipByt::borrowed(&V[..size]);
        assert!(!bytes.is_inline());
        assert!(bytes.is_borrowed());
        assert!(!bytes.is_allocated());
        assert_eq!(bytes.len(), size);
        assert_eq!(bytes.as_ptr(), V.as_ptr());
    }
}

#[test]
fn test_from_static() {
    fn is_static_type<T: 'static>(_: &T) {}

    let s = b"abcdefghijklmnopqrstuvwxyz";
    let bytes = HipByt::from_static(s);

    // compiler check
    is_static_type(&bytes);

    assert!(bytes.is_borrowed());
    assert!(!bytes.is_inline());
    assert!(!bytes.is_allocated());
    assert_eq!(bytes.len(), s.len());
    assert_eq!(bytes.as_slice(), s);
    assert_eq!(bytes.as_ptr(), s.as_ptr());
}

#[test]
fn test_from_slice() {
    static V: &[u8] = &[42; 1024];

    for size in [0, 1, INLINE_CAPACITY, INLINE_CAPACITY + 1, 256, 1024] {
        let bytes = HipByt::from(&V[..size]);
        assert_eq!(size <= INLINE_CAPACITY, bytes.is_inline());
        assert_eq!(size > INLINE_CAPACITY, bytes.is_allocated());
        assert_eq!(bytes.len(), size);
    }
}

#[test]
fn test_as_slice() {
    // static
    {
        let a = HipByt::borrowed(b"abc");
        assert!(a.is_borrowed());
        assert!(!a.is_inline());
        assert!(!a.is_allocated());
        assert_eq!(a.as_slice(), b"abc");
    }
    // inline
    {
        let a = HipByt::from(b"abc".as_slice());
        assert!(!a.is_borrowed());
        assert!(a.is_inline());
        assert!(!a.is_allocated());
        assert_eq!(a.as_slice(), b"abc");
    }
    // allocated
    {
        let a = HipByt::from(vec![42; 42]);
        assert!(!a.is_borrowed());
        assert!(!a.is_inline());
        assert!(a.is_allocated());
        assert_eq!(a.as_slice(), [42; 42]);
    }
}

#[test]
fn test_clone() {
    // static
    {
        let s: &'static [u8] = b"abc";
        let a = HipByt::borrowed(s);
        assert!(a.is_borrowed());
        let b = a.clone();
        drop(a);
        assert_eq!(b.as_slice(), s);
        assert_eq!(s.as_ptr(), b.as_ptr());
    }

    // inline
    {
        let a = HipByt::from(b"abc".as_slice());
        assert!(a.is_inline());
        let b = a.clone();
        drop(a);
        assert_eq!(b.as_slice(), b"abc");
    }

    // allocated
    {
        let v = vec![42; 42];
        let p = v.as_ptr();
        let a = HipByt::from(v);
        assert!(a.is_allocated());
        let b = a.clone();
        drop(a);
        assert_eq!(b.as_slice(), [42; 42]);
        assert_eq!(b.as_ptr(), p);
    }
}

#[test]
fn test_clone_drop() {
    let v = vec![42; 42];
    let mut rand = Rng::with_seed(0);
    for n in [5, 10, 20, 100] {
        // println!("!n {n}");
        let mut vs = vec![HipByt::from(v.clone()); n];

        while !vs.is_empty() {
            // println!("len {}", vs.len());
            let drops = rand.usize(1..=vs.len());
            // println!("drops {drops}");

            for _ in 0..drops {
                let _ = vs.pop();
            }
            if !vs.is_empty() {
                let clones = rand.usize(..drops.min(vs.len()));
                // println!("clones {clones}");
                for _ in 0..clones {
                    vs.push(vs[0].clone())
                }
            }
        }
    }
    // assert!(false);
}

#[test]
fn test_into_static() {
    // static
    let a = HipByt::borrowed(b"abc");
    assert_eq!(a.into_borrowed(), Ok(b"abc".as_slice()));

    // inline
    let a = HipByt::from(b"abc".as_slice());
    let b = a.clone();
    assert_eq!(a.into_borrowed(), Err(b));

    // heap
    let a = HipByt::from([42; 42].as_slice());
    let b = a.clone();
    assert_eq!(a.into_borrowed(), Err(b));
}

#[test]
fn test_as_mut_slice() {
    // static
    let mut a = HipByt::borrowed(b"abc");
    assert_eq!(a.as_mut_slice(), None);

    // inline
    let mut a = HipByt::from([42; 3].as_slice());
    assert!(a.is_inline());
    assert_eq!(a.as_mut_slice(), Some([42; 3].as_mut_slice()));

    // heap
    let mut a = HipByt::from([42; 42].as_slice());
    {
        let sl = a.as_mut_slice();
        assert_eq!(sl, Some([42; 42].as_mut_slice()));
        sl.unwrap()[0] = 43;
    }
    let mut b = a.clone();
    assert_eq!(b[0], 43);
    assert_eq!(b.as_mut_slice(), None);
    let _ = a.as_slice();
}

#[test]
fn test_to_mut_slice() {
    // static
    let mut a = HipByt::borrowed(b"abc");
    assert!(a.is_borrowed());
    assert_eq!(a.to_mut_slice(), b"abc".to_vec().as_mut_slice());
    assert!(a.is_inline());

    // inline
    let mut a = HipByt::from([42; 3].as_slice());
    assert!(a.is_inline());
    assert_eq!(a.to_mut_slice(), [42; 3].as_mut_slice());
    assert!(a.is_inline());

    // heap
    let mut a = HipByt::from([42; 42].as_slice());
    assert!(a.is_allocated());
    {
        let sl = a.to_mut_slice();
        assert_eq!(sl, [42; 42].as_mut_slice());
        sl[0] = 43;
    }
    let mut b = a.clone();
    assert_eq!(b[0], 43);
    let _ = b.to_mut_slice();
    assert!(b.is_allocated());
    assert_ne!(b.as_ptr(), a.as_ptr());
}

#[test]
fn test_slice_inline() {
    let v: Vec<_> = (0..(INLINE_CAPACITY as u8)).collect();
    let s = HipByt::from(&v[..]);
    let sl = s.slice(0..10);
    assert_eq!(&sl, &v[0..10]);
    let sl = s.slice(..);
    assert_eq!(&sl, &v[..]);
    assert!(sl.is_normalized());
}

#[test]
fn test_slice_borrowed() {
    let v: Vec<_> = (0..42).collect();
    let s = HipByt::borrowed(&v[..]);

    let sl1 = s.slice(4..30);
    assert_eq!(&sl1, &v[4..30]);
    assert_eq!(sl1.as_ptr(), s[4..30].as_ptr());
    assert!(sl1.is_normalized());

    let p = s[9..12].as_ptr();
    drop(s);

    let sl2 = sl1.slice(5..8);
    drop(sl1);
    assert_eq!(&sl2, &v[9..12]);
    assert_eq!(sl2.as_ptr(), p);
    assert!(sl2.is_normalized());
}

#[test]
fn test_slice_allocated() {
    let v: Vec<_> = (0..42).collect();
    let s = HipByt::from(&v[..]);
    assert!(s.is_allocated());

    let sl1 = s.slice(4..30);
    assert_eq!(&sl1, &v[4..30]);
    assert_eq!(sl1.as_ptr(), s[4..30].as_ptr());
    assert!(sl1.is_normalized());
    drop(s);

    let sl2 = sl1.slice(5..8);
    drop(sl1);
    assert_eq!(&sl2, &v[9..12]);
    assert!(sl2.is_inline());
    assert!(sl2.is_normalized());
}

#[test]
#[should_panic]
fn test_slice_panic_start() {
    let a = HipByt::borrowed(b"abc");
    let _b = a.slice(4..);
}

#[test]
#[should_panic]
fn test_slice_panic_end() {
    let a = HipByt::borrowed(b"abc");
    let _b = a.slice(..5);
}

#[test]
#[should_panic]
fn test_slice_panic_mixed() {
    let a = HipByt::borrowed(b"abc");
    let _b = a.slice(3..2);
}

static ABCDEF: HipByt = HipByt::borrowed(b"abcdef");

#[test]
fn test_slice_ok() {
    assert_eq!(ABCDEF.slice(..), b"abcdef");
    assert_eq!(ABCDEF.slice(..1), b"a");
    assert_eq!(ABCDEF.slice(..=1), b"ab");
    assert_eq!(ABCDEF.slice(1..2), b"b");
    assert_eq!(ABCDEF.slice((Bound::Excluded(0), Bound::Included(1))), b"b");
}

#[test]
fn test_try_slice_start_out_of_bounds() {
    let err = ABCDEF.try_slice(7..).unwrap_err();
    assert_eq!(err.kind(), SliceErrorKind::StartOutOfBounds);
    assert_eq!(err.start(), 7);
    assert_eq!(err.end(), 6);
    assert_eq!(err.range(), 7..6);
    assert!(ptr::eq(err.source(), &ABCDEF));
    assert_eq!(format!("{err:?}"), "SliceError { kind: StartOutOfBounds, start: 7, end: 6, bytes: [97, 98, 99, 100, 101, 102] }");
    assert_eq!(
        format!("{err}"),
        "range start index 7 out of bounds for slice of length 6"
    );
    assert_eq!(err.clone(), err);
}

#[test]
fn test_try_slice_end_out_of_bounds() {
    let err = ABCDEF.try_slice(..7).unwrap_err();
    assert_eq!(err.kind(), SliceErrorKind::EndOutOfBounds);
    assert_eq!(
        format!("{err:?}"),
        "SliceError { kind: EndOutOfBounds, start: 0, end: 7, bytes: [97, 98, 99, 100, 101, 102] }"
    );
    assert_eq!(
        format!("{err}"),
        "range end index 7 out of bounds for slice of length 6"
    );
    assert_eq!(err.clone(), err);
}

#[test]
fn test_try_slice_start_greater_than_end() {
    let err = ABCDEF.try_slice(1..0).unwrap_err();
    assert_eq!(err.kind(), SliceErrorKind::StartGreaterThanEnd);
    assert_eq!(format!("{err:?}"), "SliceError { kind: StartGreaterThanEnd, start: 1, end: 0, bytes: [97, 98, 99, 100, 101, 102] }");
    assert_eq!(format!("{err}"), "range starts at 1 but ends at 0");
    assert_eq!(err.clone(), err);
}

#[test]
fn test_try_slice_ok() {
    assert_eq!(ABCDEF.try_slice(..).unwrap(), b"abcdef");
    assert_eq!(ABCDEF.try_slice(..5).unwrap(), b"abcde");
    assert_eq!(ABCDEF.try_slice(1..4).unwrap(), b"bcd");
    assert_eq!(ABCDEF.try_slice(0..=5).unwrap(), b"abcdef");
    assert_eq!(ABCDEF.try_slice(..=1).unwrap(), b"ab");
    assert_eq!(ABCDEF.try_slice(1..).unwrap(), b"bcdef");
    assert_eq!(
        ABCDEF
            .try_slice((Bound::Excluded(0), Bound::Included(1)))
            .unwrap(),
        b"b"
    );
}

#[test]
fn test_empty_vec() {
    let source = vec![];
    let heap_zero = HipByt::from(source);
    assert!(heap_zero.is_normalized());
    assert!(!heap_zero.is_allocated());
    assert_eq!(heap_zero.len(), 0);
    assert_eq!(heap_zero, b"");
}

#[test]
fn test_empty_slice() {
    // should normalize slice
    let source1 = HipByt::from(vec![1, 2, 3]);
    let empty_slice1 = source1.slice(0..0);
    assert!(empty_slice1.is_normalized());
    assert!(!empty_slice1.is_allocated());
    assert!(empty_slice1.is_empty());

    let source2 = HipByt::from(&[1, 2, 3]);
    let empty_slice2 = source2.slice(0..0);
    assert!(empty_slice2.is_normalized());
    assert!(!empty_slice2.is_allocated());
    assert!(empty_slice2.is_empty());
}

#[test]
fn test_into_vec() {
    {
        // static
        let a = HipByt::borrowed(b"abc");
        assert!(a.into_vec().is_err());
    }

    {
        // inline
        let a = HipByt::from(b"abc");
        assert!(a.into_vec().is_err());
    }

    let v = vec![42; INLINE_CAPACITY + 2];
    {
        // allocated, unique
        let v = v.clone();
        let p = v.as_ptr();
        let a = HipByt::from(v);
        let v = a.into_vec().unwrap();
        assert_eq!(p, v.as_ptr());
        assert_eq!(INLINE_CAPACITY + 2, v.len());
    }

    {
        // allocated, shared
        let a = HipByt::from(v.clone());
        let _b = a.clone();
        assert!(a.into_vec().is_err());
    }

    {
        // allocated, unique, sliced at start
        let v = v.clone();
        let p = v.as_ptr();
        let a = HipByt::from(v).slice(0..INLINE_CAPACITY + 1);
        let v = a.into_vec().unwrap();
        assert_eq!(v.len(), INLINE_CAPACITY + 1);
        assert_eq!(v.as_ptr(), p);
    }

    {
        // allocated, unique, sliced at start
        let a = HipByt::from(v).slice(1..5);
        assert!(a.into_vec().is_err());
    }
}

#[test]
fn test_capacity() {
    {
        // static
        let a = HipByt::borrowed(b"abc");
        assert_eq!(a.capacity(), a.len());
    }

    {
        // inline
        let a = HipByt::from(b"abc");
        assert_eq!(a.capacity(), HipByt::inline_capacity());
    }

    {
        // allocated
        let mut v = Vec::with_capacity(42);
        v.extend_from_slice(&b"abc".repeat(10));
        let a = HipByt::from(v);
        assert_eq!(a.capacity(), 42);

        let b = a.slice(1..);
        assert_eq!(b.capacity(), 42);
    }
}

#[test]
fn test_mutate_borrowed() {
    let mut a = HipByt::borrowed(b"abc");
    assert!(a.is_borrowed());
    {
        let mut r = a.mutate();
        assert_eq!(r.as_slice(), b"abc");
        r.extend_from_slice(b"def");
    }
    assert!(!a.is_borrowed());
    assert_eq!(a, b"abcdef");
    assert!(a.is_normalized());
}

#[test]
fn test_mutate_inline() {
    let mut a = HipByt::from(b"abc");
    assert!(a.is_inline());
    a.mutate().extend_from_slice(b"def");
    assert_eq!(a, b"abcdef");
    assert!(a.is_normalized());
}

#[test]
fn test_mutate_allocated() {
    {
        // allocated, unique with enough capacity
        let mut v = Vec::with_capacity(42);
        v.extend_from_slice(b"abcdefghijklmnopqrstuvwxyz");
        let p = v.as_ptr();
        let mut a = HipByt::from(v);
        assert!(a.is_allocated());
        a.mutate().extend_from_slice(b"0123456789");
        assert!(a.is_allocated());
        assert_eq!(a, b"abcdefghijklmnopqrstuvwxyz0123456789",);
        assert_eq!(a.as_ptr(), p);
        assert!(a.is_normalized());
    }

    {
        // allocated, shared
        let mut v = Vec::with_capacity(42);
        v.extend_from_slice(b"abcdefghijklmnopqrstuvwxyz");
        let mut a = HipByt::from(v);
        assert!(a.is_allocated());
        let b = a.clone();
        a.mutate().extend_from_slice(b"0123456789");
        assert!(a.is_allocated());
        assert_eq!(a, b"abcdefghijklmnopqrstuvwxyz0123456789",);
        assert_eq!(b, b"abcdefghijklmnopqrstuvwxyz");
        assert_ne!(a.as_ptr(), b.as_ptr());
        assert!(a.is_normalized());
    }
}

const FORTY_TWOS: &[u8] = &[42; 42];

#[test]
fn test_push_slice_borrowed() {
    #[track_caller]
    fn should_inline(input: &[u8], addition: &[u8], expected: &[u8]) {
        let mut a = HipByt::borrowed(input);
        assert!(a.is_borrowed());
        a.push_slice(addition);
        assert!(a.is_inline());
        assert_eq!(a, expected);
    }

    #[track_caller]
    fn should_allocate(input: &[u8], addition: &[u8], expected: &[u8]) {
        let mut a = HipByt::borrowed(input);
        assert!(a.is_borrowed());
        a.push_slice(addition);
        assert!(a.is_allocated());
        assert_eq!(a, expected);
    }

    should_inline(b"abc", b"def", b"abcdef");

    for i in 0..(INLINE_CAPACITY - 1) {
        // add one byte to a byte string of variable length (< inline capacity)
        should_inline(&FORTY_TWOS[..i], &[42], &FORTY_TWOS[..i + 1]);

        // fill to inline capacity
        should_inline(
            &FORTY_TWOS[..i],
            &FORTY_TWOS[..INLINE_CAPACITY - i],
            &FORTY_TWOS[..INLINE_CAPACITY],
        );

        // overfill by one
        should_allocate(
            &FORTY_TWOS[..i],
            &FORTY_TWOS[..INLINE_CAPACITY - i + 1],
            &FORTY_TWOS[..INLINE_CAPACITY + 1],
        );
    }

    // add one byte to a byte string with a length at max inline capacity
    should_allocate(
        &FORTY_TWOS[..INLINE_CAPACITY],
        &FORTY_TWOS[..1],
        &FORTY_TWOS[..INLINE_CAPACITY + 1],
    );

    let mut a = HipByt::borrowed(FORTY_TWOS);
    a.push_slice(b"abc");
    assert_eq!(&a[..42], FORTY_TWOS);
    assert_eq!(&a[42..], b"abc");
}

#[test]
fn test_push_slice_inline() {
    #[track_caller]
    fn should_stay_inline(input: &[u8], addition: &[u8], expected: &[u8]) {
        let mut a = HipByt::from(input);
        assert!(a.is_inline());
        a.push_slice(addition);
        assert!(a.is_inline());
        assert_eq!(a, expected);
    }
    #[track_caller]
    fn should_allocate(input: &[u8], addition: &[u8], expected: &[u8]) {
        let mut a = HipByt::from(input);
        assert!(a.is_inline());
        a.push_slice(addition);
        assert!(a.is_allocated());
        assert_eq!(a, expected);
    }

    should_stay_inline(b"abc", b"def", b"abcdef");

    let mut a = HipByt::from(b"abc");
    a.push_slice(FORTY_TWOS);
    assert_eq!(&a[..3], b"abc");
    assert_eq!(&a[3..], FORTY_TWOS);

    for i in 0..(INLINE_CAPACITY - 1) {
        // add one byte to an inline byte string of variable length
        should_stay_inline(&FORTY_TWOS[..i], &[42], &FORTY_TWOS[..i + 1]);

        // fill to inline capacity
        should_stay_inline(
            &FORTY_TWOS[..i],
            &FORTY_TWOS[..INLINE_CAPACITY - i],
            &FORTY_TWOS[..INLINE_CAPACITY],
        );

        // overfill by one
        should_allocate(
            &FORTY_TWOS[..i],
            &FORTY_TWOS[..INLINE_CAPACITY - i + 1],
            &FORTY_TWOS[..INLINE_CAPACITY + 1],
        );
    }

    // add one byte to an inline byte string at max length
    should_allocate(
        &FORTY_TWOS[..INLINE_CAPACITY],
        &FORTY_TWOS[..1],
        &FORTY_TWOS[..INLINE_CAPACITY + 1],
    );
}

#[test]
fn test_push_slice_allocated() {
    // allocated, unique
    let mut a = HipByt::from(FORTY_TWOS);
    assert!(a.is_allocated());
    a.push_slice(b"abc");
    assert_eq!(&a[0..42], FORTY_TWOS);
    assert_eq!(&a[42..], b"abc");

    // allocated, not unique
    let mut a = HipByt::from(FORTY_TWOS);
    assert!(a.is_allocated());
    let pa = a.as_ptr();
    let b = a.clone();
    assert_eq!(pa, b.as_ptr());
    a.push_slice(b"abc");
    assert_ne!(a.as_ptr(), pa);
    assert_eq!(&a[0..42], FORTY_TWOS);
    assert_eq!(&a[42..], b"abc");
    assert_eq!(b, FORTY_TWOS);

    // allocated, unique but sliced
    let mut a = {
        let x = HipByt::from(FORTY_TWOS);
        x.slice(1..39)
    };
    assert!(a.is_allocated());
    let p = a.as_ptr();
    a.push_slice(b"abc");
    assert_eq!(&a[..38], &FORTY_TWOS[1..39]);
    assert_eq!(&a[38..], b"abc");
    assert_eq!(a.as_ptr(), p);
    // => the underlying vector is big enough
}

#[test]
fn test_push() {
    // for now, push uses push_slice
    // so test can be minimal

    let mut a = HipByt::from(b"abc");
    a.push(b'd');
    assert_eq!(a, b"abcd");
}

#[test]
fn test_to_owned() {
    let b = b"abc";
    let h = HipByt::from(b);
    assert!(h.is_inline());
    let h = h.into_owned();
    assert!(h.is_inline());

    let v = vec![42; 42];
    let a = HipByt::borrowed(&v[0..2]);
    let a = a.into_owned();
    drop(v);
    assert_eq!(a, [42, 42]);

    let v = vec![42; 42];
    let a = HipByt::from(&v[..]);
    drop(v);
    let p = a.as_ptr();
    let a = a.into_owned();
    assert_eq!(a.as_ptr(), p);
}

#[test]
fn test_make_ascii_lowercase() {
    let mut h = HipByt::from(b"aB0\x80");
    h.make_ascii_lowercase();
    assert_eq!(h, b"ab0\x80");

    let r = b"*".repeat(42);
    let mut h = HipByt::from(&r[..]);
    h.make_ascii_lowercase();
    assert_eq!(h, r);
}

#[test]
fn test_to_ascii_lowercase() {
    let h = HipByt::from(b"aB0\x80");
    let h2 = h.to_ascii_lowercase();
    assert_eq!(h2, b"ab0\x80");
    assert_eq!(h, b"aB0\x80");

    let r = b"*".repeat(42);
    let h = HipByt::from(&r[..]);
    let h2 = h.to_ascii_lowercase();
    assert_eq!(h2, r);
}

#[test]
fn test_make_ascii_uppercase() {
    let mut h = HipByt::from(b"aB0\x80");
    h.make_ascii_uppercase();
    assert_eq!(h, b"AB0\x80");

    let r = b"*".repeat(42);
    let mut h = HipByt::from(&r[..]);
    h.make_ascii_uppercase();
    assert_eq!(h, r);
}

#[test]
fn test_to_ascii_uppercase() {
    let h = HipByt::from(b"aB0\x80");
    let h2 = h.to_ascii_uppercase();
    assert_eq!(h2, b"AB0\x80");
    assert_eq!(h, b"aB0\x80");

    let r = b"*".repeat(42);
    let h = HipByt::from(&r[..]);
    let h2 = h.to_ascii_uppercase();
    assert_eq!(h2, r);
}

#[test]
fn test_repeat() {
    let h = HipByt::new();
    let h50 = h.repeat(50);
    assert_eq!(h50.len(), 0);
    assert!(!h50.is_allocated());

    let h = HipByt::from(b"*".repeat(42));
    let h1 = h.repeat(1);
    assert_eq!(h1.len(), h.len());
    assert_eq!(h.as_ptr(), h1.as_ptr());

    let h = HipByt::from(b"abc");
    let h4 = h.repeat(2);
    assert_eq!(h4, b"abc".repeat(2));
    assert!(h4.is_inline());

    assert_eq!(h.repeat(50), b"abc".repeat(50));
}
