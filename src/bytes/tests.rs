use core::cell::Cell;
use core::mem::MaybeUninit;
use core::ops::Bound;
use core::ptr;
#[cfg(feature = "std")]
use std::collections::HashSet;

// cspell:ignore fastrand
use fastrand::Rng;

use super::{simplify_range, SliceErrorKind};
use crate::alloc::borrow::ToOwned;
use crate::alloc::rc::Rc;
use crate::alloc::vec::Vec;
use crate::alloc::{format, vec};
use crate::HipByt as H;

type S<'a> = &'a [u8];
type Owned = Vec<u8>;
const INLINE_CAPACITY: usize = H::inline_capacity();

const EMPTY_SLICE: S = &[];
const ABC: S = b"abc";
const A: S = b"a";
const B: S = b"b";
const C: S = b"c";
const AB: S = b"ab";
const ABCDEF: S = b"abcdef";
static H_ABCDEF: H = H::borrowed(ABCDEF);
const ALPHABET: &[u8] = b"abcdefghijklmnopqrstuvwxyz";
const MEDIUM: &[u8] = &[42; 42];
const BIG: &[u8] = &[42; 1024];

#[test]
fn test_new_default() {
    let new = H::new();
    assert_eq!(new, EMPTY_SLICE);
    assert!(new.is_empty());

    let new = H::default();
    assert_eq!(new, EMPTY_SLICE);
    assert!(new.is_empty());
}

#[test]
#[cfg(feature = "std")]
fn test_borrow_and_hash() {
    let mut set = HashSet::new();
    set.insert(H::from(A));
    set.insert(H::from(B));

    assert!(set.contains(A));
    assert!(!set.contains(C));
}

#[test]
fn test_fmt() {
    let source = ABC;

    let a = H::borrowed(source);
    assert_eq!(format!("{a:?}"), format!("{source:?}"));

    let a = H::from(source);
    assert_eq!(format!("{a:?}"), format!("{source:?}"));
}

#[test]
fn test_from_owned() {
    let s = Owned::from(MEDIUM);
    let h = H::from(s.clone());
    assert!(!h.is_inline());
    assert!(!h.is_borrowed());
    assert!(h.is_allocated());
    assert_eq!(h.len(), 42);
    assert_eq!(h.as_slice(), s.as_slice());

    let o = Owned::from(ABC);
    let h = H::from(o);
    assert!(h.is_inline());
    assert!(!h.is_borrowed());
    assert!(!h.is_allocated());
    assert_eq!(h.len(), 3);
    assert_eq!(h.as_slice(), ABC);
}

#[test]
fn test_borrowed() {
    let s = BIG;

    for size in [0, 1, INLINE_CAPACITY, INLINE_CAPACITY + 1, 256, 1024] {
        let h = H::borrowed(&s[..size]);
        assert!(!h.is_inline());
        assert!(h.is_borrowed());
        assert!(!h.is_allocated());
        assert_eq!(h.len(), size);
        assert_eq!(h.as_ptr(), s.as_ptr());
    }
}

#[test]
fn test_from_static() {
    fn is_static_type<T: 'static>(_: &T) {}

    let s = ALPHABET;
    let h = H::from_static(s);

    // compiler check
    is_static_type(&h);

    assert!(h.is_borrowed());
    assert!(!h.is_inline());
    assert!(!h.is_allocated());
    assert_eq!(h.len(), s.len());
    assert_eq!(h.as_slice(), s);
    assert_eq!(h.as_ptr(), s.as_ptr());
}

#[test]
fn test_from_slice() {
    let s = BIG;

    for size in [0, 1, INLINE_CAPACITY, INLINE_CAPACITY + 1, 256, 1024] {
        let h = H::from(&s[..size]);
        assert_eq!(size <= INLINE_CAPACITY, h.is_inline());
        assert_eq!(size > INLINE_CAPACITY, h.is_allocated());
        assert_eq!(h.len(), size);
    }
}

#[test]
fn test_as_slice() {
    // static
    {
        let a = H::borrowed(ABC);
        assert!(a.is_borrowed());
        assert!(!a.is_inline());
        assert!(!a.is_allocated());
        assert_eq!(a.as_slice(), ABC);
    }
    // inline
    {
        let a = H::from(ABC);
        assert!(!a.is_borrowed());
        assert!(a.is_inline());
        assert!(!a.is_allocated());
        assert_eq!(a.as_slice(), ABC);
    }
    // allocated
    {
        let a = H::from(Vec::from(MEDIUM));
        assert!(!a.is_borrowed());
        assert!(!a.is_inline());
        assert!(a.is_allocated());
        assert_eq!(a.as_slice(), MEDIUM);
    }
}

#[test]
fn test_clone() {
    // static
    {
        let a = H::borrowed(ABC);
        assert!(a.is_borrowed());
        let b = a.clone();
        drop(a);
        assert_eq!(b.as_slice(), ABC);
        assert_eq!(b.as_ptr(), ABC.as_ptr());
    }

    // inline
    {
        let a = H::from(ABC);
        assert!(a.is_inline());
        let b = a.clone();
        drop(a);
        assert_eq!(b.as_slice(), ABC);
    }

    // allocated
    {
        let v = Owned::from(MEDIUM);
        let p = v.as_ptr();
        let a = H::from(v);
        assert!(a.is_allocated());
        let b = a.clone();
        drop(a);
        assert_eq!(b.as_slice(), MEDIUM);
        assert_eq!(b.as_ptr(), p);
    }
}

#[test]
fn test_clone_drop() {
    let v = Vec::from(MEDIUM);
    let mut rand = Rng::with_seed(0);
    for n in [5, 10, 20, 100] {
        // println!("!n {n}");
        let mut vs = vec![H::from(v.clone()); n];

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
fn test_into_borrowed() {
    // static
    let a = H::borrowed(ABC);
    assert_eq!(a.into_borrowed(), Ok(ABC));

    // inline
    let a = H::from(ABC);
    let b = a.clone();
    assert_eq!(a.into_borrowed(), Err(b));

    // heap
    let a = H::from(MEDIUM);
    let b = a.clone();
    assert_eq!(a.into_borrowed(), Err(b));
}

#[test]
fn test_as_mut_slice() {
    // static
    let mut a = H::borrowed(ABC);
    assert_eq!(a.as_mut_slice(), None);

    // inline
    let mut a = H::from(ABC);
    assert!(a.is_inline());
    assert_eq!(a.as_mut_slice().unwrap(), ABC);

    // heap
    let mut a = H::from(MEDIUM);
    {
        let sl = a.as_mut_slice().unwrap();
        assert_eq!(sl, MEDIUM);
        sl[0] = b'+';
    }
    let mut b = a.clone();
    assert_eq!(b[0], b'+');
    assert_eq!(b.as_mut_slice(), None);
    let _ = a.as_slice();
}

#[test]
fn test_to_mut_slice_static() {
    let mut a = H::borrowed(ABC);
    assert!(a.is_borrowed());
    assert_eq!(a.to_mut_slice(), ABC.to_vec().as_mut_slice());
    assert!(a.is_inline());
}

#[test]
fn test_to_mut_slice_inline() {
    let mut a = H::from(ABC);
    assert!(a.is_inline());
    assert_eq!(a.to_mut_slice(), ABC);
    assert!(a.is_inline());
}

#[test]
fn test_to_mut_slice_allocated() {
    let mut a = H::from(MEDIUM);
    assert!(a.is_allocated());
    {
        let sl = a.to_mut_slice();
        assert_eq!(sl, MEDIUM);
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
    let v = &MEDIUM[0..INLINE_CAPACITY];
    let s = H::from(v);
    let sl = s.slice(0..10);
    assert_eq!(&sl, &v[0..10]);
    let sl = s.slice(..);
    assert_eq!(&sl, v);
    assert!(sl.is_normalized());
}

#[test]
fn test_slice_borrowed() {
    let m = MEDIUM;
    let s = H::borrowed(m);

    let sl1 = s.slice(4..30);
    assert_eq!(&sl1, &m[4..30]);
    assert_eq!(sl1.as_ptr(), s[4..30].as_ptr());
    assert!(sl1.is_normalized());

    let p = s[9..12].as_ptr();
    drop(s);

    let sl2 = sl1.slice(5..8);
    drop(sl1);
    assert_eq!(&sl2, &m[9..12]);
    assert_eq!(sl2.as_ptr(), p);
    assert!(sl2.is_normalized());
}

#[test]
fn test_slice_allocated() {
    let v = MEDIUM;
    let s = H::from(v);
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
    let a = H::borrowed(ABC);
    let _b = a.slice(4..);
}

#[test]
#[should_panic]
fn test_slice_panic_end() {
    let a = H::borrowed(ABC);
    let _b = a.slice(0..5);
}

#[test]
#[should_panic]
fn test_slice_panic_mixed() {
    let a = H::borrowed(ABC);
    let _b = a.slice(3..2);
}

#[test]
fn test_slice_unchecked() {
    use core::ops::Bound;
    let a = H::borrowed(ABC);
    assert_eq!(unsafe { a.slice_unchecked(0..2) }, b"ab");
    assert_eq!(unsafe { a.slice_unchecked(0..=1) }, b"ab");
    assert_eq!(unsafe { a.slice_unchecked(..2) }, b"ab");
    assert_eq!(unsafe { a.slice_unchecked(..) }, ABC);
    assert_eq!(
        unsafe { a.slice_unchecked((Bound::Excluded(0), Bound::Unbounded)) },
        b"bc"
    );
}

#[test]
#[cfg(debug_assertions)]
#[should_panic]
fn test_slice_unchecked_debug_panic_start() {
    let a = H::borrowed(ABC);
    let _ = unsafe { a.slice_unchecked(4..) };
}

#[test]
#[cfg(debug_assertions)]
#[should_panic]
fn test_slice_unchecked_debug_panic_end() {
    let a = H::borrowed(ABC);
    let _ = unsafe { a.slice_unchecked(..5) };
}

#[test]
#[cfg(debug_assertions)]
#[should_panic]
fn test_slice_unchecked_debug_panic_mixed() {
    let a = H::borrowed(ABC);
    let _ = unsafe { a.slice_unchecked(3..2) };
}

#[test]
fn test_slice_ok() {
    assert_eq!(H_ABCDEF.slice(..), ABCDEF);
    assert_eq!(H_ABCDEF.slice(..1), A);
    assert_eq!(H_ABCDEF.slice(..=1), AB);
    assert_eq!(H_ABCDEF.slice(1..2), B);
    assert_eq!(H_ABCDEF.slice((Bound::Excluded(0), Bound::Included(1))), B);
}

#[test]
fn test_try_slice_start_out_of_bounds() {
    let err = H_ABCDEF.try_slice(7..).unwrap_err();
    assert_eq!(err.kind(), SliceErrorKind::StartOutOfBounds);
    assert_eq!(err.start(), 7);
    assert_eq!(err.end(), 6);
    assert_eq!(err.range(), 7..6);
    assert!(ptr::eq(err.source(), &H_ABCDEF));
    assert_eq!(format!("{err:?}"), "SliceError { kind: StartOutOfBounds, start: 7, end: 6, bytes: [97, 98, 99, 100, 101, 102] }");
    assert_eq!(
        format!("{err}"),
        "range start index 7 out of bounds for slice of length 6"
    );
    assert_eq!(err.clone(), err);
}

#[test]
fn test_try_slice_end_out_of_bounds() {
    let err = H_ABCDEF.try_slice(..7).unwrap_err();
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
    let err = H_ABCDEF.try_slice(1..0).unwrap_err();
    assert_eq!(err.kind(), SliceErrorKind::StartGreaterThanEnd);
    assert_eq!(format!("{err:?}"), "SliceError { kind: StartGreaterThanEnd, start: 1, end: 0, bytes: [97, 98, 99, 100, 101, 102] }");
    assert_eq!(format!("{err}"), "range starts at 1 but ends at 0");
    assert_eq!(err.clone(), err);
}

#[test]
fn test_try_slice_ok() {
    assert_eq!(H_ABCDEF.try_slice(..).unwrap(), b"abcdef");
    assert_eq!(H_ABCDEF.try_slice(..5).unwrap(), b"abcde");
    assert_eq!(H_ABCDEF.try_slice(1..4).unwrap(), b"bcd");
    assert_eq!(H_ABCDEF.try_slice(0..=5).unwrap(), b"abcdef");
    assert_eq!(H_ABCDEF.try_slice(..=1).unwrap(), b"ab");
    assert_eq!(H_ABCDEF.try_slice(1..).unwrap(), b"bcdef");
    assert_eq!(
        H_ABCDEF
            .try_slice((Bound::Excluded(0), Bound::Included(1)))
            .unwrap(),
        B
    );
}

#[test]
fn test_empty_vec() {
    let source = vec![];
    let heap_zero = H::from(source);
    assert!(heap_zero.is_normalized());
    assert!(!heap_zero.is_allocated());
    assert_eq!(heap_zero.len(), 0);
    assert_eq!(heap_zero, EMPTY_SLICE);
}

#[test]
fn test_empty_slice() {
    // should normalize slice
    let source1 = H::from(vec![1, 2, 3]);
    let empty_slice1 = source1.slice(0..0);
    assert!(empty_slice1.is_normalized());
    assert!(!empty_slice1.is_allocated());
    assert!(empty_slice1.is_empty());

    let source2 = H::from(&[1, 2, 3]);
    let empty_slice2 = source2.slice(0..0);
    assert!(empty_slice2.is_normalized());
    assert!(!empty_slice2.is_allocated());
    assert!(empty_slice2.is_empty());
}

#[test]
fn test_into_vec() {
    {
        // static
        let a = H::borrowed(ABC);
        assert!(a.into_vec().is_err());
    }

    {
        // inline
        let a = H::from(ABC);
        assert!(a.into_vec().is_err());
    }

    let v = vec![42; INLINE_CAPACITY + 2];
    {
        // allocated, unique
        let v = v.clone();
        let p = v.as_ptr();
        let a = H::from(v);
        let v = a.into_vec().unwrap();
        assert_eq!(p, v.as_ptr());
        assert_eq!(INLINE_CAPACITY + 2, v.len());
    }

    {
        // allocated, shared
        let a = H::from(v.clone());
        let _b = a.clone();
        assert!(a.into_vec().is_err());
    }

    {
        // allocated, unique, sliced at start
        let v = v.clone();
        let p = v.as_ptr();
        let a = H::from(v).slice(0..INLINE_CAPACITY + 1);
        let v = a.into_vec().unwrap();
        assert_eq!(v.len(), INLINE_CAPACITY + 1);
        assert_eq!(v.as_ptr(), p);
    }

    {
        // allocated, unique, sliced at start
        let a = H::from(v).slice(1..5);
        assert!(a.into_vec().is_err());
    }
}

#[test]
fn test_capacity() {
    {
        // static
        let a = H::borrowed(ABC);
        assert_eq!(a.capacity(), a.len());
    }

    {
        // inline
        let a = H::from(ABC);
        assert_eq!(a.capacity(), H::inline_capacity());
    }

    {
        // allocated
        let mut v = Vec::with_capacity(42);
        v.extend_from_slice(&ABC.repeat(10));
        let a = H::from(v);
        assert_eq!(a.capacity(), 42);

        let b = a.slice(1..);
        assert_eq!(b.capacity(), 42);
    }
}

#[test]
fn test_mutate_borrowed() {
    let mut a = H::borrowed(ABC);
    assert!(a.is_borrowed());
    {
        let mut r = a.mutate();
        assert_eq!(r.as_slice(), ABC);
        r.extend_from_slice(b"def");
    }
    assert!(!a.is_borrowed());
    assert_eq!(a, b"abcdef");
    assert!(a.is_normalized());
}

#[test]
fn test_mutate_inline() {
    let mut a = H::from(ABC);
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
        let mut a = H::from(v);
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
        let mut a = H::from(v);
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

#[test]
fn test_push_slice_borrowed() {
    #[track_caller]
    fn should_inline(input: S, addition: S, expected: S) {
        let mut a = H::borrowed(input);
        assert!(a.is_borrowed());
        a.push_slice(addition);
        assert!(a.is_inline());
        assert_eq!(a, expected);
    }

    #[track_caller]
    fn should_allocate(input: S, addition: S, expected: S) {
        let mut a = H::borrowed(input);
        assert!(a.is_borrowed());
        a.push_slice(addition);
        assert!(a.is_allocated());
        assert_eq!(a, expected);
    }

    should_inline(ABC, b"def", b"abcdef");

    for i in 0..(INLINE_CAPACITY - 1) {
        // add one byte to a byte string of variable length (< inline capacity)
        should_inline(&MEDIUM[..i], &[42], &MEDIUM[..i + 1]);

        // fill to inline capacity
        should_inline(
            &MEDIUM[..i],
            &MEDIUM[..INLINE_CAPACITY - i],
            &MEDIUM[..INLINE_CAPACITY],
        );

        // overfill by one
        should_allocate(
            &MEDIUM[..i],
            &MEDIUM[..INLINE_CAPACITY - i + 1],
            &MEDIUM[..INLINE_CAPACITY + 1],
        );
    }

    // add one byte to a byte string with a length at max inline capacity
    should_allocate(
        &MEDIUM[..INLINE_CAPACITY],
        &MEDIUM[..1],
        &MEDIUM[..INLINE_CAPACITY + 1],
    );

    let mut a = H::borrowed(MEDIUM);
    a.push_slice(ABC);
    assert_eq!(&a[..42], MEDIUM);
    assert_eq!(&a[42..], ABC);
}

#[test]
fn test_push_slice_inline() {
    #[track_caller]
    fn should_stay_inline(input: S, addition: S, expected: S) {
        let mut a = H::from(input);
        assert!(a.is_inline());
        a.push_slice(addition);
        assert!(a.is_inline());
        assert_eq!(a, expected);
    }
    #[track_caller]
    fn should_allocate(input: S, addition: S, expected: S) {
        let mut a = H::from(input);
        assert!(a.is_inline());
        a.push_slice(addition);
        assert!(a.is_allocated());
        assert_eq!(a, expected);
    }

    should_stay_inline(ABC, b"def", b"abcdef");

    let mut a = H::from(ABC);
    a.push_slice(MEDIUM);
    assert_eq!(&a[..3], ABC);
    assert_eq!(&a[3..], MEDIUM);

    for i in 0..(INLINE_CAPACITY - 1) {
        // add one byte to an inline byte string of variable length
        should_stay_inline(&MEDIUM[..i], &[42], &MEDIUM[..i + 1]);

        // fill to inline capacity
        should_stay_inline(
            &MEDIUM[..i],
            &MEDIUM[..INLINE_CAPACITY - i],
            &MEDIUM[..INLINE_CAPACITY],
        );

        // overfill by one
        should_allocate(
            &MEDIUM[..i],
            &MEDIUM[..INLINE_CAPACITY - i + 1],
            &MEDIUM[..INLINE_CAPACITY + 1],
        );
    }

    // add one byte to an inline byte string at max length
    should_allocate(
        &MEDIUM[..INLINE_CAPACITY],
        &MEDIUM[..1],
        &MEDIUM[..INLINE_CAPACITY + 1],
    );
}

#[test]
fn test_push_slice_allocated() {
    // allocated, unique
    let mut a = H::from(MEDIUM);
    assert!(a.is_allocated());
    a.push_slice(ABC);
    assert_eq!(&a[0..42], MEDIUM);
    assert_eq!(&a[42..], ABC);

    // allocated, not unique
    let mut a = H::from(MEDIUM);
    assert!(a.is_allocated());
    let pa = a.as_ptr();
    let b = a.clone();
    assert_eq!(pa, b.as_ptr());
    a.push_slice(ABC);
    assert_ne!(a.as_ptr(), pa);
    assert_eq!(&a[0..42], MEDIUM);
    assert_eq!(&a[42..], ABC);
    assert_eq!(b, MEDIUM);

    // allocated, unique but sliced
    let mut a = {
        let x = H::from(MEDIUM);
        x.slice(1..39)
    };
    assert!(a.is_allocated());
    let p = a.as_ptr();
    a.push_slice(ABC);
    assert_eq!(&a[..38], &MEDIUM[1..39]);
    assert_eq!(&a[38..], ABC);
    assert_eq!(a.as_ptr(), p);
    // => the underlying vector is big enough
}

#[test]
fn test_push() {
    // for now, push uses push_slice
    // so test can be minimal

    let mut a = H::from(ABC);
    a.push(b'd');
    assert_eq!(a, b"abcd");
}

#[test]
fn test_to_owned() {
    let b = ABC;
    let h = H::from(b);
    assert!(h.is_inline());
    let h = h.into_owned();
    assert!(h.is_inline());

    let v = vec![42; 42];
    let a = H::borrowed(&v[0..2]);
    let a = a.into_owned();
    drop(v);
    assert_eq!(a, [42, 42]);

    let v = vec![42; 42];
    let a = H::from(&v[..]);
    drop(v);
    let p = a.as_ptr();
    let a = a.into_owned();
    assert_eq!(a.as_ptr(), p);
}

#[test]
fn test_make_ascii_lowercase() {
    let mut h = H::from(b"aB0\x80");
    h.make_ascii_lowercase();
    assert_eq!(h, b"ab0\x80");

    let r = b"*".repeat(42);
    let mut h = H::from(&r[..]);
    h.make_ascii_lowercase();
    assert_eq!(h, r);
}

#[test]
fn test_to_ascii_lowercase() {
    let h = H::from(b"aB0\x80");
    let h2 = h.to_ascii_lowercase();
    assert_eq!(h2, b"ab0\x80");
    assert_eq!(h, b"aB0\x80");

    let r = b"*".repeat(42);
    let h = H::from(&r[..]);
    let h2 = h.to_ascii_lowercase();
    assert_eq!(h2, r);
}

#[test]
fn test_make_ascii_uppercase() {
    let mut h = H::from(b"aB0\x80");
    h.make_ascii_uppercase();
    assert_eq!(h, b"AB0\x80");

    let r = b"*".repeat(42);
    let mut h = H::from(&r[..]);
    h.make_ascii_uppercase();
    assert_eq!(h, r);
}

#[test]
fn test_to_ascii_uppercase() {
    let h = H::from(b"aB0\x80");
    let h2 = h.to_ascii_uppercase();
    assert_eq!(h2, b"AB0\x80");
    assert_eq!(h, b"aB0\x80");

    let r = b"*".repeat(42);
    let h = H::from(&r[..]);
    let h2 = h.to_ascii_uppercase();
    assert_eq!(h2, r);
}

#[test]
fn test_repeat() {
    let h = H::new();
    let h50 = h.repeat(50);
    assert_eq!(h50.len(), 0);
    assert!(!h50.is_allocated());

    let h = H::from(MEDIUM);
    let h1 = h.repeat(1);
    assert_eq!(h1.len(), h.len());
    assert_eq!(h.as_ptr(), h1.as_ptr());

    let h = H::from(ABC);
    let h4 = h.repeat(2);
    assert_eq!(h4, ABC.repeat(2));
    assert!(h4.is_inline());

    assert_eq!(h.repeat(50), ABC.repeat(50));
}

#[test]
fn test_simplify_range() {
    assert_eq!(simplify_range(0..10, 10), Ok(0..10));
    assert_eq!(simplify_range(.., 10), Ok(0..10));
    assert_eq!(simplify_range(..10, 10), Ok(0..10));
    assert_eq!(simplify_range(..=9, 10), Ok(0..10));
    assert_eq!(
        simplify_range((Bound::Included(0), Bound::Excluded(10)), 10),
        Ok(0..10)
    );
    assert_eq!(
        simplify_range((Bound::Unbounded, Bound::Excluded(10)), 10),
        Ok(0..10)
    );
    assert_eq!(
        simplify_range((Bound::Included(0), Bound::Unbounded), 10),
        Ok(0..10)
    );
    assert_eq!(
        simplify_range((Bound::<usize>::Unbounded, Bound::Unbounded), 10),
        Ok(0..10)
    );

    assert_eq!(simplify_range(1..10, 10), Ok(1..10));
    assert_eq!(simplify_range(1.., 10), Ok(1..10));
    assert_eq!(
        simplify_range((Bound::Included(1), Bound::Excluded(10)), 10),
        Ok(1..10)
    );
    assert_eq!(
        simplify_range((Bound::Excluded(0), Bound::Excluded(10)), 10),
        Ok(1..10)
    );
    assert_eq!(
        simplify_range((Bound::Included(1), Bound::Unbounded), 10),
        Ok(1..10)
    );
    assert_eq!(
        simplify_range((Bound::Excluded(0), Bound::Excluded(10)), 10),
        Ok(1..10)
    );

    assert_eq!(
        simplify_range(11..13, 10),
        Err((11, 13, SliceErrorKind::StartOutOfBounds))
    );
    assert_eq!(
        simplify_range((Bound::Included(11), Bound::Excluded(13)), 10),
        Err((11, 13, SliceErrorKind::StartOutOfBounds))
    );
    assert_eq!(
        simplify_range(11..=12, 10),
        Err((11, 13, SliceErrorKind::StartOutOfBounds))
    );
    assert_eq!(
        simplify_range((Bound::Included(11), Bound::Included(12)), 10),
        Err((11, 13, SliceErrorKind::StartOutOfBounds))
    );
    assert_eq!(
        simplify_range(11.., 10),
        Err((11, 10, SliceErrorKind::StartOutOfBounds))
    );
    assert_eq!(
        simplify_range((Bound::Included(11), Bound::Unbounded), 10),
        Err((11, 10, SliceErrorKind::StartOutOfBounds))
    );

    assert_eq!(
        simplify_range(9..8, 10),
        Err((9, 8, SliceErrorKind::StartGreaterThanEnd))
    );
    assert_eq!(
        simplify_range(9..=7, 10),
        Err((9, 8, SliceErrorKind::StartGreaterThanEnd))
    );
}

#[test]
fn test_slice_ref_unchecked() {
    let s = Owned::from(ABC);
    let a = H::borrowed(s.as_slice());

    unsafe {
        assert_eq!(a.slice_ref_unchecked(&a[0..1]), A);
        assert_eq!(a.slice_ref_unchecked(&a[0..0]), EMPTY_SLICE);
        assert_eq!(a.slice_ref_unchecked(&a[3..3]), EMPTY_SLICE);
    }

    let a = H::from(s.as_slice());

    unsafe {
        assert_eq!(a.slice_ref_unchecked(&a[0..1]), A);
        assert_eq!(a.slice_ref_unchecked(&a[0..0]), EMPTY_SLICE);
        assert_eq!(a.slice_ref_unchecked(&a[3..3]), EMPTY_SLICE);
    }

    let s = b"*".repeat(42);
    let a = H::from(s);

    unsafe {
        assert_eq!(a.slice_ref_unchecked(&a[0..1]), b"*");
        assert_eq!(a.slice_ref_unchecked(&a[0..41]).as_ptr(), a.as_ptr());
        assert_eq!(a.slice_ref_unchecked(&a[0..0]), EMPTY_SLICE);
        assert_eq!(a.slice_ref_unchecked(&a[3..3]), EMPTY_SLICE);
    }
}

#[test]
fn test_try_slice_ref() {
    let s = Owned::from(ABC);
    let a = H::borrowed(s.as_slice());

    assert_eq!(a.try_slice_ref(&a[0..1]).unwrap(), A);
    assert_eq!(a.try_slice_ref(&a[0..0]).unwrap(), EMPTY_SLICE);
    assert_eq!(a.try_slice_ref(&a[3..3]).unwrap(), EMPTY_SLICE);

    assert!(a.try_slice_ref(ABC).is_none());
    assert!(a.try_slice_ref(EMPTY_SLICE).is_none());

    let b = H::borrowed(&s[0..2]);
    assert!(b.try_slice_ref(&s[1..3]).is_none());
}

#[test]
fn test_slice_ref() {
    let s = Owned::from(ABC);
    let a = H::borrowed(s.as_slice());
    assert_eq!(a.slice_ref(&a[0..1]), A);
    assert_eq!(a.slice_ref(&a[0..0]), EMPTY_SLICE);
    assert_eq!(a.slice_ref(&a[3..3]), EMPTY_SLICE);
}

#[test]
#[should_panic]
fn test_slice_ref_panic() {
    let s = Owned::from(ABC);
    let a = H::borrowed(s.as_slice());
    let _ = a.slice_ref(ABC);
}

#[test]
fn test_spare_capacity_mut() {
    let mut h = H::from_static(ABC);
    assert!(h.spare_capacity_mut().is_empty());

    let mut h = H::from(ABC);
    assert_eq!(h.spare_capacity_mut().len(), INLINE_CAPACITY - ABC.len());

    let mut h = H::with_capacity(42);
    assert_eq!(h.spare_capacity_mut().len(), 42);
}

#[test]
fn test_spare_capacity_mut_shared() {
    let mut h = H::from(MEDIUM);
    let h2 = h.clone();
    assert!(h.spare_capacity_mut().is_empty());
    let _ = h2;
}

#[test]
fn test_set_len() {
    let mut h = H::with_capacity(INLINE_CAPACITY);
    assert_eq!(h.len(), 0);
    h.spare_capacity_mut().fill(MaybeUninit::new(0));
    unsafe {
        h.set_len(10);
    }
    assert_eq!(h.len(), 10);

    let mut h = H::with_capacity(INLINE_CAPACITY + 1);
    assert_eq!(h.len(), 0);
    unsafe {
        h.set_len(0);
    }
    assert_eq!(h.len(), 0);
    h.spare_capacity_mut().fill(MaybeUninit::new(0));
    unsafe {
        h.set_len(10);
    }
    assert_eq!(h.len(), 10);

    let mut x = H::borrowed(b"abc");
    unsafe {
        x.set_len(3);
    }
}

#[test]
#[cfg(debug_assertions)]
#[should_panic]
fn test_set_len_debug_panic() {
    let mut x = H::borrowed(b"abc");
    unsafe {
        x.set_len(4);
    }
}

#[test]
fn test_concat_slices() {
    let h = H::concat_slices(&[]);
    assert!(h.is_empty());

    let slices: &[S] = &[A, B, C];
    let h = H::concat_slices(slices);
    assert_eq!(h, slices.concat());
    assert!(h.is_inline());

    let slices: &[S] = &[A, B, C, MEDIUM];
    let h = H::concat_slices(slices);
    assert_eq!(h, slices.concat());
    assert!(h.is_allocated());
}

#[test]
fn test_concat() {
    let slices: &[S] = &[];
    let h = H::concat(slices);
    assert_eq!(h, EMPTY_SLICE);

    let slices: &[&[_; 1]] = &[b"a", b"b", b"c"];
    let h = H::concat(slices);
    assert_eq!(h, ABC);
    assert!(h.is_inline());

    let long = MEDIUM.to_owned();
    let slices: &[Vec<_>] = &[A.into(), B.into(), C.into(), long.clone()];
    let h = H::concat(slices);
    assert_eq!(h, [ABC, long.as_slice()].concat());
    assert!(h.is_allocated());
}

#[test]
#[should_panic]
fn test_concat_bad_iter() {
    #[derive(Clone)]
    struct I(Option<Rc<Cell<&'static [u8]>>>);

    impl Iterator for I {
        type Item = &'static [u8];
        fn next(&mut self) -> Option<Self::Item> {
            self.0.take().map(|x| x.replace(b"longer"))
        }
    }

    let _h = H::concat(I(Some(Rc::new(Cell::new(b"long")))));
}

#[test]
fn test_join_slices() {
    let h = H::join_slices(&[], b",");
    assert!(h.is_empty());

    let slices: &[&[_]] = &[A, B, C];
    let h = H::join_slices(slices, b",");
    assert_eq!(h, b"a,b,c");
    assert!(h.is_inline());

    let long = b"*".repeat(42);
    let slices: &[&[_]] = &[A, B, C, &long];
    let h = H::join_slices(slices, b",");
    assert_eq!(h, slices.join(b",".as_slice()));
    assert!(h.is_allocated());
}

#[test]
fn test_join() {
    let slices: &[S] = &[];
    let h = H::join(slices, b",");
    assert!(h.is_empty());

    let slices: &[&[_; 1]] = &[b"a", b"b", b"c"];
    let h = H::join(slices, b",");
    assert_eq!(h, b"a,b,c");
    assert!(h.is_inline());

    let long = b"*".repeat(42);
    let slices: &[Vec<_>] = &[A.into(), B.into(), C.into(), long.clone()];
    let h = H::join(slices, b",");
    assert_eq!(h, [b"a,b,c,".as_slice(), long.as_slice()].concat());
    assert!(h.is_allocated());
}

#[test]
#[should_panic]
fn test_join_bad_iter() {
    #[derive(Clone)]
    struct I(Option<Rc<Cell<&'static [u8]>>>);

    impl Iterator for I {
        type Item = &'static [u8];
        fn next(&mut self) -> Option<Self::Item> {
            self.0.take().map(|x| x.replace(b"longer"))
        }
    }

    let _h = H::join(I(Some(Rc::new(Cell::new(b"long")))), b",");
}

#[test]
#[should_panic]
fn test_join_bad_iter2() {
    #[derive(Clone)]
    struct I(alloc::vec::IntoIter<Rc<Cell<&'static [u8]>>>);

    impl Iterator for I {
        type Item = &'static [u8];
        fn next(&mut self) -> Option<Self::Item> {
            self.0.next().map(|x| x.replace(b"ab"))
        }
    }

    let _h = H::join(
        I(vec![Rc::new(Cell::new(b"ab".as_slice())), Rc::new(Cell::new(B))].into_iter()),
        b",",
    );
}
