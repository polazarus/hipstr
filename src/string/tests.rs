use core::cell::Cell;
use core::ops::Bound;
use core::ptr;
#[cfg(feature = "std")]
use std::collections::HashSet;

use super::SliceErrorKind;
use crate::alloc::borrow::ToOwned;
use crate::alloc::rc::Rc;
use crate::alloc::string::{String, ToString};
use crate::alloc::{format, vec};
use crate::{HipByt, HipStr as H};

type S<'a> = &'a str;
type Owned = String;
const INLINE_CAPACITY: usize = H::inline_capacity();

const EMPTY_SLICE: S = "";
const ABC: S = "abc";
const A: S = "a";
const B: S = "b";
const C: S = "c";
const AB: S = "ab";
const ABCDEF: S = "abcdef";
static H_ABCDEF: H = H::borrowed(ABCDEF);
const ALPHABET: &str = "abcdefghijklmnopqrstuvwxyz";
const MEDIUM: &str = {
    let Ok(s) = core::str::from_utf8(&[42; 42]) else {
        panic!()
    };
    s
};
const BIG: &str = {
    let Ok(s) = core::str::from_utf8(&[42; 1024]) else {
        panic!()
    };
    s
};

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
fn test_with_capacity() {
    let h = H::with_capacity(0);
    assert_eq!(h, EMPTY_SLICE);
    assert!(h.is_empty());
    assert_eq!(h.capacity(), INLINE_CAPACITY);

    let mut h = H::with_capacity(42);
    let p = h.as_ptr();
    assert_eq!(h, EMPTY_SLICE);
    assert!(h.is_empty());
    assert_eq!(h.capacity(), 42);
    for _ in 0..42 {
        h.push_str(A);
    }
    assert_eq!(h.len(), 42);
    assert_eq!(h, A.repeat(42));
    assert_eq!(h.as_ptr(), p);
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
    assert_eq!(format!("{a}"), source);
    assert_eq!(format!("{a:?}"), format!("{source:?}"));

    let a = H::from(source);
    assert_eq!(format!("{a}"), source);
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
    assert_eq!(h.as_str(), s.as_str());

    let o = Owned::from(ABC);
    let h = H::from(o);
    assert!(h.is_inline());
    assert!(!h.is_borrowed());
    assert!(!h.is_allocated());
    assert_eq!(h.len(), 3);
    assert_eq!(h.as_str(), ABC);
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
    const fn is_static_type<T: 'static>(_: &T) {}

    let s = ALPHABET;
    let h = H::from_static(s);

    // compiler check
    is_static_type(&h);

    assert!(h.is_borrowed());
    assert!(!h.is_inline());
    assert!(!h.is_allocated());
    assert_eq!(h.len(), s.len());
    assert_eq!(h.as_str(), s);
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
        assert_eq!(a.as_str(), ABC);
    }
    // inline
    {
        let a = H::from(ABC);
        assert!(!a.is_borrowed());
        assert!(a.is_inline());
        assert!(!a.is_allocated());
        assert_eq!(a.as_str(), ABC);
    }
    // allocated
    {
        let a = H::from(String::from(MEDIUM));
        assert!(!a.is_borrowed());
        assert!(!a.is_inline());
        assert!(a.is_allocated());
        assert_eq!(a.as_str(), MEDIUM);
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
        assert_eq!(b.as_str(), ABC);
        assert_eq!(b.as_ptr(), ABC.as_ptr());
    }

    // inline
    {
        let a = H::from(ABC);
        assert!(a.is_inline());
        let b = a.clone();
        drop(a);
        assert_eq!(b.as_str(), ABC);
    }

    // allocated
    {
        let v = Owned::from(MEDIUM);
        let p = v.as_ptr();
        let a = H::from(v);
        assert!(a.is_allocated());
        let b = a.clone();
        drop(a);
        assert_eq!(b.as_str(), MEDIUM);
        assert_eq!(b.as_ptr(), p);
    }
}

#[test]
fn test_into_borrowed() {
    // borrowed
    let a = H::borrowed(ABC);
    let s = a.into_borrowed().unwrap();
    assert_eq!(s, ABC);
    assert!(core::ptr::eq(s, ABC));

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
fn test_as_borrowed() {
    // borrowed
    let a = H::borrowed(ABC);
    let b = a.as_borrowed().unwrap();
    assert_eq!(b, ABC);
    assert!(core::ptr::eq(b, ABC));

    // inline
    let a = H::from(ABC);
    assert_eq!(a.as_borrowed(), None);

    // heap
    let a = H::from(MEDIUM);
    assert_eq!(a.as_borrowed(), None);
}

#[test]
fn test_as_mut_str() {
    // static
    let mut a = H::borrowed(ABC);
    assert_eq!(a.as_mut_str(), None);

    // inline
    let mut a = H::from(ABC);
    assert!(a.is_inline());
    assert_eq!(a.as_mut_str().unwrap(), ABC);

    // heap
    let mut a = H::from(MEDIUM);
    {
        let sl = a.as_mut_str().unwrap();
        assert_eq!(sl, MEDIUM);
        unsafe {
            sl.as_bytes_mut()[0] = b'+';
        }
    }
    let mut b = a.clone();
    assert!(b.starts_with('+'));
    assert_eq!(b.as_mut_str(), None);
    let _ = a.as_str();
}

#[test]
fn test_to_mut_str_static() {
    let mut a = H::borrowed(ABC);
    assert!(a.is_borrowed());
    assert_eq!(a.to_mut_str(), ABC.to_string().as_mut_str());
    assert!(a.is_inline());
}

#[test]
fn test_to_mut_str_inline() {
    let mut a = H::from(ABC);
    assert!(a.is_inline());
    assert_eq!(a.to_mut_str(), ABC);
    assert!(a.is_inline());
}

#[test]
fn test_to_mut_str_allocated() {
    let mut a = H::from(MEDIUM);
    assert!(a.is_allocated());
    {
        let sl = a.to_mut_str();
        assert_eq!(sl, MEDIUM);
        unsafe {
            sl.as_bytes_mut()[0] = b'+';
        }
    }

    let mut b = a.clone();
    assert!(b.starts_with('+'));
    let _ = b.to_mut_str();
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
}

#[test]
fn test_slice_borrowed() {
    let m = MEDIUM;
    let s = H::borrowed(m);

    let sl1 = s.slice(4..30);
    assert_eq!(&sl1, &m[4..30]);
    assert_eq!(sl1.as_ptr(), s[4..30].as_ptr());

    let p = s[9..12].as_ptr();
    drop(s);

    let sl2 = sl1.slice(5..8);
    drop(sl1);
    assert_eq!(&sl2, &m[9..12]);
    assert_eq!(sl2.as_ptr(), p);
}

#[test]
fn test_slice_allocated() {
    let v = MEDIUM;
    let s = H::from(v);
    assert!(s.is_allocated());

    let sl1 = s.slice(4..30);
    assert_eq!(&sl1, &v[4..30]);
    assert_eq!(sl1.as_ptr(), s[4..30].as_ptr());
    drop(s);

    let sl2 = sl1.slice(5..8);
    drop(sl1);
    assert_eq!(&sl2, &v[9..12]);
    assert!(sl2.is_inline());
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
#[should_panic]
fn test_slice_panic_start_char_boundary() {
    let a = H::borrowed("\u{1F980}");
    let _b = a.slice(1..);
}

#[test]
#[should_panic]
fn test_slice_panic_end_char_boundary() {
    let a = H::borrowed("\u{1F980}");
    let _b = a.slice(0..2);
}

#[test]
fn test_slice_unchecked() {
    use core::ops::Bound;
    let a = H::borrowed(ABC);
    assert_eq!(unsafe { a.slice_unchecked(0..2) }, "ab");
    assert_eq!(unsafe { a.slice_unchecked(0..=1) }, "ab");
    assert_eq!(unsafe { a.slice_unchecked(..2) }, "ab");
    assert_eq!(unsafe { a.slice_unchecked(..) }, ABC);
    assert_eq!(
        unsafe { a.slice_unchecked((Bound::Excluded(0), Bound::Unbounded)) },
        "bc"
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
#[cfg(debug_assertions)]
#[should_panic]
fn test_slice_unchecked_debug_start_char_boundary_panic() {
    let a = H::borrowed("\u{1F980}");
    let _ = unsafe { a.slice_unchecked(1..) };
}

#[test]
#[cfg(debug_assertions)]
#[should_panic]
fn test_slice_unchecked_debug_end_char_boundary_panic() {
    let a = H::borrowed("\u{1F980}");
    let _ = unsafe { a.slice_unchecked(..1) };
}

#[test]
fn test_slice_ok() {
    assert_eq!(H_ABCDEF.slice(..), ABCDEF);
    assert_eq!(H_ABCDEF.slice(..1), A);
    assert_eq!(H_ABCDEF.slice(..=1), AB);
    assert_eq!(H_ABCDEF.slice(1..2), B);
    assert_eq!(H_ABCDEF.slice((Bound::Excluded(0), Bound::Included(1))), B);
}

static RUST_CRAB: H = H::borrowed("Rust \u{1F980}");

#[test]
fn test_try_slice_start_out_of_bounds() {
    let err = RUST_CRAB.try_slice(10..).unwrap_err();
    assert_eq!(err.kind(), SliceErrorKind::StartOutOfBounds);
    assert_eq!(err.start(), 10);
    assert_eq!(err.end(), RUST_CRAB.len());
    assert_eq!(err.range(), 10..RUST_CRAB.len());
    assert!(ptr::eq(err.source(), &RUST_CRAB));
    assert_eq!(
        format!("{err:?}"),
        "SliceError { kind: StartOutOfBounds, start: 10, end: 9, string: \"Rust \u{1F980}\" }"
    );
    assert_eq!(
        format!("{err}"),
        "range start index 10 is out of bounds of `Rust \u{1F980}`"
    );
    assert_eq!(err.clone(), err);
}

#[test]
fn test_try_slice_end_out_of_bounds() {
    let err = RUST_CRAB.try_slice(..10).unwrap_err();
    assert_eq!(err.kind(), SliceErrorKind::EndOutOfBounds);
    assert_eq!(
        format!("{err:?}"),
        "SliceError { kind: EndOutOfBounds, start: 0, end: 10, string: \"Rust \u{1F980}\" }"
    );
    assert_eq!(
        format!("{err}"),
        "range end index 10 is out of bounds of `Rust \u{1F980}`"
    );
    assert_eq!(err.clone(), err);
}

#[test]
fn test_try_slice_start_greater_than_end() {
    let err = RUST_CRAB.try_slice(4..2).unwrap_err();
    assert_eq!(err.kind(), SliceErrorKind::StartGreaterThanEnd);
    assert_eq!(
        format!("{err:?}"),
        "SliceError { kind: StartGreaterThanEnd, start: 4, end: 2, string: \"Rust \u{1F980}\" }"
    );
    assert_eq!(
        format!("{err}"),
        "range starts at 4 but ends at 2 when slicing `Rust \u{1F980}`"
    );
    assert_eq!(err.clone(), err);
}

#[test]
fn test_try_slice_start_not_a_char_boundary() {
    let err = RUST_CRAB.try_slice(6..).unwrap_err();
    assert_eq!(err.kind(), SliceErrorKind::StartNotACharBoundary);
    assert_eq!(
        format!("{err:?}"),
        "SliceError { kind: StartNotACharBoundary, start: 6, end: 9, string: \"Rust \u{1F980}\" }"
    );
    assert_eq!(
        format!("{err}"),
        "range start index 6 is not a char boundary of `Rust \u{1F980}`"
    );
}

#[test]
fn test_try_slice_end_not_a_char_boundary() {
    let err = RUST_CRAB.try_slice(..6).unwrap_err();
    assert_eq!(err.kind(), SliceErrorKind::EndNotACharBoundary);
    assert_eq!(
        format!("{err:?}"),
        "SliceError { kind: EndNotACharBoundary, start: 0, end: 6, string: \"Rust \u{1F980}\" }"
    );
    assert_eq!(
        format!("{err}"),
        "range end index 6 is not a char boundary of `Rust \u{1F980}`"
    );
    assert_eq!(err.clone(), err);
}

#[test]
fn test_try_slice_ok() {
    let s = RUST_CRAB.as_str();
    assert_eq!(RUST_CRAB.try_slice(..).unwrap(), RUST_CRAB);
    assert_eq!(RUST_CRAB.try_slice(0..5).unwrap(), &s[0..5]);
    assert_eq!(RUST_CRAB.try_slice(0..=4).unwrap(), &s[0..=4]);
    assert_eq!(RUST_CRAB.try_slice(..=1).unwrap(), &s[..=1]);
    assert_eq!(RUST_CRAB.try_slice(1..).unwrap(), &s[1..]);
    assert_eq!(
        RUST_CRAB
            .try_slice((Bound::Excluded(0), Bound::Included(1)))
            .unwrap(),
        &s[(Bound::Excluded(0), Bound::Included(1))]
    );
}

#[test]
fn test_from_utf8() {
    let bytes = HipByt::borrowed(b"abc\x80");
    let err = H::from_utf8(bytes.clone()).unwrap_err();
    assert!(ptr::eq(err.as_bytes(), bytes.as_slice()));
    assert_eq!(err.utf8_error().valid_up_to(), 3);
    assert_eq!(format!("{err:?}"), "FromUtf8Error { bytes: [97, 98, 99, 128], error: Utf8Error { valid_up_to: 3, error_len: Some(1) } }");
    assert_eq!(
        format!("{err}"),
        "invalid utf-8 sequence of 1 bytes from index 3"
    );
    assert_eq!(err.clone(), err);
    let bytes_clone = err.into_bytes();
    assert_eq!(bytes_clone.as_ptr(), bytes.as_ptr());
    assert_eq!(bytes_clone.len(), bytes.len());

    let bytes = HipByt::from(b"ABC".repeat(10));
    let string = H::from_utf8(bytes.clone()).unwrap();
    assert_eq!(bytes.as_ptr(), string.as_ptr());
}

#[test]
fn test_from_utf8_lossy() {
    let bytes = HipByt::borrowed(b"abc\x80");
    let string = H::from_utf8_lossy(bytes.clone());
    assert!(string.len() > bytes.len());
    assert_eq!(string, "abc\u{FFFD}");

    let bytes = HipByt::from(b"ABC".repeat(10));
    let string = H::from_utf8_lossy(bytes.clone());
    assert_eq!(bytes.as_ptr(), string.as_ptr());
}

#[test]
fn test_capacity() {
    let a = H::borrowed(ABC);
    assert_eq!(a.capacity(), a.len());

    let a = H::from(ABC);
    assert_eq!(a.capacity(), H::inline_capacity());

    let mut v = String::with_capacity(42);
    for _ in 0..10 {
        v.push_str(ABC);
    }
    let a = H::from(v);
    assert_eq!(a.capacity(), 42);
}

#[test]
fn test_mutate_borrowed() {
    let mut a = H::borrowed(ABC);
    assert!(a.is_borrowed());
    {
        let mut r = a.mutate();
        assert_eq!(r.as_str(), ABC);
        r.push_str("def");
    }
    assert!(!a.is_borrowed());
    assert_eq!(a, "abcdef");
}

#[test]
fn test_mutate_inline() {
    let mut a = H::from(ABC);
    assert!(a.is_inline());
    a.mutate().push_str("def");
    assert_eq!(a, "abcdef");
}

#[test]
fn test_mutate_allocated() {
    {
        // allocated, unique with enough capacity
        let mut v = String::with_capacity(42);
        v.push_str("abcdefghijklmnopqrstuvwxyz");
        let p = v.as_ptr();
        let mut a = H::from(v);
        assert!(a.is_allocated());
        a.mutate().push_str("0123456789");
        assert!(a.is_allocated());
        assert_eq!(a, "abcdefghijklmnopqrstuvwxyz0123456789",);
        assert_eq!(a.as_ptr(), p);
    }

    {
        // allocated, shared
        let mut v = String::with_capacity(42);
        v.push_str("abcdefghijklmnopqrstuvwxyz");
        let mut a = H::from(v);
        assert!(a.is_allocated());
        let b = a.clone();
        a.mutate().push_str("0123456789");
        assert!(a.is_allocated());
        assert_eq!(a, "abcdefghijklmnopqrstuvwxyz0123456789",);
        assert_eq!(b, "abcdefghijklmnopqrstuvwxyz");
        assert_ne!(a.as_ptr(), b.as_ptr());
    }
}

#[test]
fn test_shrink_to_fit() {
    let mut h = H::borrowed(MEDIUM);
    h.shrink_to_fit();
    assert_eq!(h, MEDIUM);
    assert!(core::ptr::eq(h.as_str(), MEDIUM));

    let mut h = H::from(MEDIUM);
    h.truncate(INLINE_CAPACITY);
    h.shrink_to_fit();
    assert!(h.is_inline());
    assert_eq!(h, &MEDIUM[..INLINE_CAPACITY]);

    let mut h = H::from(MEDIUM);
    let h2 = h.clone();
    h.truncate(INLINE_CAPACITY + 1);
    assert_eq!(h.as_ptr(), h2.as_ptr());
    h.shrink_to_fit();
    assert_ne!(h.as_ptr(), h2.as_ptr());
    assert_eq!(h, &MEDIUM[..=INLINE_CAPACITY]);

    let mut h = H::from(&MEDIUM[..INLINE_CAPACITY]);
    assert!(h.is_inline());
    h.shrink_to_fit();
    assert!(h.is_inline());
    assert_eq!(h, &MEDIUM[..INLINE_CAPACITY]);
}

#[test]
fn test_shrink_to() {
    // borrowed no-op
    let mut h = H::borrowed(MEDIUM);
    h.shrink_to(0);
    assert_eq!(h, MEDIUM);
    assert!(core::ptr::eq(h.as_str(), MEDIUM));

    // allocated with capacity < length
    let mut h = H::from(MEDIUM);
    h.shrink_to(0);
    assert_eq!(h, MEDIUM);
    assert!(h.capacity() >= MEDIUM.len());

    // allocated with capacity > actual capacity
    let mut h = H::from(MEDIUM);
    let old_capacity = h.capacity();
    h.shrink_to(1024);
    assert_eq!(h, MEDIUM);
    assert_eq!(h.capacity(), old_capacity);

    // allocated that switches to inline
    let mut h = H::from(MEDIUM);
    h.truncate(INLINE_CAPACITY);
    h.shrink_to(INLINE_CAPACITY);
    assert!(h.is_inline());
    assert_eq!(h, &MEDIUM[..INLINE_CAPACITY]);

    // allocated that reallocates
    let mut h = H::from(MEDIUM);
    let h2 = h.clone();
    h.truncate(INLINE_CAPACITY + 1);
    assert_eq!(h.as_ptr(), h2.as_ptr());
    assert!(h.capacity() >= INLINE_CAPACITY + 2);
    h.shrink_to(INLINE_CAPACITY + 2);
    assert_ne!(h.as_ptr(), h2.as_ptr());
    assert!(h.capacity() >= INLINE_CAPACITY + 2);

    // inline no-op
    let mut h = H::from(&MEDIUM[..INLINE_CAPACITY]);
    assert!(h.is_inline());
    h.truncate(0);
    h.shrink_to(INLINE_CAPACITY / 4);
    assert!(h.is_inline());
    assert_eq!(h.capacity(), INLINE_CAPACITY);
}

#[test]
fn test_truncate() {
    let mut h = H::borrowed(MEDIUM);
    h.truncate(MEDIUM.len() + 1);
    assert_eq!(h, MEDIUM);

    let mut h = H::borrowed(MEDIUM);
    h.truncate(1);
    assert_eq!(h, &MEDIUM[..1]);

    let mut h = H::from(MEDIUM);
    h.truncate(1);
    assert!(h.is_inline());
    assert_eq!(h, &MEDIUM[..1]);

    let mut h = H::from(MEDIUM);
    h.truncate(INLINE_CAPACITY + 1);
    assert!(h.is_allocated());
    assert_eq!(h, &MEDIUM[..=INLINE_CAPACITY]);

    let mut h = H::from(&MEDIUM[..INLINE_CAPACITY]);
    h.truncate(1);
    assert_eq!(h, &MEDIUM[..1]);
}

#[test]
#[should_panic]
fn test_truncate_char_boundary() {
    let mut h = H::borrowed("\u{1F980}");
    h.truncate(1);
}

#[test]
fn test_clear() {
    let mut h = H::borrowed(MEDIUM);
    h.clear();
    assert!(h.is_empty());
    assert!(!h.is_allocated());

    let mut h = H::from(MEDIUM);
    h.clear();
    assert!(h.is_empty());
    assert!(!h.is_allocated());

    let mut h = H::from(&MEDIUM[..INLINE_CAPACITY]);
    h.clear();
    assert!(h.is_empty());
    assert!(!h.is_allocated());
}

#[test]
fn test_pop() {
    let mut h = H::borrowed(MEDIUM);
    assert_eq!(h.pop(), Some('*'));
    assert_eq!(h, &MEDIUM[..MEDIUM.len() - 1]);

    let mut h = H::from(MEDIUM);
    assert_eq!(h.pop(), Some('*'));
    assert_eq!(h, &MEDIUM[..MEDIUM.len() - 1]);

    let mut h = H::from(&MEDIUM[..INLINE_CAPACITY]);
    assert_eq!(h.pop(), Some('*'));
    assert_eq!(h, &MEDIUM[..INLINE_CAPACITY - 1]);

    let mut h = H::from(&MEDIUM[..=INLINE_CAPACITY]);
    assert_eq!(h.pop(), Some('*'));
    assert!(h.is_inline());
    assert_eq!(h, &MEDIUM[..INLINE_CAPACITY]);

    assert_eq!(H::new().pop(), None);
}

#[test]
fn test_push_slice_allocated() {
    // borrowed, not unique
    let mut a = H::borrowed(MEDIUM);
    a.push_str(ABC);
    assert_eq!(&a[0..42], MEDIUM);
    assert_eq!(&a[42..], ABC);

    // allocated, unique
    let mut a = H::from(MEDIUM);
    a.push_str(ABC);
    assert_eq!(&a[0..42], MEDIUM);
    assert_eq!(&a[42..], ABC);

    // allocated, not unique
    let mut a = H::from(MEDIUM);
    let pa = a.as_ptr();
    let b = a.clone();
    assert_eq!(pa, b.as_ptr());
    a.push_str(ABC);
    assert_ne!(a.as_ptr(), pa);
    assert_eq!(&a[0..42], MEDIUM);
    assert_eq!(&a[42..], ABC);
    assert_eq!(b, MEDIUM);

    // allocated, unique but shifted
    let mut a = {
        let x = H::from(MEDIUM);
        x.slice(1..39)
    };
    let p = a.as_ptr();
    a.push_str(ABC);
    assert_eq!(&a[..38], &MEDIUM[1..39]);
    assert_eq!(&a[38..], ABC);
    assert_eq!(a.as_ptr(), p);
    // => the underlying vector is big enough
}

#[test]
fn test_push() {
    // for now, push_char uses push_slice
    // so test can be minimal

    let mut a = H::from(ABC);
    a.push('d');
    assert_eq!(a, "abcd");
    a.push('🦀');
    assert_eq!(a, "abcd🦀");
}

#[test]
fn test_to_owned() {
    let b = ABC;
    let h = H::from(b);
    assert!(h.is_inline());
    let h = h.into_owned();
    assert!(h.is_inline());

    let r = "*".repeat(42);

    let v = r.clone();
    let a = H::borrowed(&v[0..2]);
    let a = a.into_owned();
    drop(v);
    assert_eq!(a, &r[0..2]);

    let a = H::from(&r[..]);
    drop(r);
    let p = a.as_ptr();
    let a = a.into_owned();
    assert_eq!(a.as_ptr(), p);
}

#[test]
fn test_to_case() {
    for (input, a_l, l, a_u, u) in [
        (ABC, ABC, ABC, "ABC", "ABC"),
        ("ὈΔΥΣΣΕΎΣ", "ὈΔΥΣΣΕΎΣ", "ὀδυσσεύς", "ὈΔΥΣΣΕΎΣ", "ὈΔΥΣΣΕΎΣ"),
        ("农历新年", "农历新年", "农历新年", "农历新年", "农历新年"),
    ] {
        let h = H::from(input);
        assert_eq!(h.to_ascii_lowercase(), a_l);
        assert_eq!(h.to_lowercase(), l);
        assert_eq!(h.to_ascii_uppercase(), a_u);
        assert_eq!(h.to_uppercase(), u);
    }
}

#[test]
fn test_make_case() {
    let mut h = H::from("abcDEF");
    let mut h2 = h.clone();
    let h_ref = h.clone();
    h.make_ascii_lowercase();
    assert_eq!(h, "abcdef");
    assert_eq!(h_ref, "abcDEF");

    h2.make_ascii_uppercase();
    assert_eq!(h2, "ABCDEF");
    assert_eq!(h_ref, "abcDEF");
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
fn test_slice_ref_unchecked() {
    let s = Owned::from(ABC);
    let a = H::borrowed(s.as_str());

    unsafe {
        assert_eq!(a.slice_ref_unchecked(&a[0..1]), A);
        assert_eq!(a.slice_ref_unchecked(&a[0..0]), EMPTY_SLICE);
        assert_eq!(a.slice_ref_unchecked(&a[3..3]), EMPTY_SLICE);
    }

    let a = H::from(s.as_str());

    unsafe {
        assert_eq!(a.slice_ref_unchecked(&a[0..1]), A);
        assert_eq!(a.slice_ref_unchecked(&a[0..0]), EMPTY_SLICE);
        assert_eq!(a.slice_ref_unchecked(&a[3..3]), EMPTY_SLICE);
    }

    let s = "*".repeat(42);
    let a = H::from(s);

    unsafe {
        assert_eq!(a.slice_ref_unchecked(&a[0..1]), "*");
        assert_eq!(a.slice_ref_unchecked(&a[0..41]).as_ptr(), a.as_ptr());
        assert_eq!(a.slice_ref_unchecked(&a[0..0]), EMPTY_SLICE);
        assert_eq!(a.slice_ref_unchecked(&a[3..3]), EMPTY_SLICE);
    }
}

#[test]
fn test_try_slice_ref() {
    let s = Owned::from(ABC);
    let a = H::borrowed(s.as_str());

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
    let a = H::borrowed(s.as_str());
    assert_eq!(a.slice_ref(&a[0..1]), A);
    assert_eq!(a.slice_ref(&a[0..0]), EMPTY_SLICE);
    assert_eq!(a.slice_ref(&a[3..3]), EMPTY_SLICE);
}

#[test]
#[should_panic]
fn test_slice_ref_panic() {
    let s = Owned::from(ABC);
    let a = H::borrowed(s.as_str());
    let _ = a.slice_ref(ABC);
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

    let slices: &[S] = &[A, B, C];
    let h = H::concat(slices);
    assert_eq!(h, ABC);
    assert!(h.is_inline());

    let long = MEDIUM.to_owned();
    let slices: &[String] = &[A.into(), B.into(), C.into(), long.clone()];
    let h = H::concat(slices);
    assert_eq!(h, [ABC, long.as_str()].concat());
    assert!(h.is_allocated());
}

#[test]
#[should_panic]
fn test_concat_bad_iter() {
    #[derive(Clone)]
    struct I(Option<Rc<Cell<&'static str>>>);

    impl Iterator for I {
        type Item = &'static str;
        fn next(&mut self) -> Option<Self::Item> {
            self.0.take().map(|x| x.replace("longer"))
        }
    }

    let _h = H::concat(I(Some(Rc::new(Cell::new("long")))));
}

#[test]
fn test_join_slices() {
    let h = H::join_slices(&[], ",");
    assert!(h.is_empty());

    let h = H::join_slices(&[EMPTY_SLICE, EMPTY_SLICE], EMPTY_SLICE);
    assert!(h.is_empty());

    let slices: &[S] = &[A, B, C];
    let h = H::join_slices(slices, ",");
    assert_eq!(h, "a,b,c");
    assert!(h.is_inline());

    let long = "*".repeat(42);
    let slices: &[S] = &[A, B, C, &long];
    let h = H::join_slices(slices, ",");
    assert_eq!(h, slices.join(","));
    assert!(h.is_allocated());
}

#[test]
fn test_join() {
    let slices: &[S] = &[];
    let h = H::join(slices, ",");
    assert!(h.is_empty());

    let slices: &[S] = &[A, B, C];
    let h = H::join(slices, ",");
    assert_eq!(h, "a,b,c");
    assert!(h.is_inline());

    let long = "*".repeat(42);
    let slices: &[String] = &[A.into(), B.into(), C.into(), long.clone()];
    let h = H::join(slices, ",");
    assert_eq!(h, ["a,b,c,", long.as_str()].concat());
    assert!(h.is_allocated());
}

#[test]
#[should_panic]
fn test_join_bad_iter() {
    #[derive(Clone)]
    struct I(Option<Rc<Cell<&'static str>>>);

    impl Iterator for I {
        type Item = &'static str;
        fn next(&mut self) -> Option<Self::Item> {
            self.0.take().map(|x| x.replace("longer"))
        }
    }

    let _h = H::join(I(Some(Rc::new(Cell::new("long")))), ",");
}

#[test]
#[should_panic]
fn test_join_bad_iter2() {
    #[derive(Clone)]
    struct I(alloc::vec::IntoIter<Rc<Cell<&'static str>>>);

    impl Iterator for I {
        type Item = &'static str;
        fn next(&mut self) -> Option<Self::Item> {
            self.0.next().map(|x| x.replace("ab"))
        }
    }

    let _h = H::join(
        I(vec![Rc::new(Cell::new("ab")), Rc::new(Cell::new(B))].into_iter()),
        ",".to_string(),
    );
}

#[inline]
#[track_caller]
fn value_eq<'a>(computed: H<'a>, expected: &'a str) {
    assert!(
        core::ptr::eq(computed.as_str(), expected),
        "{computed:?} and {expected:?} are not the same"
    );
}

#[inline]
#[track_caller]
fn option_eq<'a>(computed: Option<H<'a>>, expected: Option<&'a str>) {
    match (computed, expected) {
        (None, None) => (),
        (None, Some(e)) => panic!("expected value {e:?}, got none"),
        (Some(c), None) => panic!("expected none, got {c:?}"),
        (Some(c), Some(e)) => value_eq(c, e),
    }
}

#[inline]
#[track_caller]
fn iter_eq_bidir<'a>(
    computed: impl DoubleEndedIterator<Item = H<'a>> + Clone,
    expected: impl DoubleEndedIterator<Item = &'a str> + Clone,
) {
    iter_eq(computed.clone(), expected.clone());
    iter_eq(computed.rev(), expected.rev());
}
#[inline]
#[track_caller]
fn iter_eq<'a>(
    mut computed: impl Iterator<Item = H<'a>>,
    mut expected: impl Iterator<Item = &'a str>,
) {
    loop {
        match (computed.next(), expected.next()) {
            (Some(c), Some(e)) => value_eq(c, e),
            (None, None) => break,
            (_, _) => panic!("non matching iterator"),
        }
    }
}

#[inline]
#[track_caller]
fn pair_eq<'a>(computed: Option<(H<'a>, H<'a>)>, expected: Option<(&'a str, &'a str)>) {
    match (computed, expected) {
        (Some((c1, c2)), Some((e1, e2))) => {
            value_eq(c1, e1);
            value_eq(c2, e2);
        }
        (None, None) => (),
        (_, _) => panic!("non matching iterator"),
    }
}

#[test]
fn test_whitespace() {
    // test only with borrowed string

    let source = " \r\n a\t\n";
    let h = H::borrowed(source);
    value_eq(h.trim(), source.trim());
    value_eq(h.trim_start(), source.trim_start());
    value_eq(h.trim_end(), source.trim_end());
    iter_eq_bidir(h.split_whitespace(), source.split_whitespace());
    iter_eq_bidir(h.split_ascii_whitespace(), source.split_ascii_whitespace());
    iter_eq_bidir(h.lines(), source.lines());

    let source = ABC;
    let h = H::borrowed(source);
    value_eq(h.trim(), source.trim());
    value_eq(h.trim_start(), source.trim_start());
    value_eq(h.trim_end(), source.trim_end());
    iter_eq_bidir(h.split_whitespace(), source.split_whitespace());
    iter_eq_bidir(h.split_ascii_whitespace(), source.split_ascii_whitespace());
    iter_eq_bidir(h.lines(), source.lines());
}

#[test]
fn test_pattern() {
    // test only on borrowed string  to check the slice reuse easily
    // compare the resulting iterator to the iterator obtained on str

    macro_rules! test_method {
        (>< $name:ident  $( ( $p:tt ) )? $test:ident) => {{
            let source = ":a:b:c:";
            let hip = H::borrowed(source);
            $test(hip.$name($( $p , )? ':'), source.$name($( $p , )? ':'));
            $test(hip.$name($( $p , )? '.'), source.$name($( $p , )? '.'));
            $test(hip.$name($( $p , )? [':'].as_slice()), source.$name($( $p , )? [':'].as_slice()));
            $test(hip.$name($( $p , )? |c| c == ':'), source.$name($( $p , )? |c| c == ':'));
        }};
        ($name:ident  $( ( $p:tt ) )? $test:ident) => {{
            let source = ":a:b:c:";
            let hip = H::borrowed(source);
            $test(hip.$name($( $p , )? ":"), source.$name($( $p , )? ":"));
            $test(hip.$name($( $p , )? "."), source.$name($( $p , )? "."));
            $test(hip.$name($( $p , )? ':'), source.$name($( $p , )? ':'));
            $test(hip.$name($( $p , )? &[':']), source.$name($( $p , )? &[':']));
            $test(hip.$name($( $p , )? [':'].as_slice()), source.$name($( $p , )? [':'].as_slice()));
            $test(hip.$name($( $p , )? |c| c == ':'), source.$name($( $p , )? |c| c == ':'));
        }};
    }

    test_method!(split iter_eq);
    test_method!(>< split iter_eq_bidir);
    test_method!(split_inclusive iter_eq);
    test_method!(>< split_inclusive iter_eq_bidir);
    test_method!(rsplit iter_eq);
    test_method!(>< rsplit iter_eq_bidir);
    test_method!(split_terminator iter_eq);
    test_method!(>< split_terminator iter_eq_bidir);
    test_method!(rsplit_terminator iter_eq);
    test_method!(>< rsplit_terminator iter_eq_bidir);
    test_method!(splitn(1) iter_eq);
    test_method!(rsplitn(2) iter_eq);
    test_method!(split_once pair_eq);
    test_method!(rsplit_once pair_eq);
    test_method!(matches iter_eq);
    test_method!(>< matches iter_eq_bidir);
    test_method!(rmatches iter_eq);
    test_method!(>< rmatches iter_eq_bidir);

    {
        let source = ":a:b:c:";
        let hip = H::borrowed(source);
        iter_eq(hip.match_indices(":").map(|(_, v)| v), source.matches(":"));
        iter_eq(hip.match_indices(".").map(|(_, v)| v), source.matches("."));
        iter_eq_bidir(hip.match_indices(':').map(|(_, v)| v), source.matches(':'));
        iter_eq_bidir(hip.match_indices('.').map(|(_, v)| v), source.matches('.'));
        iter_eq(
            hip.match_indices(&[':']).map(|(_, v)| v),
            source.matches(&[':']),
        );
        iter_eq_bidir(
            hip.match_indices([':'].as_slice()).map(|(_, v)| v),
            source.matches([':'].as_slice()),
        );
        iter_eq_bidir(
            hip.match_indices(|c| c == ':').map(|(_, v)| v),
            source.matches(|c| c == ':'),
        );
    };

    {
        let source = ":a:b:c:";
        let hip = H::borrowed(source);
        iter_eq(
            hip.rmatch_indices(":").map(|(_, v)| v),
            source.rmatches(":"),
        );
        iter_eq(
            hip.rmatch_indices(".").map(|(_, v)| v),
            source.rmatches("."),
        );
        iter_eq_bidir(
            hip.rmatch_indices(':').map(|(_, v)| v),
            source.rmatches(':'),
        );
        iter_eq_bidir(
            hip.rmatch_indices('.').map(|(_, v)| v),
            source.rmatches('.'),
        );
        iter_eq(
            hip.rmatch_indices(&[':']).map(|(_, v)| v),
            source.rmatches(&[':']),
        );
        iter_eq_bidir(
            hip.rmatch_indices([':'].as_slice()).map(|(_, v)| v),
            source.rmatches([':'].as_slice()),
        );
        #[allow(clippy::manual_pattern_char_comparison)]
        iter_eq_bidir(
            hip.rmatch_indices(|c| c == ':').map(|(_, v)| v),
            source.rmatches(|c| c == ':'),
        );
    };

    test_method!(trim_start_matches value_eq);
    test_method!(trim_end_matches value_eq);
    test_method!(>< trim_matches value_eq);

    test_method!(strip_prefix option_eq);
    test_method!(strip_suffix option_eq);
}

#[test]
fn test_into_bytes() {
    let s = H::from("A".repeat(42));
    let bytes = s.into_bytes();
    assert_eq!(bytes.len(), 42);
    assert_eq!(bytes.as_slice(), [b'A'; 42]);
}

#[test]
fn test_from_utf16() {
    let v = [u16::from(b'a')].repeat(42);
    assert_eq!(H::from_utf16(&v[0..4]).unwrap(), A.repeat(4));
    assert_eq!(H::from_utf16(&v).unwrap(), A.repeat(42));
    assert!(H::from_utf16(&[0xD834]).is_err());
}

#[test]
fn test_from_utf16_lossy() {
    let v = [u16::from(b'a')].repeat(42);
    assert_eq!(H::from_utf16_lossy(&v[0..4]), A.repeat(4));
    assert_eq!(H::from_utf16_lossy(&v), A.repeat(42));
    assert_eq!(H::from_utf16_lossy(&[0xD834]), "\u{FFFD}");
}
