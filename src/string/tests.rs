use core::ops::Bound;
use core::ptr;
#[cfg(feature = "std")]
use std::collections::HashSet;

use super::SliceErrorKind;
use crate::alloc::format;
use crate::alloc::string::{String, ToString};
use crate::{HipByt, HipStr};

const INLINE_CAPACITY: usize = HipStr::inline_capacity();

#[test]
fn test_new_default() {
    let new = HipStr::new();
    assert_eq!(new, "");
    assert!(new.is_empty());

    let new = HipStr::default();
    assert_eq!(new, "");
    assert!(new.is_empty());
}

#[test]
#[cfg(feature = "std")]
fn test_borrow_and_hash() {
    let mut set = HashSet::new();
    set.insert(HipStr::from("a"));
    set.insert(HipStr::from("b"));

    assert!(set.contains("a"));
    assert!(!set.contains("c"));
}

#[test]
fn test_fmt() {
    let source = "Rust \u{1F980}";
    let a = HipStr::borrowed(source);
    assert_eq!(format!("{}", a), source);
    assert_eq!(format!("{:?}", a), format!("{:?}", source),);
}

#[test]
fn test_from_string() {
    let s = "A".repeat(42);
    let hs = HipStr::from(s.clone());
    assert!(!hs.is_borrowed());
    assert!(!hs.is_inline());
    assert!(hs.is_allocated());
    assert_eq!(hs.len(), 42);
    assert_eq!(hs.as_str(), s.as_str());
}

#[test]
fn test_borrowed() {
    let s = "0123456789";
    let string = HipStr::borrowed(s);
    assert!(string.is_borrowed());
    assert!(!string.is_inline());
    assert_eq!(string.len(), s.len());
    assert_eq!(string.as_str(), s);
    assert_eq!(string.as_ptr(), s.as_ptr());
}

#[test]
fn test_from_static() {
    fn is_static_type<T: 'static>(_: &T) {}

    let s = "abcdefghijklmnopqrstuvwxyz";
    let string = HipStr::from_static(s);

    // compiler check
    is_static_type(&string);

    assert!(string.is_borrowed());
    assert!(!string.is_inline());
    assert!(!string.is_allocated());
    assert_eq!(string.len(), s.len());
    assert_eq!(string.as_str(), s);
    assert_eq!(string.as_ptr(), s.as_ptr());
}

#[test]
fn test_from_slice() {
    static V: &[u8] = &[b'a'; 1024];
    let s = core::str::from_utf8(V).unwrap();

    for size in [0, 1, INLINE_CAPACITY, INLINE_CAPACITY + 1, 256, 1024] {
        let string = HipStr::from(&s[..size]);
        assert_eq!(size <= INLINE_CAPACITY, string.is_inline());
        assert_eq!(size > INLINE_CAPACITY, string.is_allocated());
        assert_eq!(string.len(), size);
    }
}

#[test]
fn test_as_slice() {
    // static
    {
        let a = HipStr::borrowed("abc");
        assert!(a.is_borrowed());
        assert!(!a.is_inline());
        assert!(!a.is_allocated());
        assert_eq!(a.as_str(), "abc");
    }
    // inline
    {
        let a = HipStr::from("abc");
        assert!(!a.is_borrowed());
        assert!(a.is_inline());
        assert!(!a.is_allocated());
        assert_eq!(a.as_str(), "abc");
    }
    // allocated
    {
        let s = "A".repeat(42);
        let a = HipStr::from(s.as_str());
        assert!(!a.is_borrowed());
        assert!(!a.is_inline());
        assert!(a.is_allocated());
        assert_eq!(a.as_str(), s.as_str());
    }
}

#[test]
fn test_clone() {
    // static
    {
        let s: &'static str = "abc";
        let a = HipStr::borrowed(s);
        assert!(a.is_borrowed());
        let b = a.clone();
        drop(a);
        assert_eq!(b.as_str(), "abc");
        assert_eq!(s.as_ptr(), b.as_ptr());
    }

    // inline
    {
        let a = HipStr::from("abc");
        assert!(a.is_inline());
        let b = a.clone();
        drop(a);
        assert_eq!(b.as_str(), "abc");
    }

    // allocated
    {
        let s = "a".repeat(42);
        let p = s.as_ptr();
        let a = HipStr::from(s);
        assert!(a.is_allocated());
        let b = a.clone();
        drop(a);
        assert_eq!(b.as_str(), "a".repeat(42).as_str());
        assert_eq!(b.as_ptr(), p);
    }
}

#[test]
fn test_into_static() {
    // static
    let a = HipStr::borrowed("abc");
    assert_eq!(a.into_borrowed(), Ok("abc"));

    // inline
    let a = HipStr::from("abc");
    let b = a.clone();
    assert_eq!(a.into_borrowed(), Err(b));

    // heap
    let a = HipStr::from("a".repeat(42).as_str());
    let b = a.clone();
    assert_eq!(a.into_borrowed(), Err(b));
}

#[test]
fn test_into_bytes() {
    let s = HipStr::from("A".repeat(42));
    let bytes = s.into_bytes();
    assert_eq!(bytes.len(), 42);
    assert_eq!(bytes.as_slice(), [b'A'; 42]);
}

#[test]
fn test_as_mut_str() {
    // static
    let mut a = HipStr::borrowed("abc");
    assert_eq!(a.as_mut_str(), None);

    // inline
    let mut a = HipStr::from("abc");
    assert!(a.is_inline());
    assert_eq!(a.as_mut_str(), Some(String::from("abc").as_mut_str()));

    // heap
    let mut a = HipStr::from("a".repeat(42).as_str());
    {
        let sl = a.as_mut_str();
        assert_eq!(sl, Some("a".repeat(42).as_mut_str()));
        unsafe {
            sl.unwrap().as_bytes_mut()[0] = b'b';
        }
    }
    let mut b = a.clone();
    assert!(b.starts_with("b"));
    assert_eq!(b.as_mut_str(), None);
    let _ = a.as_str();
}

#[test]
fn test_to_mut_str() {
    {
        // static
        let mut a = HipStr::borrowed("abc");
        assert!(a.is_borrowed());
        assert_eq!(a.to_mut_str(), "abc".to_string().as_mut_str());
        assert!(a.is_inline());
    }

    {
        // inline
        let mut a = HipStr::from("abc");
        assert!(a.is_inline());
        assert_eq!(a.to_mut_str(), "abc".to_string().as_mut_str());
        assert!(a.is_inline());
    }

    {
        // heap
        let mut a = HipStr::from("a".repeat(42).as_str());
        assert!(a.is_allocated());
        {
            let sl = a.to_mut_str();
            assert_eq!(sl, "a".repeat(42).as_mut_str());
            sl.make_ascii_uppercase();
        }

        let mut b = a.clone();
        assert_eq!(b, "A".repeat(42));
        let _ = b.to_mut_str();
        assert_ne!(b.as_ptr(), a.as_ptr());
        assert!(b.is_allocated());
    }
}

#[test]
fn test_slice_inline() {
    let v = "a".repeat(INLINE_CAPACITY);
    let s = HipStr::from(&v[..]);
    let sl = s.slice(0..10);
    assert_eq!(&sl, &v[0..10]);
}

#[test]
fn test_slice_borrowed() {
    let v = "a".repeat(42);
    let s = HipStr::borrowed(&v);

    let sl1 = s.slice(4..30);
    assert_eq!(&sl1, &v[4..30]);
    assert_eq!(sl1.as_ptr(), s[4..30].as_ptr());

    let p = s[9..12].as_ptr();
    drop(s);

    let sl2 = sl1.slice(5..8);
    drop(sl1);
    assert_eq!(&sl2, &v[9..12]);
    assert_eq!(sl2.as_ptr(), p);
}

#[test]
fn test_slice_allocated() {
    let v = "a".repeat(42);
    let s = HipStr::from(&v[..]);
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
    let a = HipStr::borrowed("abc");
    let _b = a.slice(4..=4);
}

#[test]
#[should_panic]
fn test_slice_panic_end() {
    let a = HipStr::borrowed("abc");
    let _b = a.slice(0..5);
}

#[test]
#[should_panic]
fn test_slice_panic_mixed() {
    let a = HipStr::borrowed("abc");
    let _b = a.slice(3..2);
}

#[test]
#[should_panic]
fn test_slice_panic_start_char_boundary() {
    let a = HipStr::borrowed("\u{1F980}");
    let _b = a.slice(1..);
}

#[test]
#[should_panic]
fn test_slice_panic_end_char_boundary() {
    let a = HipStr::borrowed("\u{1F980}");
    let _b = a.slice(0..2);
}

static RUST_CRAB: HipStr = HipStr::borrowed("Rust \u{1F980}");

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
    let err = HipStr::from_utf8(bytes.clone()).unwrap_err();
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

    let bytes = HipByt::from(b"abc".repeat(10));
    let string = HipStr::from_utf8(bytes.clone()).unwrap();
    assert_eq!(bytes.as_ptr(), string.as_ptr());
}

#[test]
fn test_from_utf8_lossy() {
    let bytes = HipByt::borrowed(b"abc\x80");
    let string = HipStr::from_utf8_lossy(bytes.clone());
    assert!(string.len() > bytes.len());
    assert_eq!(string, "abc\u{FFFD}");

    let bytes = HipByt::from(b"abc".repeat(10));
    let string = HipStr::from_utf8_lossy(bytes.clone());
    assert_eq!(bytes.as_ptr(), string.as_ptr());
}

#[test]
fn test_capacity() {
    let a = HipStr::borrowed("abc");
    assert_eq!(a.capacity(), a.len());

    let a = HipStr::from("abc");
    assert_eq!(a.capacity(), HipStr::inline_capacity());

    let mut v = String::with_capacity(42);
    for _ in 0..10 {
        v.push_str("abc");
    }
    let a = HipStr::from(v);
    assert_eq!(a.capacity(), 42);
}

#[test]
fn test_mutate_borrowed() {
    let mut a = HipStr::borrowed("abc");
    assert!(a.is_borrowed());
    {
        let mut r = a.mutate();
        assert_eq!(r.as_str(), "abc");
        r.push_str("def");
    }
    assert!(!a.is_borrowed());
    assert_eq!(a, "abcdef");
}

#[test]
fn test_mutate_inline() {
    let mut a = HipStr::from("abc");
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
        let mut a = HipStr::from(v);
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
        let mut a = HipStr::from(v);
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
fn test_from_utf16() {
    let v = [b'a' as u16].repeat(42);
    assert_eq!(HipStr::from_utf16(&v[0..4]).unwrap(), "a".repeat(4));
    assert_eq!(HipStr::from_utf16(&v).unwrap(), "a".repeat(42));
    assert!(HipStr::from_utf16(&[0xD834]).is_err());
}

#[test]
fn test_from_utf16_lossy() {
    let v = [b'a' as u16].repeat(42);
    assert_eq!(HipStr::from_utf16_lossy(&v[0..4]), "a".repeat(4));
    assert_eq!(HipStr::from_utf16_lossy(&v), "a".repeat(42));
    assert_eq!(HipStr::from_utf16_lossy(&[0xD834]), "\u{FFFD}");
}

const FORTY_TWOS: &str = unsafe { core::str::from_utf8_unchecked(&[42; 42]) };

#[test]
fn test_push_slice_allocated() {
    // borrowed, not unique
    let mut a = HipStr::borrowed(FORTY_TWOS);
    a.push_str("abc");
    assert_eq!(&a[0..42], FORTY_TWOS);
    assert_eq!(&a[42..], "abc");

    // allocated, unique
    let mut a = HipStr::from(FORTY_TWOS);
    a.push_str("abc");
    assert_eq!(&a[0..42], FORTY_TWOS);
    assert_eq!(&a[42..], "abc");

    // allocated, not unique
    let mut a = HipStr::from(FORTY_TWOS);
    let pa = a.as_ptr();
    let b = a.clone();
    assert_eq!(pa, b.as_ptr());
    a.push_str("abc");
    assert_ne!(a.as_ptr(), pa);
    assert_eq!(&a[0..42], FORTY_TWOS);
    assert_eq!(&a[42..], "abc");
    assert_eq!(b, FORTY_TWOS);

    // allocated, unique but shifted
    let mut a = {
        let x = HipStr::from(FORTY_TWOS);
        x.slice(1..39)
    };
    let p = a.as_ptr();
    a.push_str("abc");
    assert_eq!(&a[..38], &FORTY_TWOS[1..39]);
    assert_eq!(&a[38..], "abc");
    assert_eq!(a.as_ptr(), p);
    // => the underlying vector is big enough
}

#[test]
fn test_push() {
    // for now, push_char uses push_slice
    // so test can be minimal

    let mut a = HipStr::from("abc");
    a.push('d');
    assert_eq!(a, "abcd");
    a.push('🦀');
    assert_eq!(a, "abcd🦀");
}

#[test]
fn test_to_owned() {
    let b = "abc";
    let h = HipStr::from(b);
    assert!(h.is_inline());
    let h = h.into_owned();
    assert!(h.is_inline());

    let r = "*".repeat(42);

    let v = r.clone();
    let a = HipStr::borrowed(&v[0..2]);
    let a = a.into_owned();
    drop(v);
    assert_eq!(a, &r[0..2]);

    let v = r.clone();
    let a = HipStr::from(&v[..]);
    drop(v);
    let p = a.as_ptr();
    let a = a.into_owned();
    assert_eq!(a.as_ptr(), p);
}

#[test]
fn test_to_case() {
    for (input, a_l, l, a_u, u) in [
        ("abc", "abc", "abc", "ABC", "ABC"),
        ("ὈΔΥΣΣΕΎΣ", "ὈΔΥΣΣΕΎΣ", "ὀδυσσεύς", "ὈΔΥΣΣΕΎΣ", "ὈΔΥΣΣΕΎΣ"),
        ("农历新年", "农历新年", "农历新年", "农历新年", "农历新年"),
    ] {
        let h = HipStr::from(input);
        assert_eq!(h.to_ascii_lowercase(), a_l);
        assert_eq!(h.to_lowercase(), l);
        assert_eq!(h.to_ascii_uppercase(), a_u);
        assert_eq!(h.to_uppercase(), u);
    }
}

#[test]
fn test_make_case() {
    let mut h = HipStr::from("abcDEF");
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
    let h = HipStr::new();
    let h50 = h.repeat(50);
    assert_eq!(h50.len(), 0);
    assert!(!h50.is_allocated());

    let h = HipStr::from("*".repeat(42));
    let h1 = h.repeat(1);
    assert_eq!(h1.len(), h.len());
    assert_eq!(h.as_ptr(), h1.as_ptr());

    let h = HipStr::from("abc");
    let h4 = h.repeat(2);
    assert_eq!(h4, "abc".repeat(2));
    assert!(h4.is_inline());

    assert_eq!(h.repeat(50), "abc".repeat(50));
}

#[test]
fn test_slice_ref_unchecked() {
    let s = String::from("abc");
    let a = HipStr::borrowed(s.as_str());

    unsafe {
        assert_eq!(a.slice_ref_unchecked(&a[0..1]), "a");
        assert_eq!(a.slice_ref_unchecked(&a[0..0]), "");
        assert_eq!(a.slice_ref_unchecked(&a[3..3]), "");
    }

    let a = HipStr::from(s.as_str());

    unsafe {
        assert_eq!(a.slice_ref_unchecked(&a[0..1]), "a");
        assert_eq!(a.slice_ref_unchecked(&a[0..0]), "");
        assert_eq!(a.slice_ref_unchecked(&a[3..3]), "");
    }

    let s = "*".repeat(42);
    let a = HipStr::from(s);

    unsafe {
        assert_eq!(a.slice_ref_unchecked(&a[0..1]), "*");
        assert_eq!(a.slice_ref_unchecked(&a[0..41]).as_ptr(), a.as_ptr());
        assert_eq!(a.slice_ref_unchecked(&a[0..0]), "");
        assert_eq!(a.slice_ref_unchecked(&a[3..3]), "");
    }
}

#[test]
fn test_try_slice_ref() {
    let s = String::from("abc");
    let a = HipStr::borrowed(s.as_str());

    assert_eq!(a.try_slice_ref(&a[0..1]).unwrap(), "a");
    assert_eq!(a.try_slice_ref(&a[0..0]).unwrap(), "");
    assert_eq!(a.try_slice_ref(&a[3..3]).unwrap(), "");

    assert!(a.try_slice_ref("abc").is_none());
    assert!(a.try_slice_ref("").is_none());

    let b = HipStr::borrowed(&s[0..2]);
    assert!(b.try_slice_ref(&s[1..3]).is_none());
}

#[test]
fn test_slice_ref() {
    let s = String::from("abc");
    let a = HipStr::borrowed(s.as_str());
    assert_eq!(a.slice_ref(&a[0..1]), "a");
    assert_eq!(a.slice_ref(&a[0..0]), "");
    assert_eq!(a.slice_ref(&a[3..3]), "");
}

#[test]
#[should_panic]
fn test_slice_ref_panic() {
    let s = String::from("abc");
    let a = HipStr::borrowed(s.as_str());
    let _ = a.slice_ref("abc");
}
