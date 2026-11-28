//! `Hip::convert` and `Hip::try_convert`: every representation and backend,
//! every kind of value; contents always, buffer reuse where documented.

use alloc::string::String;
use alloc::vec::Vec;

use crate::backend::{Arc, Rc, Unique};
use crate::bytes::{HipByt, SmallByt, TinyByt};
use crate::{HipCStr, HipStr, SmallStr, TinyCStr, TinyStr};

const LONG: &[u8] = b"0123456789abcdefghijklmnopqrstuvwxyzABCDEFGH"; // 44 bytes

type W = HipByt<'static, Arc>;
type S = SmallByt<'static, Arc>;
type T = TinyByt<Arc>;

/// Converts to the three representations of the same backend, checking the
/// contents; returns the data pointers of the results.
fn to_all<'a, R: crate::repr::Repr<'a, Backend = Arc>>(
    make: impl Fn() -> crate::Hip<crate::enc::Bytes, R>,
) -> [*const u8; 3] {
    let expected = make().bytes().to_vec();
    let w: HipByt<'a, Arc> = make().convert();
    let s: SmallByt<'a, Arc> = make().convert();
    let t: T = make().convert();
    assert_eq!(w.as_slice(), expected);
    assert_eq!(s.as_slice(), expected);
    assert_eq!(t.as_slice(), expected);
    [w.as_ptr(), s.as_ptr(), t.as_ptr()]
}

#[test]
fn inline_stays_inline() {
    let s: S = W::from(&b"abc"[..]).convert();
    let t: T = W::from(&b"abc"[..]).convert();
    let w: W = T::from(&b"abc"[..]).convert();
    assert!(s.is_inline() && t.is_inline() && w.is_inline());
    // a 15-byte inline 3-word value does not fit 1 word: heap
    let t: T = W::from(&LONG[..15]).convert();
    assert!(t.is_allocated());
    assert_eq!(t.as_slice(), &LONG[..15]);
}

#[test]
fn borrowed_kept_where_possible() {
    let w = W::borrowed(LONG);
    let s: S = w.clone().convert();
    assert!(s.is_borrowed());
    assert_eq!(s.as_ptr(), LONG.as_ptr());
    let back: W = s.convert();
    assert!(back.is_borrowed());
    assert_eq!(back.as_ptr(), LONG.as_ptr());
    let t: T = w.convert();
    assert!(t.is_allocated(), "a 1-word value never borrows");
    assert_eq!(t.as_slice(), LONG);
}

#[test]
fn thin_buffer_kept_everywhere() {
    for shared in [false, true] {
        let src = W::from(LONG);
        // a shared buffer is handed over too (one more reference)
        let keep = shared.then(|| src.clone());
        let p = src.as_ptr();
        let s: S = src.clone().convert();
        let t: T = src.convert();
        assert_eq!((s.as_ptr(), t.as_ptr()), (p, p));
        let w: W = t.convert();
        assert_eq!(w.as_ptr(), p);
        let w2: W = s.convert();
        assert_eq!(w2.as_ptr(), p);
        assert_eq!(w2.as_slice(), LONG);
        drop(keep);
    }
}

#[test]
fn small_and_tiny_round_trips() {
    let s = S::from(LONG);
    let p = s.as_ptr();
    let t: T = s.convert();
    assert_eq!(t.as_ptr(), p);
    let s: S = t.convert();
    assert_eq!(s.as_ptr(), p);
    assert_eq!(s.as_slice(), LONG);
}

#[test]
fn wide_prefix_views() {
    // unique: everyone keeps the buffer (1 word truncates it in place)
    let w = W::from(LONG).slice(0..30);
    let p = w.as_ptr();
    let [pw, ps, pt] = to_all(|| w.clone());
    assert_eq!((pw, ps), (p, p));
    // `w` itself is alive in the closure's captures: the 1-word target copies
    assert_ne!(pt, p);
    let t: T = w.convert();
    assert_eq!(t.as_ptr(), p, "unique prefix: truncated in place");
    assert_eq!(t.as_slice(), &LONG[..30]);
}

#[test]
fn wide_offset_views() {
    let base = W::from(LONG);
    let start = base.as_ptr();
    let w = base.slice(5..35);
    drop(base);
    // unique with an offset: moved to the start of the buffer, kept
    let s: S = w.clone().convert();
    // `w` still shares the buffer: copied
    assert_ne!(s.as_ptr(), start);
    assert_eq!(s.as_slice(), &LONG[5..35]);
    let t: T = w.convert();
    assert_eq!(t.as_ptr(), start, "unique: compacted in place");
    assert_eq!(t.as_slice(), &LONG[5..35]);
    let w = W::from(LONG).slice(5..35);
    let s: S = w.convert();
    assert_eq!(s.as_slice(), &LONG[5..35]);
}

#[test]
fn adopted_vectors() {
    let w = W::from(LONG.to_vec());
    let p = w.as_ptr();
    let again: W = w.clone().convert();
    assert_eq!(again.as_ptr(), p);
    drop(again);
    // the 2- and 1-word types do not adopt vectors
    let s: S = w.clone().convert();
    assert_ne!(s.as_ptr(), p);
    let t: T = w.convert();
    assert_ne!(t.as_ptr(), p);
    assert_eq!((s.as_slice(), t.as_slice()), (LONG, LONG));
}

#[test]
fn small_heap_prefix_to_tiny() {
    let mut s = S::from(LONG);
    s.truncate(30);
    let p = s.as_ptr();
    let kept = s.clone();
    let t: T = s.convert();
    assert_ne!(t.as_ptr(), p, "shared prefix: copied");
    assert_eq!(t.as_slice(), &LONG[..30]);
    let t: T = kept.convert();
    assert_eq!(t.as_ptr(), p, "unique prefix: truncated in place");
    assert_eq!(t.as_slice(), &LONG[..30]);
}

#[test]
fn backends() {
    // unique buffers change backend in place
    let w = W::from(LONG);
    let p = w.as_ptr();
    let local: HipByt<'static, Rc> = w.convert();
    assert_eq!(local.as_ptr(), p);
    let unique: TinyByt<Unique> = local.convert();
    assert_eq!(unique.as_ptr(), p);
    let back: SmallByt<'static, Arc> = unique.convert();
    assert_eq!(back.as_ptr(), p);
    assert_eq!(back.as_slice(), LONG);

    // shared buffers are copied, both values stay valid
    let w = W::from(LONG);
    let keep = w.clone();
    let local: HipByt<'static, Rc> = w.convert();
    assert_ne!(local.as_ptr(), keep.as_ptr());
    assert_eq!(local.as_slice(), keep.as_slice());
    drop(keep);

    // adopted vectors too
    let w = W::from(LONG.to_vec());
    let p = w.as_ptr();
    let local: HipByt<'static, Rc> = w.convert();
    assert_eq!(local.as_ptr(), p);
    let vec = local.into_vec();
    assert_eq!(vec.as_ptr(), p, "still the adopted vector");

    // borrowed and inline values
    let b: SmallByt<'static, Rc> = W::borrowed(LONG).convert();
    assert!(b.is_borrowed());
    let i: TinyByt<Rc> = W::from(&b"ab"[..]).convert();
    assert!(i.is_inline());
}

#[test]
fn families() {
    // same bytes, same buffer
    let s = HipStr::from(String::from_utf8(LONG.to_vec()).unwrap());
    let p = s.as_ptr();
    let b: HipByt<'static, Arc> = s.convert();
    assert_eq!(b.as_ptr(), p);
    let s: SmallStr = b.try_convert().unwrap();
    assert_ne!(s.as_ptr(), p, "a 2-word value does not adopt the vector");
    let p = s.as_ptr();
    let t: TinyStr = s.convert();
    assert_eq!(t.as_ptr(), p);

    // validation gives the value back
    let bad = W::from(&b"ok\xff"[..]);
    let error = bad.try_convert::<crate::enc::Utf8, crate::repr::Small<'static, Arc>>();
    let error = error.unwrap_err();
    assert_eq!(error.reason().valid_up_to(), 2);
    assert_eq!(error.into_source().as_slice(), b"ok\xff");
}

#[test]
fn c_strings() {
    // dropping the NUL: a shorter view, no copy
    let c = HipCStr::try_from(LONG).unwrap();
    let p = c.as_ptr();
    let b: HipByt<'static, Arc> = c.convert();
    assert_eq!((b.as_ptr(), b.as_slice()), (p, LONG));

    // 1 word: truncated in place when unique, copied when shared
    let c = TinyCStr::try_from(LONG).unwrap();
    let p = c.as_ptr();
    let keep = c.clone();
    let shared: T = c.convert();
    assert_ne!(shared.as_ptr(), p);
    let unique: T = keep.convert();
    assert_eq!((unique.as_ptr(), unique.as_slice()), (p, LONG));

    // adding the NUL
    let c: HipCStr = HipStr::from("hello").try_convert().unwrap();
    assert_eq!(c.to_bytes_with_nul(), b"hello\0");
    let c: TinyCStr = W::from(LONG).try_convert().unwrap();
    assert_eq!(c.to_bytes(), LONG);
    let empty: HipCStr = HipStr::new().try_convert().unwrap();
    assert_eq!(empty.to_bytes_with_nul(), b"\0");
    let back: HipStr = empty.try_convert().unwrap();
    assert!(back.is_empty());

    // interior NUL
    let error = W::from(&b"a\0b"[..])
        .try_convert::<crate::enc::CStr, crate::repr::Wide<'static, Arc>>()
        .unwrap_err();
    assert_eq!(error.reason().nul_position(), 1);
    assert_eq!(error.into_source().as_slice(), b"a\0b");

    // C string to string: NUL dropped, then validated
    let c = HipCStr::try_from(&b"caf\xc3\xa9"[..]).unwrap();
    let s: TinyStr = c.try_convert().unwrap();
    assert_eq!(s, "café");
    let bad = HipCStr::try_from(&b"\xff"[..]).unwrap();
    assert!(
        bad.try_convert::<crate::enc::Utf8, crate::repr::Tiny<Arc>>()
            .is_err()
    );
}

#[cfg(feature = "std")]
#[test]
fn os_strings_and_paths() {
    use crate::{HipOsStr, TinyPath};

    let s = HipStr::from(String::from_utf8(LONG.to_vec()).unwrap());
    let p = s.as_ptr();
    let os: HipOsStr = s.convert();
    assert_eq!(os.as_encoded_bytes().as_ptr(), p);
    let path: TinyPath = os.convert();
    assert_eq!(path.as_os_str().as_encoded_bytes(), LONG);
    let back: HipStr = path.try_convert().unwrap();
    assert_eq!(back.as_bytes(), LONG);
    let os: Result<HipOsStr, _> = W::from(LONG).try_convert();
    assert!(os.is_ok());
}

#[test]
fn clones() {
    let w = W::from(LONG);
    let t: T = w.to_converted();
    assert_eq!(t.as_ptr(), w.as_ptr());
    let s: Result<SmallStr, _> = w.try_to_converted();
    assert_eq!(s.unwrap().as_bytes(), LONG);
    let v: Vec<u8> = w.into_vec();
    assert_eq!(v, LONG);
}

#[test]
fn generated_repr_impls() {
    // by value, generic over the family
    let w = HipStr::from(String::from_utf8(LONG.to_vec()).unwrap()).slice(0..40);
    let s: SmallStr = SmallStr::from(w.clone());
    assert_eq!(s.as_bytes(), &LONG[..40]);
    let t = TinyStr::from(s.clone());
    assert_eq!(t.as_ptr(), s.as_ptr());
    let back = HipStr::from(t.clone());
    assert_eq!(back.as_ptr(), t.as_ptr());
    let s2 = SmallStr::from(t);
    assert_eq!(s2.as_ptr(), back.as_ptr());
    let t2 = TinyStr::from(back);
    let w2 = HipStr::from(s2);
    assert_eq!(t2.as_ptr(), w2.as_ptr());

    // by reference, per family: shares the buffer
    let b = W::from(LONG);
    let s = S::from(&b);
    let t = T::from(&b);
    assert_eq!((s.as_ptr(), t.as_ptr()), (b.as_ptr(), b.as_ptr()));
    assert_eq!(W::from(&t).as_ptr(), b.as_ptr());
    assert_eq!(W::from(&s).as_ptr(), b.as_ptr());
    assert_eq!(T::from(&s).as_ptr(), b.as_ptr());
    assert_eq!(S::from(&t).as_ptr(), b.as_ptr());
    let c = HipCStr::try_from(LONG).unwrap();
    let tc = TinyCStr::from(&c);
    assert_eq!(tc.as_ptr(), c.as_ptr());
}

#[test]
fn generated_family_impls() {
    let s = HipStr::from(String::from_utf8(LONG.to_vec()).unwrap());
    // by reference: shares
    let b = HipByt::<'static, Arc>::from(&s);
    assert_eq!(b.as_ptr(), s.as_ptr());
    let back = HipStr::try_from(&b).unwrap();
    assert_eq!(back.as_ptr(), s.as_ptr());
    let c = HipCStr::try_from(&s).unwrap();
    assert_eq!(c.to_bytes(), LONG);
    let e = HipCStr::try_from(&W::from(&b"a\0"[..])).unwrap_err();
    assert_eq!(e.reason().nul_position(), 1);
    let from_c = HipByt::<'static, Arc>::from(&c);
    assert_eq!(from_c.as_slice(), LONG);
    let s2 = HipStr::try_from(c).unwrap();
    assert_eq!(s2.as_bytes(), LONG);
    let e = HipStr::try_from(&W::from(&b"\xff"[..])).unwrap_err();
    assert_eq!(e.into_source().as_slice(), b"\xff");
}

#[test]
fn std_types() {
    let v = LONG.to_vec();
    let b = W::from(&v);
    assert_eq!(b.as_slice(), LONG);
    let mut owned = String::from("hello");
    let s = HipStr::from(&mut *owned);
    assert_eq!(s, "hello");
    let s = HipStr::from(&owned);
    assert_eq!(s, "hello");
    let rc: alloc::rc::Rc<str> = "shared".into();
    assert_eq!(TinyStr::from(rc), "shared");
    let arc: alloc::sync::Arc<[u8]> = LONG.into();
    assert_eq!(S::from(arc).as_slice(), LONG);
    let cs = alloc::ffi::CString::new("c").unwrap();
    assert_eq!(HipCStr::from(&cs).to_bytes(), b"c");
}

#[test]
fn inline_bridges() {
    use crate::inline::{CapacityError, InlineByt, InlineCStr, InlineStr};

    let i = InlineStr::<8>::inline("abc");
    assert_eq!(i.try_resize::<3>().unwrap(), "abc");
    assert_eq!(i.try_resize::<2>(), Err(CapacityError));
    assert_eq!(i.widen::<16>(), "abc");

    let b: InlineByt<8> = i.convert();
    assert_eq!(b.as_slice(), b"abc");
    let s: InlineStr<8> = b.try_convert().unwrap();
    assert_eq!(s, "abc");
    let bad = InlineByt::<8>::inline(b"\xff");
    let e = bad.try_convert::<crate::enc::Utf8>().unwrap_err();
    assert!(matches!(
        e.reason(),
        crate::convert::InlineConvertError::Invalid(_)
    ));
    assert_eq!(e.into_source().as_slice(), b"\xff");
    let c: InlineCStr<8> = s.try_convert().unwrap();
    assert_eq!(c.as_bytes_with_nul(), b"abc\0");
    let back: InlineByt<8> = c.convert();
    assert_eq!(back.as_slice(), b"abc");
    let nul = InlineByt::<8>::inline(b"a\0");
    assert!(matches!(
        nul.try_convert::<crate::enc::CStr>().unwrap_err().reason(),
        crate::convert::InlineConvertError::Invalid(_)
    ));

    // Hip <-> Inline
    let h = HipStr::from(String::from_utf8(LONG.to_vec()).unwrap());
    assert!(h.try_to_inline::<8>().is_none());
    let long: InlineStr<64> = h.try_to_inline().unwrap();
    assert_eq!(long.as_bytes(), LONG);
    assert!(SmallStr::try_from_inline(&long).is_none());
    assert_eq!(HipStr::from(long), h, "From goes to the heap");
    // the 1-word inline capacity: one byte less than a word
    const TINY: usize = size_of::<usize>() - 1;
    let t = TinyStr::from_inline(InlineStr::<TINY>::inline("abc"));
    assert!(t.is_inline());
    let w = HipStr::try_from_inline(&InlineStr::<23>::inline("x")).unwrap();
    assert!(w.is_inline());
    let c = HipCStr::try_from(&b"ab"[..]).unwrap();
    let ic: InlineCStr<3> = c.try_to_inline().unwrap();
    assert_eq!(ic.as_bytes_with_nul(), b"ab\0");
    assert!(c.try_to_inline::<2>().is_none(), "no room for the NUL");
    let back = TinyCStr::from_inline(ic);
    assert_eq!(back.to_bytes_with_nul(), b"ab\0");

    // by value: gives the value back
    let e = InlineStr::<4>::try_from(h.clone()).unwrap_err();
    assert_eq!(*e.as_source(), h);
    let ok = InlineStr::<4>::try_from(HipStr::from("abc")).unwrap();
    assert_eq!(ok, "abc");
}

#[test]
fn short_heap_values_go_inline() {
    // 10 bytes: heap in 1 word, inline in 3 words; the unique buffer is freed
    let t = T::from(&LONG[..10]);
    assert!(t.is_allocated());
    let w: W = t.convert();
    assert!(w.is_inline());
    assert_eq!(w.as_slice(), &LONG[..10]);
    // from a 2-word inline value
    let s = S::from(&b"abc"[..]);
    let w: W = s.clone().convert();
    let t: T = s.convert();
    assert!(w.is_inline() && t.is_inline());
}

#[test]
fn error_formatting() {
    use alloc::format;
    use core::error::Error;

    use crate::convert::{InlineConvertError, OsStrError};

    let e = HipStr::try_from(W::from(&b"\xff"[..])).unwrap_err();
    assert_eq!(format!("{e}"), format!("{}", e.reason()));
    assert!(format!("{e:?}").starts_with("ConvertError"));
    assert!(e.source().is_some());
    let (value, _) = e.clone().into_parts();
    assert_eq!(value.as_slice(), b"\xff");

    let nul = HipCStr::try_from(W::from(&b"a\0"[..])).unwrap_err();
    assert_eq!(format!("{nul}"), "interior NUL byte at position 1");

    let os = OsStrError { valid_up_to: 3 };
    assert_eq!(os.valid_up_to(), 3);
    assert_eq!(format!("{os}"), "not a valid OS string from position 3");

    let capacity = InlineConvertError::<OsStrError>::Capacity(crate::inline::CapacityError);
    assert_eq!(format!("{capacity}"), "insufficient capacity");
    assert!(capacity.source().is_some());
    let invalid = InlineConvertError::Invalid(os);
    assert_eq!(format!("{invalid}"), format!("{os}"));
    assert!(invalid.source().is_some());
}

#[test]
fn inline_capacity_for_the_nul() {
    use crate::inline::{InlineCStr, InlineStr};

    let full = InlineStr::<4>::inline("abcd");
    let error = full.try_convert::<crate::enc::CStr>().unwrap_err();
    assert!(matches!(
        error.reason(),
        crate::convert::InlineConvertError::Capacity(_)
    ));
    assert_eq!(*error.as_source(), full);
    let ok: InlineCStr<5> = full.widen::<5>().try_convert().unwrap();
    assert_eq!(ok.as_bytes_with_nul(), b"abcd\0");
}

#[test]
fn c_string_with_nul() {
    let c = HipCStr::try_from(&b"ab"[..]).unwrap();
    assert_eq!(c.into_bytes_with_nul().as_slice(), b"ab\0");
}
