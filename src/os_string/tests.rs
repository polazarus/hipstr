use core::ops::Range;
use std::collections::HashSet;
use std::ffi::OsStr;

use crate::alloc::format;
use crate::alloc::string::String;
use crate::HipOsStr;

type H<'borrow> = HipOsStr<'borrow>;
const EMPTY_SLICE: &str = "";
const A: &str = "A";

const INLINE_CAPACITY: usize = HipOsStr::inline_capacity();

#[test]
fn test_deref() {
    let h = HipOsStr::borrowed("test");
    let _: &OsStr = &*h;
}

#[test]
fn test_new_default() {
    let new = HipOsStr::new();
    assert_eq!(new, "");
    assert!(new.is_empty());

    let new = HipOsStr::default();
    assert_eq!(new, "");
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
        h.push(A);
    }
    assert_eq!(h.len(), 42);
    assert_eq!(h, A.repeat(42).as_str());
    assert_eq!(h.as_ptr(), p);
}

#[test]
#[cfg(feature = "std")]
fn test_borrow_and_hash() {
    let mut set = HashSet::new();
    set.insert(HipOsStr::from("a"));
    set.insert(HipOsStr::from("b"));

    assert!(set.contains::<OsStr>("a".as_ref()));
    assert!(!set.contains::<OsStr>("c".as_ref()));
}

#[test]
fn test_fmt() {
    let source: &OsStr = "Rust \u{1F980}".as_ref();
    let a = HipOsStr::borrowed(source);
    assert_eq!(format!("{a:?}"), format!("{source:?}"));
}

#[test]
fn test_from_string() {
    let s = "A".repeat(42);
    let hs = HipOsStr::from(s.clone());
    assert!(!hs.is_borrowed());
    assert!(!hs.is_inline());
    assert!(hs.is_allocated());
    assert_eq!(hs.len(), 42);
    assert_eq!(hs.as_os_str(), s.as_str());
}

#[test]
fn test_borrowed() {
    let s = "0123456789";
    let string = HipOsStr::borrowed(s);
    assert!(string.is_borrowed());
    assert!(!string.is_inline());
    assert_eq!(string.len(), s.len());
    assert_eq!(string.as_os_str(), s);
    assert_eq!(string.as_ptr(), s.as_ptr());
}

#[test]
fn test_from_static() {
    const fn is_static_type<T: 'static>(_: &T) {}

    let s = "abcdefghijklmnopqrstuvwxyz";
    let string = HipOsStr::from_static(s);

    // compiler check
    is_static_type(&string);

    assert!(string.is_borrowed());
    assert!(!string.is_inline());
    assert!(!string.is_allocated());
    assert_eq!(string.len(), s.len());
    assert_eq!(string.as_os_str(), s);
    assert_eq!(string.as_ptr(), s.as_ptr());
}

#[test]
fn test_from_slice() {
    static V: &[u8] = &[b'a'; 1024];
    let s = core::str::from_utf8(V).unwrap();

    for size in [0, 1, INLINE_CAPACITY, INLINE_CAPACITY + 1, 256, 1024] {
        let string = HipOsStr::from(&s[..size]);
        assert_eq!(size <= INLINE_CAPACITY, string.is_inline());
        assert_eq!(size > INLINE_CAPACITY, string.is_allocated());
        assert_eq!(string.len(), size);
    }
}

#[test]
fn test_as_slice() {
    // static
    {
        let a = HipOsStr::borrowed("abc");
        assert!(a.is_borrowed());
        assert!(!a.is_inline());
        assert!(!a.is_allocated());
        assert_eq!(a.as_os_str(), "abc");
    }
    // inline
    {
        let a = HipOsStr::from("abc");
        assert!(!a.is_borrowed());
        assert!(a.is_inline());
        assert!(!a.is_allocated());
        assert_eq!(a.as_os_str(), "abc");
    }
    // allocated
    {
        let s = "A".repeat(42);
        let a = HipOsStr::from(s.as_str());
        assert!(!a.is_borrowed());
        assert!(!a.is_inline());
        assert!(a.is_allocated());
        assert_eq!(a.as_os_str(), s.as_str());
    }
}

#[test]
fn test_clone() {
    // static
    {
        let s: &'static str = "abc";
        let a = HipOsStr::borrowed(s);
        assert!(a.is_borrowed());
        let b = a.clone();
        drop(a);
        assert_eq!(b.as_os_str(), "abc");
        assert_eq!(s.as_ptr(), b.as_ptr());
    }

    // inline
    {
        let a = HipOsStr::from("abc");
        assert!(a.is_inline());
        let b = a.clone();
        drop(a);
        assert_eq!(b.as_os_str(), "abc");
    }

    // allocated
    {
        let s = "a".repeat(42);
        let p = s.as_ptr();
        let a = HipOsStr::from(s);
        assert!(a.is_allocated());
        let b = a.clone();
        drop(a);
        assert_eq!(b.as_os_str(), "a".repeat(42).as_str());
        assert_eq!(b.as_ptr(), p);
    }
}

#[test]
fn test_into_static() {
    // static
    let a = HipOsStr::borrowed("abc");
    assert_eq!(a.into_borrowed(), Ok("abc".as_ref()));

    // inline
    let a = HipOsStr::from("abc");
    let b = a.clone();
    assert_eq!(a.into_borrowed(), Err(b));

    // heap
    let a = HipOsStr::from("a".repeat(42).as_str());
    let b = a.clone();
    assert_eq!(a.into_borrowed(), Err(b));
}

#[test]
fn test_into_bytes() {
    let s = HipOsStr::from("A".repeat(42));
    let bytes = s.into_bytes();
    assert_eq!(bytes.len(), 42);
    assert_eq!(bytes.as_slice(), [b'A'; 42]);
}

#[test]
fn test_capacity() {
    let a = HipOsStr::borrowed("abc");
    assert_eq!(a.capacity(), a.len());

    let a = HipOsStr::from("abc");
    assert_eq!(a.capacity(), HipOsStr::inline_capacity());

    let mut v = String::with_capacity(42);
    for _ in 0..10 {
        v.push_str("abc");
    }
    let a = HipOsStr::from(v);
    assert_eq!(a.capacity(), 42);
}

#[test]
fn test_mutate_debug() {
    let mut a = HipOsStr::borrowed("abc");
    let debug = format!("{a:?}");
    let r = a.mutate();
    assert_eq!(format!("{r:?}"), debug);
}

#[test]
fn test_mutate_borrowed() {
    let mut a = HipOsStr::borrowed("abc");
    assert!(a.is_borrowed());
    {
        let mut r = a.mutate();
        assert_eq!(&*r, "abc");
        r.push("def");
    }
    assert!(!a.is_borrowed());
    assert_eq!(a, "abcdef");
}

#[test]
fn test_mutate_inline() {
    let mut a = HipOsStr::from("abc");
    assert!(a.is_inline());
    a.mutate().push("def");
    assert_eq!(a, "abcdef");
}

#[test]
fn test_mutate_allocated() {
    {
        // allocated, unique with enough capacity
        let mut v = String::with_capacity(42);
        v.push_str("abcdefghijklmnopqrstuvwxyz");
        let p = v.as_ptr();
        let mut a = HipOsStr::from(v);
        assert!(a.is_allocated());
        a.mutate().push("0123456789");
        assert!(a.is_allocated());
        assert_eq!(a, "abcdefghijklmnopqrstuvwxyz0123456789",);
        assert_eq!(a.as_ptr(), p);
    }

    {
        // allocated, shared
        let mut v = String::with_capacity(42);
        v.push_str("abcdefghijklmnopqrstuvwxyz");
        let mut a = HipOsStr::from(v);
        assert!(a.is_allocated());
        let b = a.clone();
        a.mutate().push("0123456789");
        assert!(a.is_allocated());
        assert_eq!(a, "abcdefghijklmnopqrstuvwxyz0123456789",);
        assert_eq!(b, "abcdefghijklmnopqrstuvwxyz");
        assert_ne!(a.as_ptr(), b.as_ptr());
    }
}

#[test]
fn test_push() {
    let mut a = HipOsStr::from("abc");
    a.push("def");
    assert_eq!(a, "abcdef");
}

#[test]
fn test_to_owned() {
    let b = "abc";
    let h = HipOsStr::from(b);
    assert!(h.is_inline());
    let h = h.into_owned();
    assert!(h.is_inline());

    let r = "*".repeat(42);

    let v = r.clone();
    let a = HipOsStr::borrowed(&v[0..2]);
    let a = a.into_owned();
    drop(v);
    assert_eq!(a, &r[0..2]);

    let v = r;
    let a = HipOsStr::from(&v[..]);
    drop(v);
    let p = a.as_ptr();
    let a = a.into_owned();
    assert_eq!(a.as_ptr(), p);
}

#[test]
fn test_into_str() {
    let s = "*".repeat(42);
    let ho = HipOsStr::from(s);
    assert!(ho.is_allocated());
    let hs = ho.clone().into_str().unwrap();
    assert!(core::ptr::eq(ho.as_os_str(), hs.as_str().as_ref()));

    #[cfg(windows)]
    {
        use std::ffi::OsString;
        use std::os::windows::ffi::OsStringExt;
        let shorts = [u16::from(b'a'), u16::from(b'b'), u16::from(b'c'), 0xD800];
        let source = OsString::from_wide(&shorts);
        let ho = HipOsStr::from(source);
        let _ = ho.into_str().unwrap_err();
    }
    #[cfg(unix)]
    {
        use std::os::unix::ffi::OsStrExt;
        let bytes = b"abc\x80";
        let ho = HipOsStr::from(OsStr::from_bytes(bytes));
        let _ = ho.into_str().unwrap_err();
    }
}

#[test]
fn test_to_str() {
    let s = "*".repeat(42);
    let ho = HipOsStr::from(s);
    assert!(ho.is_allocated());
    let hs = ho.to_str().unwrap();
    assert!(core::ptr::eq(ho.as_os_str(), hs.as_str().as_ref()));

    #[cfg(windows)]
    {
        use std::ffi::OsString;
        use std::os::windows::ffi::OsStringExt;
        let shorts = [u16::from(b'a'), u16::from(b'b'), u16::from(b'c'), 0xD800];
        let source = OsString::from_wide(&shorts);
        let ho = HipOsStr::from(source);
        assert!(ho.to_str().is_none());
    }
    #[cfg(unix)]
    {
        use std::os::unix::ffi::OsStrExt;
        let bytes = b"abc\x80";
        let ho = HipOsStr::from(OsStr::from_bytes(bytes));
        assert!(ho.to_str().is_none());
    }
}

#[test]
fn test_to_str_lossy() {
    let s = "*".repeat(42);
    let ho = HipOsStr::from(s);
    assert!(ho.is_allocated());
    let hs = ho.to_str_lossy();
    assert!(core::ptr::eq(ho.as_os_str(), hs.as_str().as_ref()));

    #[cfg(windows)]
    {
        use std::ffi::OsString;
        use std::os::windows::ffi::OsStringExt;
        let shorts = [u16::from(b'a'), u16::from(b'b'), u16::from(b'c'), 0xD800];
        let source = OsString::from_wide(&shorts);
        let ho = HipOsStr::from(source);
        let hs = ho.to_str_lossy();
        assert_eq!(hs, "abc�");
    }
    #[cfg(unix)]
    {
        use std::os::unix::ffi::OsStrExt;
        let bytes = b"abc\x80";
        let ho = HipOsStr::from(OsStr::from_bytes(bytes));
        let hs = ho.to_str_lossy();
        assert_eq!(hs, "abc�");
    }
}

/// Gets an `OsStr` slice out of a `HipOsStr`.
///
/// # Safety
///
/// The range must be at "os char" boundary.
unsafe fn sl<'a>(h: &'a HipOsStr, r: Range<usize>) -> &'a OsStr {
    unsafe { OsStr::from_encoded_bytes_unchecked(&h.0[r]) }
}

#[test]
fn test_slice_ref_unchecked() {
    let s = String::from("abc");
    let a = HipOsStr::borrowed(s.as_str());

    unsafe {
        assert_eq!(a.slice_ref_unchecked(sl(&a, 0..1)).as_encoded_bytes(), b"a");
        assert_eq!(a.slice_ref_unchecked(sl(&a, 0..0)).as_encoded_bytes(), b"");
        assert_eq!(a.slice_ref_unchecked(sl(&a, 3..3)).as_encoded_bytes(), b"");
    }

    let a = HipOsStr::from(s.as_str());

    unsafe {
        assert_eq!(a.slice_ref_unchecked(sl(&a, 0..1)).as_encoded_bytes(), b"a");
        assert_eq!(a.slice_ref_unchecked(sl(&a, 0..0)).as_encoded_bytes(), b"");
        assert_eq!(a.slice_ref_unchecked(sl(&a, 3..3)).as_encoded_bytes(), b"");
    }

    let s = "*".repeat(42);
    let a = HipOsStr::from(s);

    unsafe {
        assert_eq!(a.slice_ref_unchecked(sl(&a, 0..1)).as_encoded_bytes(), b"*");
        assert_eq!(a.slice_ref_unchecked(sl(&a, 0..41)).as_ptr(), a.as_ptr());
        assert_eq!(a.slice_ref_unchecked(sl(&a, 0..0)).as_encoded_bytes(), b"");
        assert_eq!(a.slice_ref_unchecked(sl(&a, 3..3)).as_encoded_bytes(), b"");
    }
}

#[test]
fn test_try_slice_ref() {
    let s = String::from("abc");
    let a = HipOsStr::borrowed(s.as_str());

    assert_eq!(
        a.try_slice_ref(unsafe { sl(&a, 0..1) })
            .unwrap()
            .as_encoded_bytes(),
        b"a"
    );
    assert_eq!(
        a.try_slice_ref(unsafe { sl(&a, 0..0) })
            .unwrap()
            .as_encoded_bytes(),
        b""
    );
    assert_eq!(
        a.try_slice_ref(unsafe { sl(&a, 3..3) })
            .unwrap()
            .as_encoded_bytes(),
        b""
    );

    assert!(a.try_slice_ref(OsStr::new("abc")).is_none());
    assert!(a.try_slice_ref(OsStr::new("")).is_none());

    let b = HipOsStr::borrowed(&s[0..2]);
    assert!(b.try_slice_ref(s[1..3].as_ref()).is_none());
}

#[test]
fn test_slice_ref() {
    let s = String::from("abc");
    let a = HipOsStr::borrowed(&s);

    assert_eq!(
        a.slice_ref(unsafe { sl(&a, 0..1) }).as_encoded_bytes(),
        b"a"
    );
    assert_eq!(a.slice_ref(unsafe { sl(&a, 0..0) }).as_encoded_bytes(), b"");
    assert_eq!(a.slice_ref(unsafe { sl(&a, 3..3) }).as_encoded_bytes(), b"");
}

#[test]
#[should_panic]
fn test_slice_ref_panic() {
    let s = String::from("abc");
    let a = HipOsStr::borrowed(&s);
    let _ = a.slice_ref("abc".as_ref());
}

#[test]
fn test_shrink_to_fit() {
    let mut h = H::with_capacity(INLINE_CAPACITY + 1);
    h.shrink_to_fit();
    assert_eq!(h.capacity(), INLINE_CAPACITY);

    let mut h = H::from("abc");
    h.shrink_to_fit();
    assert_eq!(h.capacity(), INLINE_CAPACITY);

    let mut h = H::from_static("abc");
    h.shrink_to_fit();
    assert_eq!(h.capacity(), 3);
}

#[test]
fn test_shrink_to() {
    let mut h = H::with_capacity(INLINE_CAPACITY + 1);
    h.push("a");
    h.shrink_to(0);
    assert_eq!(h.capacity(), INLINE_CAPACITY);
    assert_eq!(h.len(), 1);

    let mut h = H::from("abc");
    h.shrink_to(4);
    assert_eq!(h.capacity(), INLINE_CAPACITY);

    let mut h = H::from_static("abc");
    assert_eq!(h.capacity(), 3);
    h.shrink_to(0);
    assert_eq!(h.capacity(), 3);
}
