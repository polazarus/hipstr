use alloc::format;
use alloc::string::String;
use std::collections::HashSet;
use std::ffi::OsStr;
use std::path::Path;

use crate::os_string::HipOsStr;
use crate::HipPath;

type H<'borrow> = HipPath<'borrow>;

const INLINE_CAPACITY: usize = HipPath::inline_capacity();

#[test]
fn test_deref() {
    let h = H::borrowed("test");
    let _: &Path = &h;
}

#[test]
fn test_new_default() {
    let empty_path: &Path = "".as_ref();
    let new = H::new();
    assert_eq!(new, empty_path);
    assert!(new.0.is_empty());

    let new = H::default();
    assert_eq!(new, empty_path);
    assert!(new.0.is_empty());
}

#[test]
fn test_borrow_and_hash() {
    let mut set = HashSet::new();
    set.insert(H::from("a"));
    set.insert(H::from("b"));

    assert!(set.contains::<Path>("a".as_ref()));
    assert!(!set.contains::<Path>("c".as_ref()));
}

#[test]
fn test_fmt() {
    let source: &OsStr = "Rust \u{1F980}".as_ref();
    let a = H::borrowed(source);
    assert_eq!(format!("{a:?}"), format!("{source:?}"));
}

#[test]
fn test_from_string() {
    let s = "A".repeat(42);
    let hs = H::from(s.clone());
    assert!(!hs.is_borrowed());
    assert!(!hs.is_inline());
    assert!(hs.is_allocated());
    assert_eq!(hs.0.len(), 42);
    assert_eq!(hs.as_os_str(), s.as_str());
}

#[test]
fn test_borrowed() {
    let s = "0123456789";
    let path = H::borrowed(s);
    assert!(path.is_borrowed());
    assert!(!path.is_inline());
    assert_eq!(path.0.len(), s.len());
    assert_eq!(path.as_os_str(), s);
    assert_eq!(path.0.as_ptr(), s.as_ptr());
}

#[test]
fn test_from_static() {
    const fn is_static_type<T: 'static>(_: &T) {}

    let s = "abcdefghijklmnopqrstuvwxyz";
    let path = H::from_static(s);

    // compiler check
    is_static_type(&path);

    assert!(path.is_borrowed());
    assert!(!path.is_inline());
    assert!(!path.is_allocated());
    assert_eq!(path.0.len(), s.len());
    assert_eq!(path.as_os_str(), s);
    assert_eq!(path.0.as_ptr(), s.as_ptr());
}

#[test]
fn test_from_slice() {
    static V: &[u8] = &[b'a'; 1024];
    let s = core::str::from_utf8(V).unwrap();

    for size in [0, 1, INLINE_CAPACITY, INLINE_CAPACITY + 1, 256, 1024] {
        let path = H::from(&s[..size]);
        assert_eq!(size <= INLINE_CAPACITY, path.is_inline());
        assert_eq!(size > INLINE_CAPACITY, path.is_allocated());
        assert_eq!(path.0.len(), size);
    }
}

#[test]
fn test_as_slice() {
    // static
    {
        let a = H::borrowed("abc");
        assert!(a.is_borrowed());
        assert!(!a.is_inline());
        assert!(!a.is_allocated());
        assert_eq!(a.as_os_str(), "abc");
    }
    // inline
    {
        let a = H::from("abc");
        assert!(!a.is_borrowed());
        assert!(a.is_inline());
        assert!(!a.is_allocated());
        assert_eq!(a.as_os_str(), "abc");
    }
    // allocated
    {
        let s = "A".repeat(42);
        let a = H::from(s.as_str());
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
        let a = H::borrowed(s);
        assert!(a.is_borrowed());
        let b = a.clone();
        drop(a);
        assert_eq!(b.as_os_str(), "abc");
        assert_eq!(s.as_ptr(), b.0.as_ptr());
    }

    // inline
    {
        let a = H::from("abc");
        assert!(a.is_inline());
        let b = a.clone();
        drop(a);
        assert_eq!(b.as_os_str(), "abc");
    }

    // allocated
    {
        let s = "a".repeat(42);
        let p = s.as_ptr();
        let a = H::from(s);
        assert!(a.is_allocated());
        let b = a.clone();
        drop(a);
        assert_eq!(b.as_os_str(), "a".repeat(42).as_str());
        assert_eq!(b.0.as_ptr(), p);
    }
}

#[test]
fn test_into_borrowed() {
    // borrowed
    let a = H::borrowed("abc");
    assert_eq!(a.into_borrowed(), Ok("abc".as_ref()));

    // inline
    let a = H::from("abc");
    let b = a.clone();
    assert_eq!(a.into_borrowed(), Err(b));

    // heap
    let a = H::from("a".repeat(42).as_str());
    let b = a.clone();
    assert_eq!(a.into_borrowed(), Err(b));
}

#[test]
fn test_as_borrowed() {
    let abc: &'static Path = Path::new("abc");
    let medium: &'static Path = Path::new("abcdefghijklmnopqrstuvwxyz");

    // borrowed
    let a = H::borrowed(abc);
    let b = a.as_borrowed().unwrap();
    assert_eq!(b, abc);
    assert!(core::ptr::eq(b, abc));

    // inline
    let a = H::from(abc);
    assert_eq!(a.as_borrowed(), None);

    // heap
    let a = H::from(medium);
    assert_eq!(a.as_borrowed(), None);
}

#[test]
fn test_into_os_string() {
    let h = H::from("A".repeat(42));
    let os_string = h.into_os_string().unwrap();
    assert_eq!(os_string.len(), 42);
    assert_eq!(os_string.as_encoded_bytes(), [b'A'; 42]);
}

#[test]
fn test_into_path_buf() {
    let h = H::from("A".repeat(42));
    let path_buf = h.into_path_buf().unwrap();
    assert_eq!(path_buf.as_os_str().len(), 42);
    assert_eq!(path_buf, Path::new(&"A".repeat(42)));
}

#[test]
fn test_into_str() {
    let h = H::from("A".repeat(42));
    let string = h.into_str().unwrap();
    assert_eq!(string.len(), 42);
    assert_eq!(string, "A".repeat(42));

    #[cfg(windows)]
    {
        use std::ffi::OsString;
        use std::os::windows::ffi::OsStringExt;
        let shorts = [u16::from(b'a'), u16::from(b'b'), u16::from(b'c'), 0xD800];
        let source = OsString::from_wide(&shorts);
        let hp = H::from(source);
        let _ = hp.into_str().unwrap_err();
    }
    #[cfg(unix)]
    {
        use std::os::unix::ffi::OsStrExt;
        let bytes = b"abc\x80";
        let hp = H::from(OsStr::from_bytes(bytes));
        let _ = hp.into_str().unwrap_err();
    }
}

#[test]
fn test_capacity() {
    let a = H::borrowed("abc");
    assert_eq!(a.capacity(), a.0.len());

    let a = H::from("abc");
    assert_eq!(a.capacity(), H::inline_capacity());

    let mut v = String::with_capacity(42);
    for _ in 0..10 {
        v.push_str("abc");
    }
    let a = H::from(v);
    assert_eq!(a.capacity(), 42);
}

#[test]
fn test_mutate_debug() {
    let mut a = H::borrowed("abc");
    let debug = format!("{a:?}");
    let r = a.mutate();
    assert_eq!(format!("{r:?}"), debug);
}

#[test]
fn test_mutate_borrowed() {
    let mut a = H::borrowed("abc");
    assert!(a.is_borrowed());
    {
        let mut r = a.mutate();
        assert_eq!(&*r, Path::new("abc"));
        r.push("def");
    }
    assert!(!a.is_borrowed());
    assert_eq!(a, Path::new("abc/def"));
}

#[test]
fn test_mutate_inline() {
    let mut a = H::from("abc");
    assert!(a.is_inline());
    a.mutate().push("def");
    assert_eq!(a, Path::new("abc/def"));
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
        a.mutate().push("0123456789");
        assert!(a.is_allocated());
        assert_eq!(a, Path::new("abcdefghijklmnopqrstuvwxyz/0123456789"));
        assert_eq!(a.0.as_ptr(), p);
    }

    {
        // allocated, shared
        let mut v = String::with_capacity(42);
        v.push_str("abcdefghijklmnopqrstuvwxyz");
        let mut a = H::from(v);
        assert!(a.is_allocated());
        let b = a.clone();
        a.mutate().push("0123456789");
        assert!(a.is_allocated());
        assert_eq!(a, Path::new("abcdefghijklmnopqrstuvwxyz/0123456789"));
        assert_eq!(b, Path::new("abcdefghijklmnopqrstuvwxyz"));
        assert_ne!(a.0.as_ptr(), b.0.as_ptr());
    }
}

#[test]
fn test_to_owned() {
    let b = "abc";
    let h = H::from(b);
    assert!(h.is_inline());
    let h = h.into_owned();
    assert!(h.is_inline());

    let r = "*".repeat(42);

    let v = r.clone();
    let a = H::borrowed(&v[0..2]);
    let a = a.into_owned();
    drop(v);
    assert_eq!(a, Path::new(&r[0..2]));

    let a = H::from(&r[..]);
    drop(r);
    let p = a.0.as_ptr();
    let a = a.into_owned();
    assert_eq!(a.0.as_ptr(), p);
}

#[test]
fn test_shrink_to_fit() {
    let h = HipOsStr::with_capacity(INLINE_CAPACITY + 1);
    let mut h = H::from(h);
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
    let mut h = HipOsStr::with_capacity(INLINE_CAPACITY + 1);
    h.push("a");
    let mut h = H::from(h);
    h.shrink_to(0);
    assert_eq!(h.capacity(), INLINE_CAPACITY);
    assert_eq!(h.as_os_str().len(), 1);

    let mut h = H::from("abc");
    h.shrink_to(4);
    assert_eq!(h.capacity(), INLINE_CAPACITY);

    let mut h = H::from_static("abc");
    assert_eq!(h.capacity(), 3);
    h.shrink_to(0);
    assert_eq!(h.capacity(), 3);
}
