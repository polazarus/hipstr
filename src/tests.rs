//! Tests of the public layer, through the aliases.

use alloc::borrow::Cow;
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use core::fmt::Write;

use super::*;

const LONG: &str = "a string that is definitely longer than any inline capacity";

/// Tests shared by every size of a string family.
macro_rules! string_suite {
    ($name:ident, $t:ty, borrows = $borrows:expr) => {
        mod $name {
            use super::*;

            type S = $t;

            #[test]
            fn construct_and_read() {
                for text in ["", "abc", LONG] {
                    let s = S::from(text);
                    assert_eq!(s.as_str(), text);
                    assert_eq!(s.len(), text.len());
                    assert_eq!(s.is_empty(), text.is_empty());
                    assert_eq!(s, text);
                    assert_eq!(text, s);
                    assert_eq!(s, String::from(text));
                    assert_eq!(s.to_string(), text);
                    assert_eq!(&*s, text);
                }
                assert!(S::from("abc").is_inline());
                assert!(S::from(LONG).is_allocated());
                assert_eq!(S::default(), "");
            }

            #[test]
            fn string_round_trip_is_zero_copy() {
                let string = String::from(LONG);
                let ptr = string.as_ptr();
                let s = S::from(string);
                assert_eq!(s.as_str().as_ptr(), ptr);
                let back: String = s.into_string();
                assert_eq!(back.as_ptr(), ptr);
            }

            #[test]
            fn borrowing() {
                let cow = Cow::Borrowed(LONG);
                let s = S::from(cow);
                assert_eq!(s.is_borrowed(), $borrows);
                assert_eq!(s.as_borrowed().is_some(), $borrows);
                let cow: Cow<'_, str> = s.clone().into();
                assert_eq!(matches!(cow, Cow::Borrowed(_)), $borrows);
                let owned = s.into_owned();
                assert!(!owned.is_borrowed());
                assert_eq!(owned, LONG);
            }

            #[test]
            fn mutation_and_cow() {
                let a = S::from(LONG);
                let mut b = a.clone();
                b.push_str("!!");
                b.push('é');
                assert_eq!(a, LONG);
                assert_eq!(b.as_str(), alloc::format!("{LONG}!!é"));
                assert_eq!(b.pop(), Some('é'));
                b.truncate(3);
                assert_eq!(b, "a s");
                b.make_ascii_uppercase();
                assert_eq!(b, "A S");
                assert_eq!(b.as_mut_str().map(|s| s.len()), Some(3));
                write!(b, "-{}", 42).unwrap();
                assert_eq!(b, "A S-42");
                b.clear();
                assert!(b.is_empty() && b.is_inline());
            }

            #[test]
            #[should_panic(expected = "char boundary")]
            fn truncate_inside_char() {
                S::from("é").truncate(1);
            }

            #[test]
            fn guard() {
                let mut s = S::from("abc");
                s.mutate().push_str(LONG);
                assert_eq!(s.as_str(), alloc::format!("abc{LONG}"));
                assert!(s.is_allocated());
            }

            #[test]
            fn shrink() {
                let mut s = S::with_capacity(500);
                s.push_str("abc");
                assert!(s.capacity() >= 500);
                s.shrink_to_fit();
                assert!(s.is_inline());
                assert_eq!(s, "abc");
            }

            #[test]
            fn utf8() {
                let bytes = <S as Default>::default().into_bytes();
                assert!(S::from_utf8(bytes).unwrap().is_empty());
                let err = S::try_from(alloc::vec![0xff, 0xfe]).unwrap_err();
                assert_eq!(err.utf8_error().valid_up_to(), 0);
                let lossy = S::from_utf16_lossy(&[0x61, 0xD800]);
                assert_eq!(lossy, "a\u{FFFD}");
            }

            #[test]
            fn builders() {
                assert_eq!(S::from("ab").repeat(3), "ababab");
                assert_eq!(S::concat(["a", "b", "c"]), "abc");
                assert_eq!(S::join(["a", "b", "c"], ", "), "a, b, c");
                let collected: S = "héllo".chars().collect();
                assert_eq!(collected, "héllo");
                assert_eq!(S::from("ABC").to_lowercase(), "abc");
            }

            #[test]
            #[cfg(feature = "std")]
            fn ordering_and_hash() {
                use core::hash::BuildHasher;
                let a = S::from("a");
                let b = S::from(LONG);
                assert!(a < b);
                assert!(a < *"b");
                let h = std::hash::RandomState::new();
                assert_eq!(h.hash_one(&a), h.hash_one("a"));
                let mut set = std::collections::HashSet::new();
                set.insert(b.clone());
                assert!(set.contains(LONG));
            }
        }
    };
}

string_suite!(hip_str, HipStr<'static>, borrows = true);
string_suite!(small_str, SmallStr<'static>, borrows = true);
string_suite!(tiny_str, TinyStr, borrows = false);
string_suite!(local_hip_str, LocalHipStr<'static>, borrows = true);
string_suite!(local_tiny_str, LocalTinyStr, borrows = false);

#[test]
fn sizes() {
    let w = size_of::<usize>();
    assert_eq!(size_of::<HipStr<'_>>(), 3 * w);
    assert_eq!(size_of::<SmallStr<'_>>(), 2 * w);
    assert_eq!(size_of::<TinyStr>(), w);
    assert_eq!(size_of::<Option<TinyByt>>(), w);
    assert_eq!(HipStr::inline_capacity(), 3 * w - 1);
    assert_eq!(SmallStr::inline_capacity(), 2 * w - 1);
    assert_eq!(TinyStr::inline_capacity(), w - 1);
}

#[test]
fn covariance() {
    fn shorten<'a>(s: HipStr<'static>) -> HipStr<'a> {
        s
    }
    fn shorten_small<'a>(s: SmallStr<'static>) -> SmallStr<'a> {
        s
    }
    assert_eq!(shorten(HipStr::from_static(LONG)), LONG);
    assert_eq!(shorten_small(SmallStr::from_static(LONG)), LONG);
}

#[test]
fn const_ctors() {
    const A: HipStr<'static> = HipStr::borrowed("const");
    const B: SmallByt<'static> = SmallByt::borrowed(b"bytes");
    const C: TinyStr = TinyStr::new();
    assert_eq!(A, "const");
    assert_eq!(B, b"bytes".as_slice());
    assert!(C.is_empty());
}

#[test]
fn bytes() {
    let mut b = TinyByt::from(b"abc");
    b.push(b'd');
    b.push_slice(LONG.as_bytes());
    assert_eq!(b.len(), 4 + LONG.len());
    assert_eq!(b.pop(), Some(b'y'));
    let v: Vec<u8> = b.clone().into_vec();
    assert_eq!(v, b.as_slice());
    let mut s = HipByt::new();
    let spare = s.spare_capacity_mut();
    spare[0].write(7);
    // SAFETY: one byte initialized, unique after `spare_capacity_mut`
    unsafe { s.set_len(1) };
    assert_eq!(s, [7].as_slice());
    let collected: SmallByt<'_> = (0..40u8).collect();
    assert_eq!(collected.len(), 40);
}

#[test]
#[cfg(feature = "std")]
fn conversions_keep_storage() {
    let s = HipStr::from(LONG);
    let ptr = s.as_ptr();
    let b = s.into_bytes();
    assert_eq!(b.as_ptr(), ptr);
    let s = HipStr::from_utf8(b).unwrap();
    assert_eq!(s.as_ptr(), ptr);
    let os = HipOsStr::from(s);
    assert_eq!(os.as_encoded_bytes().as_ptr(), ptr);
    let p = HipPath::from(os);
    assert_eq!(p.as_os_str().as_encoded_bytes().as_ptr(), ptr);
    let s = p.into_str().unwrap();
    assert_eq!(s.as_ptr(), ptr);
}

#[test]
#[cfg(feature = "std")]
fn os_and_path() {
    let mut os = SmallOsStr::from("dir");
    os.push("/file");
    assert_eq!(os, std::ffi::OsStr::new("dir/file"));
    assert_eq!(os.to_str(), Some("dir/file"));
    let p = TinyPath::from(std::path::PathBuf::from("a/b"));
    assert_eq!(p.as_path().file_name(), Some(std::ffi::OsStr::new("b")));
    let borrowed = HipPath::borrowed(std::path::Path::new(LONG));
    assert!(borrowed.is_borrowed());
}

#[test]
#[allow(clippy::reversed_empty_ranges, reason = "tests the error")]
fn slicing() {
    let s = HipStr::from(LONG);
    let sub = s.slice(2..40);
    assert_eq!(sub, &LONG[2..40]);
    assert_eq!(sub.as_ptr(), s[2..].as_ptr(), "shares storage");
    let short = 2..2 + HipStr::inline_capacity();
    assert!(s.slice(short).is_inline(), "small slices are copied inline");
    assert_eq!(
        s.try_slice(5..1).unwrap_err().kind(),
        slice::SliceErrorKind::StartGreaterThanEnd
    );
    let accent = HipStr::from("é");
    let e = accent.try_slice(1..).unwrap_err();
    assert_eq!(e.kind(), slice::SliceErrorKind::StartNotACharBoundary);
    let word = &s[2..8];
    assert_eq!(s.slice_ref(word), "string");
    assert!(s.try_slice_ref("elsewhere").is_none());
    let b = HipByt::from(LONG.as_bytes());
    assert_eq!(b.slice(..=1), b"a ".as_slice());
}

/// Every `const` accessor, evaluated at compile time for every alias: if one
/// stops being `const`, this fails to build.
///
/// Values with drop glue cannot be dropped in a const context, hence the
/// `forget` calls.
mod const_accessors {
    use core::mem::forget;

    use super::*;

    /// Encoding-agnostic accessors, available for every family.
    macro_rules! agnostic {
        ($($t:ty),* $(,)?) => {$(
            const _: () = {
                let h = <$t>::new();
                assert!(h.len() == 0);
                assert!(h.is_empty());
                assert!(!h.as_ptr().is_null());
                assert!(h.is_inline());
                assert!(!h.is_borrowed());
                assert!(!h.is_allocated());
                assert!(<$t>::inline_capacity() > 0);
                forget(h);
            };
        )*};
    }

    agnostic!(HipStr<'static>, SmallStr<'static>, TinyStr, LocalTinyStr);
    agnostic!(HipByt<'static>, SmallByt<'static>, TinyByt);
    agnostic!(HipCStr<'static>, SmallCStr<'static>, TinyCStr);
    #[cfg(feature = "bstr")]
    agnostic!(HipBStr<'static>, SmallBStr<'static>, TinyBStr);

    #[cfg(feature = "bstr")]
    const _: () = {
        let b = SmallBStr::borrowed_bytes(b"bytes, longer than any inline capacity!");
        assert!(b.is_borrowed() && b.as_bytes().len() == 39);
        assert!(b.as_borrowed().is_some() && !b.as_ptr().is_null());
        let _: &bstr::BStr = b.as_bstr();
        let bytes = b.into_bytes();
        assert!(bytes.as_slice().len() == 39);
        forget(bytes);
        let empty = TinyBStr::new();
        let i = TinyBStr::try_inline(empty.as_bstr());
        assert!(i.is_some());
        forget(i);
        forget(empty);
        let x = HipBStr::borrowed_bytes(b"x");
        forget(HipBStr::inline(x.as_bstr()));
        forget(x);
    };

    /// C string accessors, every size.
    macro_rules! c_str_accessors {
        ($($t:ty),* $(,)?) => {$(
            const _: () = {
                // 2 characters + NUL: fits the 1-word inline buffer on 32-bit too
                let c = <$t>::inline(c"ab");
                assert!(c.len() == 2 && !c.is_empty() && c.is_inline());
                assert!(c.as_c_str().count_bytes() == 2);
                assert!(c.as_bytes().len() == 2);
                assert!(c.as_bytes_with_nul().len() == 3);
                assert!(!c.as_ptr().is_null());
                let b = c.into_bytes_with_nul();
                assert!(b.as_slice().len() == 3);
                forget(b);
                let e = <$t>::new();
                assert!(e.is_empty() && e.as_bytes_with_nul().len() == 1);
                forget(e);
                let r = <$t>::try_inline(c"definitely longer than any inline capacity");
                assert!(r.is_none());
                forget(r);
            };
        )*};
    }

    c_str_accessors!(HipCStr<'static>, SmallCStr<'static>, TinyCStr);

    const _: () = {
        let c = HipCStr::borrowed(c"borrowed C string, longer than inline");
        assert!(c.is_borrowed() && c.as_borrowed().is_some());
        let r = c.into_borrowed();
        assert!(r.is_ok());
        forget(r);
        forget(SmallCStr::from_static(c"static"));
    };
    #[cfg(feature = "std")]
    agnostic!(HipOsStr<'static>, SmallOsStr<'static>, TinyOsStr);
    #[cfg(feature = "std")]
    agnostic!(HipPath<'static>, SmallPath<'static>, TinyPath);

    /// OS string accessors, every size (`as_os_str` itself cannot be `const`).
    #[cfg(feature = "std")]
    macro_rules! os_accessors {
        ($($t:ty),* $(,)?) => {$(
            const _: () = {
                let o = <$t>::from_static("os string, longer than any inline capacity");
                assert!(o.as_encoded_bytes().len() == 42 && o.len() == 42);
                assert!(!o.as_ptr().is_null());
                forget(o);
            };
        )*};
    }

    #[cfg(feature = "std")]
    os_accessors!(HipOsStr<'static>, SmallOsStr<'static>);

    /// String accessors on a borrowed value.
    macro_rules! borrowed_str {
        ($str:ty, $byt:ty) => {
            const _: () = {
                let s = <$str>::borrowed("hello, this is longer than any inline buffer");
                assert!(s.is_borrowed());
                assert!(s.as_str().len() == 44);
                assert!(s.as_bytes().len() == 44);
                assert!(!s.as_ptr().is_null());
                assert!(s.as_borrowed().is_some());
                let r = s.into_borrowed();
                match r.as_ref() {
                    Ok(b) => assert!(b.len() == 44),
                    Err(_) => panic!("not borrowed"),
                }
                forget(r);

                let s = <$str>::from_static("static");
                let b = s.into_bytes();
                let r = <$str>::from_utf8(b);
                assert!(r.is_ok());
                forget(r);

                let b = <$byt>::borrowed(b"bytes");
                assert!(b.as_slice().len() == 5);
                assert!(!b.as_ptr().is_null());
                assert!(b.as_borrowed().is_some());
                // SAFETY: ASCII
                let s = unsafe { <$str>::from_utf8_unchecked(b) };
                assert!(s.as_str().len() == 5);
                forget(s);
            };
        };
    }

    borrowed_str!(HipStr<'static>, HipByt<'static>);
    borrowed_str!(SmallStr<'static>, SmallByt<'static>);

    /// `inline` / `try_inline` for every string and byte alias.
    macro_rules! inline_ctors {
        ($($str:ty, $byt:ty);* $(;)?) => {$(
            const _: () = {
                let s = <$str>::inline("abc");
                assert!(s.is_inline() && s.as_str().len() == 3);
                forget(s);
                let b = <$byt>::inline(b"abc");
                assert!(b.is_inline() && b.as_slice().len() == 3);
                forget(b);
                let r = <$str>::try_inline("longer than any inline capacity, really");
                assert!(r.is_none());
                forget(r);
            };
        )*};
    }

    inline_ctors!(HipStr<'static>, HipByt<'static>; SmallStr<'static>, SmallByt<'static>; TinyStr, TinyByt);

    // `Tiny*` types cannot borrow: check the typed accessors on empty values.
    const _: () = {
        let s = TinyStr::new();
        assert!(s.as_str().is_empty());
        assert!(s.as_bytes().is_empty());
        assert!(s.as_borrowed().is_none());
        let r = s.into_borrowed();
        assert!(r.is_err());
        forget(r);
        let b = TinyByt::new();
        assert!(b.as_slice().is_empty());
        assert!(!b.as_ptr().is_null());
        let r = TinyStr::from_utf8(b);
        assert!(r.is_ok());
        forget(r);
    };
}

#[test]
fn str_patterns_share_storage() {
    let text = "  first line, with words\nsecond line: more words here  ";
    let s = HipStr::from(text);
    let inside = |h: &HipStr<'_>| {
        let range = s.as_bytes().as_ptr_range();
        range.contains(&h.as_ptr()) || h.is_inline()
    };

    let trimmed = s.trim();
    assert_eq!(trimmed, text.trim());
    assert!(inside(&trimmed) && !trimmed.is_inline());

    let lines: Vec<_> = s.lines().collect();
    assert_eq!(lines, text.lines().collect::<Vec<_>>());
    assert!(lines.iter().all(inside));

    let words: Vec<_> = s.split_whitespace().collect();
    assert_eq!(words, text.split_whitespace().collect::<Vec<_>>());
    let rev: Vec<_> = s.rsplit(' ').collect();
    assert_eq!(rev, text.rsplit(' ').collect::<Vec<_>>());
    let n: Vec<_> = s.splitn(2, ',').collect();
    assert_eq!(n, text.splitn(2, ',').collect::<Vec<_>>());

    let (a, b) = s.split_once('\n').unwrap();
    assert_eq!((a.as_str(), b.as_str()), text.split_once('\n').unwrap());
    assert!(inside(&b) && !b.is_inline());

    let idx: Vec<_> = s
        .match_indices("words")
        .map(|(i, m)| (i, m.len()))
        .collect();
    assert_eq!(idx, alloc::vec![(19, 5), (43, 5)]);
    assert_eq!(
        s.trim_matches(' ').strip_prefix("first").unwrap().len(),
        text.trim().len() - 5
    );
    assert_eq!(s.trim_end_matches(char::is_whitespace), text.trim_end());
    assert!(s.strip_suffix("nope").is_none());

    // borrowed input: results stay borrowed, with the original lifetime
    let borrowed = HipStr::borrowed(text);
    let last = borrowed.split('\n').next_back().unwrap();
    assert!(last.is_borrowed());
    assert_eq!(last.into_borrowed().unwrap().as_ptr(), text[25..].as_ptr());
}

/// Reference counting across threads, for every size. Run under loom with
/// `RUSTFLAGS="--cfg loom" cargo test --release loom`.
#[cfg(any(loom, feature = "std"))]
mod loom_threads {
    #[cfg(not(loom))]
    use std::{sync, thread};

    #[cfg(loom)]
    use loom::{sync, thread};

    use super::*;

    fn model(f: impl Fn() + Send + Sync + 'static) {
        #[cfg(loom)]
        loom::model(f);
        #[cfg(not(loom))]
        f();
    }

    macro_rules! threads_suite {
        ($name:ident, $t:ty, $get_mut:ident) => {
            mod $name {
                use super::*;

                #[test]
                fn loom_clone_move_and_drop() {
                    model(|| {
                        for mut s in [<$t>::from(LONG), <$t>::from(String::from(LONG))] {
                            let threads = [(); 2].map(|_| {
                                let s = s.clone();
                                thread::spawn(move || {
                                    assert_eq!(s, LONG);
                                    drop(s);
                                })
                            });
                            for t in threads {
                                t.join().unwrap();
                            }
                            // every clone is gone: unique again, writable in place
                            assert!(s.$get_mut().is_some());
                        }
                    });
                }

                #[test]
                fn loom_orderly_drop() {
                    model(|| {
                        let (tx, rx) = sync::mpsc::channel::<$t>();
                        let s = <$t>::from(LONG);
                        let t1 = thread::spawn(move || {
                            let s = rx.recv().unwrap();
                            assert_eq!(s, LONG);
                        });
                        let t2 = thread::spawn(move || {
                            tx.send(s.clone()).unwrap();
                            drop(s);
                        });
                        t1.join().unwrap();
                        t2.join().unwrap();
                    });
                }
            }
        };
    }

    threads_suite!(hip_str, HipStr<'static>, as_mut_str);
    threads_suite!(small_str, SmallStr<'static>, as_mut_str);
    threads_suite!(tiny_str, TinyStr, as_mut_str);
}

/// Conversion and comparison glue, family by family (one call per impl).
mod glue {
    use alloc::boxed::Box;

    use super::*;

    #[test]
    fn str_glue() {
        let s: SmallStr = SmallStr::from('é');
        assert_eq!(s, "é");
        assert_eq!(<SmallStr as AsRef<[u8]>>::as_ref(&s), "é".as_bytes());
        let parsed: TinyStr = LONG.parse().unwrap();
        assert_eq!(parsed, LONG);

        let mut e = HipStr::new();
        e.extend(["ab", "cd"]);
        assert_eq!(e, "abcd");
        let c: SmallStr = ["x", "y", LONG].into_iter().collect();
        assert_eq!(c.len(), LONG.len() + 2);

        assert_eq!(HipStr::try_from(b"ok".as_slice()).unwrap(), "ok");
        assert!(HipStr::try_from(b"\xff".as_slice()).is_err());
        let bytes = HipByt::from(LONG.as_bytes());
        assert_eq!(HipStr::try_from(&bytes).unwrap(), LONG);
        let ptr = bytes.as_ptr();
        let s = HipStr::try_from(bytes).unwrap();
        assert_eq!(s.as_ptr(), ptr, "no copy");
        let bad = HipStr::try_from(HipByt::from(b"\xffbad")).unwrap_err();
        assert_eq!(bad.as_bytes(), b"\xffbad");

        let b: HipByt = s.clone().into();
        assert_eq!(b.as_ptr(), ptr);
        let v: Vec<u8> = s.clone().into();
        assert_eq!(v, LONG.as_bytes());
        assert_eq!(s.cmp(&HipStr::from("b")), "a".cmp("b"));
        assert!(Some(core::cmp::Ordering::Less) == s.partial_cmp(&HipStr::from("b")));
        let owned: Cow<'_, str> = Cow::Owned(LONG.to_string());
        assert_eq!(HipStr::from(owned), LONG);
        let boxed: Box<str> = LONG.into();
        assert_eq!(SmallStr::from(boxed), LONG);
        assert_eq!(HipStr::new().repeat(0), "");
        assert_eq!(HipStr::from("ab").repeat(0), "");
    }

    #[test]
    #[cfg(feature = "std")]
    fn str_std_glue() {
        use std::net::ToSocketAddrs;

        let s = SmallStr::from("dir/file");
        let os: &std::ffi::OsStr = s.as_ref();
        let p: &std::path::Path = s.as_ref();
        assert_eq!(os, "dir/file");
        assert_eq!(p.file_name(), Some(std::ffi::OsStr::new("file")));
        assert_eq!(std::ffi::OsString::from(s), "dir/file");
        let addr = HipStr::from("127.0.0.1:80")
            .to_socket_addrs()
            .unwrap()
            .next();
        assert_eq!(addr.unwrap().port(), 80);
    }

    #[test]
    fn bytes_glue() {
        let mut b = TinyByt::new();
        b.reserve(100);
        assert!(b.capacity() >= 100);
        b.extend_from_slice(b"abc");
        b.extend(b"def");
        assert_eq!(b, b"abcdef");
        assert_eq!(b.repeat(0), b"");
    }

    #[test]
    fn c_str_glue() {
        let c = HipCStr::try_from(String::from(LONG)).unwrap();
        assert_eq!(c.len(), LONG.len());
        let b: HipByt = c.clone().into();
        assert_eq!(b, LONG.as_bytes());
        let v: Vec<u8> = c.into();
        assert_eq!(v, LONG.as_bytes());
        let latin1 = SmallCStr::try_from(b"caf\xe9".as_slice()).unwrap();
        let back = latin1.into_str().unwrap_err();
        assert_eq!(back.as_bytes(), b"caf\xe9");
    }

    #[test]
    #[cfg(feature = "std")]
    fn os_str_glue() {
        use std::ffi::{OsStr, OsString};
        use std::path::Path;

        const S: HipOsStr<'static> = HipOsStr::from_static("static");
        assert!(S.is_borrowed());
        let b = SmallOsStr::borrowed("borrowed");
        assert!(b.is_borrowed());
        assert_eq!(
            <SmallOsStr as AsRef<Path>>::as_ref(&b),
            Path::new("borrowed")
        );

        let boxed: Box<str> = LONG.into();
        assert_eq!(HipOsStr::from(boxed), OsStr::new(LONG));
        assert_eq!(HipOsStr::from(Cow::Borrowed(LONG)), OsStr::new(LONG));
        assert_eq!(HipOsStr::from(&HipStr::from(LONG)), OsStr::new(LONG));

        let os = TinyOsStr::from(LONG);
        assert_eq!(os.to_string_lossy(), LONG);
        let bytes: TinyByt = os.clone().into();
        assert_eq!(bytes, LONG.as_bytes());
        let v: Vec<u8> = os.clone().into();
        assert_eq!(v, LONG.as_bytes());
        assert_eq!(os.into_os_string(), OsString::from(LONG));
    }

    #[test]
    #[cfg(feature = "std")]
    fn path_glue() {
        use std::ffi::{OsStr, OsString};
        use std::path::Path;

        const P: HipPath<'static> = HipPath::from_static("/static");
        assert!(P.is_borrowed());
        let b = SmallPath::borrowed("borrowed");
        assert!(b.is_borrowed());
        assert_eq!(<SmallPath as AsRef<OsStr>>::as_ref(&b), "borrowed");

        let p = HipPath::from(OsString::from(LONG));
        let os = HipOsStr::from(LONG);
        assert!(p == os && os == p);
        let boxed: Box<str> = LONG.into();
        assert_eq!(HipPath::from(boxed), p);
        assert_eq!(HipPath::from(Cow::Borrowed(LONG)), p);
        assert_eq!(HipPath::from(Cow::Borrowed(OsStr::new(LONG))), p);
        assert_eq!(HipPath::from(&HipStr::from(LONG)), p);
        assert_eq!(HipPath::from(&os), p);

        assert_eq!(HipOsStr::from(&p), os);
        assert_eq!(OsString::from(p.clone()), OsString::from(LONG));
        assert_eq!(HipOsStr::from(p.clone()), os);
        assert_eq!(p.into_os_str(), os);
        assert_eq!(SmallPath::from(LONG).as_path(), Path::new(LONG));
    }

    #[test]
    #[cfg(feature = "bstr")]
    fn b_str_glue() {
        use bstr::{BStr, BString, ByteSlice};

        const B: SmallBStr<'static> = SmallBStr::borrowed_bytes(b"bytes");
        assert!(B.is_borrowed());
        let mut s = HipBStr::from(LONG);
        assert!(s.as_mut_bytes().is_some(), "unique");
        let shared = s.clone();
        let mut s2 = shared.clone();
        assert!(s2.as_mut_bytes().is_none(), "shared");
        s2.to_mut_bytes()[0] = b'A';
        assert_eq!(s2[0], b'A');
        assert_eq!(s.pop(), Some(b'y'));
        s.truncate(3);
        assert_eq!(s, b"a s".as_bstr());

        let b: HipByt = shared.clone().into();
        assert_eq!(b, LONG.as_bytes());
        let v: Vec<u8> = shared.clone().into();
        assert_eq!(v, LONG.as_bytes());
        assert_eq!(HipStr::try_from(shared).unwrap(), LONG);
        assert!(HipStr::try_from(HipBStr::from(b"\xff")).is_err());

        // bstr glue on bytes and strings
        let bs = BString::from(LONG);
        let hb = HipByt::from(bs.clone());
        let hs = HipStr::from(LONG);
        assert!(hb == bs && bs == hb && hs == bs && bs == hs);
        let r: &BStr = bs.as_ref();
        assert!(hb <= r && r <= hb && hs >= bs && bs >= hs);
        assert_eq!(<HipStr as AsRef<BStr>>::as_ref(&hs), r);
        assert_eq!(HipByt::from(Cow::Borrowed(r)), hb);
        assert_eq!(HipByt::from(Cow::<BStr>::Owned(bs.clone())), hb);
        assert_eq!(BString::from(hb), bs);
    }

    #[test]
    fn slice_error_formats() {
        let s = HipStr::from("abc");
        let e = s.try_slice(1..10).unwrap_err();
        let dbg = alloc::format!("{e:?}");
        assert!(dbg.contains("SliceError"), "{dbg}");
        let b = HipByt::from(b"abc");
        let e = b.try_slice(4..).unwrap_err();
        assert!(!alloc::format!("{e}").is_empty());
        assert!(!alloc::format!("{e:?}").is_empty());
        for kind in [
            slice::SliceErrorKind::StartGreaterThanEnd,
            slice::SliceErrorKind::StartOutOfBounds,
            slice::SliceErrorKind::EndOutOfBounds,
            slice::SliceErrorKind::StartNotACharBoundary,
            slice::SliceErrorKind::EndNotACharBoundary,
        ] {
            assert!(alloc::format!("{kind}").contains("index"));
        }
    }

    #[test]
    fn into_std_owned_and_reverse_order() {
        let s = HipStr::from(LONG);
        assert!("a" < s && s > "a" && String::from("a") < s);
        assert_eq!(String::from(s.clone()), LONG);
        assert_eq!(
            Vec::<u8>::from(HipByt::from(LONG.as_bytes())),
            LONG.as_bytes()
        );
        assert_eq!(
            alloc::ffi::CString::from(TinyCStr::from(c"c")).as_c_str(),
            c"c"
        );
    }
}
