//! Tests of the public layer, through the aliases.

use alloc::borrow::Cow;
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use core::fmt::Write;

use super::*;

// not under Miri on Windows: a global allocator makes Miri run std's
// Windows `System` allocator, whose header read breaks Stacked Borrows
#[cfg(not(all(miri, windows)))]
pub mod failing_alloc;

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
        let _: &::bstr::BStr = b.as_bstr();
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
    macro_rules! cstr_accessors {
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

    cstr_accessors!(HipCStr<'static>, SmallCStr<'static>, TinyCStr);

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
    fn cstr_glue() {
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
    fn bstr_glue() {
        use ::bstr::{BStr, BString, ByteSlice};

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

/// Std parity details the differential tests do not reach: panics, panic
/// safety, leaked iterators, trait impls.
mod parity {
    use alloc::boxed::Box;
    use alloc::rc::Rc;
    use alloc::sync::Arc;
    use alloc::vec;

    use super::*;

    #[test]
    #[should_panic(expected = "insertion index (is 4) should be <= len (is 3)")]
    fn insert_out_of_bounds() {
        HipByt::from(b"abc").insert(4, 0);
    }

    #[test]
    #[should_panic(expected = "removal index (is 3) should be < len (is 3)")]
    fn remove_out_of_bounds() {
        SmallByt::from(b"abc").remove(3);
    }

    #[test]
    #[should_panic(expected = "range end index 5 out of range for slice of length 3")]
    fn drain_out_of_bounds() {
        let _ = TinyByt::from(b"abc").drain(1..5);
    }

    #[test]
    #[should_panic(expected = "slice index starts at 2 but ends at 1")]
    #[allow(clippy::reversed_empty_ranges, reason = "tests the panic")]
    fn drain_reversed() {
        let _ = HipByt::from(b"abc").drain(2..1);
    }

    #[test]
    #[should_panic(expected = "is not a char boundary")]
    fn str_insert_not_on_boundary() {
        HipStr::from("é").insert(1, 'x');
    }

    #[test]
    #[should_panic(expected = "is not a char boundary")]
    fn str_drain_not_on_boundary() {
        let _ = SmallStr::from("é").drain(..1);
    }

    #[test]
    #[cfg(feature = "std")]
    fn retain_is_panic_safe() {
        let mut b = HipByt::from(LONG.as_bytes());
        let mut seen = 0;
        let r = std::panic::catch_unwind(core::panic::AssertUnwindSafe(|| {
            b.retain(|&x| {
                seen += 1;
                assert!(seen < 10, "boom");
                x != b' '
            });
        }));
        assert!(r.is_err());
        // the first 9 bytes were filtered, the rest kept as is
        let mut expected: Vec<u8> = LONG.as_bytes()[..9]
            .iter()
            .copied()
            .filter(|&x| x != b' ')
            .collect();
        expected.extend_from_slice(&LONG.as_bytes()[9..]);
        assert_eq!(b, expected.as_slice());

        let mut s = HipStr::from("é a é b é c");
        let mut n = 0;
        let r = std::panic::catch_unwind(core::panic::AssertUnwindSafe(|| {
            s.retain(|c| {
                n += 1;
                assert!(n < 5, "boom");
                c != ' '
            });
        }));
        assert!(r.is_err());
        assert_eq!(s, "éaé b é c", "valid UTF-8, unvisited part kept");
    }

    #[test]
    fn leaked_iterators_leave_the_value_unchanged() {
        let mut b = HipByt::from(LONG.as_bytes());
        core::mem::forget(b.drain(1..10));
        assert_eq!(b, LONG.as_bytes());
        let mut s = HipStr::from(LONG);
        core::mem::forget(s.drain(..5));
        assert_eq!(s, LONG);
    }

    #[test]
    fn untouched_borrowed_values_stay_borrowed() {
        let mut b = HipByt::borrowed(LONG.as_bytes());
        b.retain(|_| true);
        b.dedup();
        drop(b.drain(3..3));
        assert!(b.is_borrowed());
        let mut s = SmallStr::borrowed(LONG);
        s.retain(|_| true);
        s.replace_range(2..2, "");
        assert!(s.is_borrowed());
    }

    #[test]
    fn drain_both_ends() {
        let mut b = HipByt::from(b"abcdef");
        let mut d = b.drain(1..5);
        assert_eq!(d.len(), 4);
        assert_eq!((d.next(), d.next_back()), (Some(b'b'), Some(b'e')));
        assert_eq!(d.as_slice(), b"cd");
        drop(d);
        assert_eq!(b, b"af");

        let mut s = HipStr::from("αβγδ");
        let mut d = s.drain(2..6);
        assert_eq!(d.as_str(), "βγ");
        assert_eq!(d.next_back(), Some('γ'));
        drop(d);
        assert_eq!(s, "αδ");
    }

    #[test]
    fn try_reserve_errors_are_std() {
        let mut b = TinyByt::from(b"x");
        let e: alloc::collections::TryReserveError = b.try_reserve(usize::MAX).unwrap_err();
        assert!(!alloc::format!("{e}").is_empty());
        b.try_reserve_exact(10).unwrap();
        assert!(b.capacity() >= 11);
        b.reserve_exact(100);
        assert!(b.capacity() >= 101);
    }

    #[test]
    fn mutable_access_is_copy_on_write() {
        let a = HipByt::from(LONG.as_bytes());
        let mut b = a.clone();
        b[0] = b'A';
        assert_eq!(a[0], b'a');
        assert_eq!(b[0], b'A');
        for x in &mut b {
            *x = x.to_ascii_uppercase();
        }
        assert_eq!(a, LONG.as_bytes());
        let mut s = HipStr::from(LONG);
        let t = s.clone();
        s.make_ascii_uppercase();
        <HipStr as AsMut<str>>::as_mut(&mut s).make_ascii_lowercase();
        assert_eq!(s, t);
    }

    #[test]
    fn iterators_and_arrays() {
        let b = SmallByt::from(b"abc");
        assert_eq!((&b).into_iter().count(), 3);
        let mut it = b.clone().into_iter();
        assert_eq!(it.next_back(), Some(b'c'));
        assert_eq!(it.as_slice(), b"ab");
        assert_eq!(it.collect::<Vec<_>>(), b"ab");
        let arr: [u8; 3] = b.clone().try_into().unwrap();
        assert_eq!(&arr, b"abc");
        assert!(<[u8; 2]>::try_from(b).is_err());
        assert_eq!(HipByt::from([1u8, 2]), [1, 2]);
        assert_eq!(HipByt::from("str"), b"str");
        assert_eq!(HipByt::from(String::from(LONG)), LONG.as_bytes());
    }

    #[test]
    fn string_operators_and_collections() {
        let s = HipStr::from("a") + "b";
        let mut s = s;
        s += "c";
        assert_eq!(s, "abc");
        let parts = vec![String::from("x"), String::from("y")];
        assert_eq!(parts.into_iter().collect::<TinyStr>(), "xy");
        let mut e = SmallStr::new();
        e.extend([Cow::Borrowed("1"), Cow::Owned(String::from("2"))]);
        e.extend([HipStr::from("3")]);
        e.extend(['4', '5'].iter());
        assert_eq!(e, "12345");
        let boxed: Box<str> = e.clone().into();
        let rc: Rc<str> = e.clone().into();
        let arc: Arc<str> = e.into();
        assert!(&*boxed == "12345" && &*rc == "12345" && &*arc == "12345");
        let c = HipStr::try_from(alloc::ffi::CString::new("c").unwrap()).unwrap();
        assert_eq!(c, "c");
    }

    #[test]
    fn c_strings() {
        let c: HipCStr = "abc".parse().unwrap();
        assert_eq!(c, c"abc");
        assert!("a\0b".parse::<HipCStr>().is_err());
        let nz: Vec<core::num::NonZero<u8>> =
            b"xy".iter().map(|&b| b.try_into().unwrap()).collect();
        assert_eq!(TinyCStr::from(nz), c"xy");
        assert_eq!(c.clone().into_string().unwrap(), "abc");
        assert_eq!(&*c.clone().into_boxed_c_str(), c"abc");
        let v = HipCStr::from_vec_with_nul(b"z\0".to_vec()).unwrap();
        assert_eq!(v, c"z");
        // SAFETY: no NUL
        assert_eq!(
            unsafe { SmallCStr::from_vec_unchecked(b"q".to_vec()) },
            c"q"
        );
    }

    #[test]
    #[cfg(feature = "std")]
    fn os_strings_and_paths() {
        use std::ffi::OsStr;
        use std::fmt::Write as _;
        use std::path::Path;

        let mut o: HipOsStr = ["a", "b"].iter().map(OsStr::new).collect();
        write!(o, "{}", 1).unwrap();
        assert_eq!(o, OsStr::new("ab1"));
        assert_eq!(o.clone().into_string().unwrap(), "ab1");
        assert_eq!(o.clone().into_encoded_bytes(), b"ab1");
        let shared = o.clone();
        o.make_ascii_uppercase();
        assert_eq!(
            (o.as_os_str(), shared.as_os_str()),
            (OsStr::new("AB1"), OsStr::new("ab1"))
        );
        o.make_ascii_lowercase();
        assert_eq!(o, shared);

        let mut p: SmallPath = ["/usr", "lib"].iter().collect();
        assert_eq!(p, Path::new("/usr/lib"));
        p.extend(["x.tar"]);
        assert!(p.add_extension("gz"));
        assert_eq!(p, Path::new("/usr/lib/x.tar.gz"));
        assert!(p.set_extension("zst"));
        p.set_file_name("y");
        assert_eq!(p, Path::new("/usr/lib/y"));
        assert_eq!((&p).into_iter().count(), 4);
        assert!(HipPath::from("").pop() == false);
        assert!(!HipPath::from("/").set_extension("x"));
        #[cfg(not(miri))] // leaks on purpose
        {
            let leaked: &'static mut Path = TinyPath::from("leak").leak();
            assert_eq!(leaked, Path::new("leak"));
        }
    }

    #[test]
    #[cfg(feature = "std")]
    fn io_write() {
        use std::io::Write as _;
        let mut b = TinyByt::new();
        write!(b, "{}-{}", 1, 2).unwrap();
        b.flush().unwrap();
        assert_eq!(b, b"1-2");
    }
}

/// One call per new std-parity method not reached by the other tests (most
/// are otherwise only exercised by doctests, which coverage does not count).
mod parity_coverage {
    use alloc::format;
    use core::borrow::BorrowMut;

    use super::*;

    #[test]
    fn byte_methods() {
        let mut b = TinyByt::from_fn(4, |i| i as u8);
        assert_eq!(b, [0, 1, 2, 3]);
        *b.insert_mut(0, 9) += 1;
        *b.push_mut(7) += 1;
        assert_eq!(b, [10, 0, 1, 2, 3, 8]);
        b.retain_mut(|x| {
            *x += 1;
            *x % 2 == 1
        });
        assert_eq!(b, [11, 1, 3, 9]);
        let mut d = SmallByt::from(b"aAbBbc");
        d.dedup_by_key(|x| x.to_ascii_lowercase());
        assert_eq!(d, b"abc");
        let mut d = HipByt::from(b"aab");
        d.dedup_by(|a, b| a == b);
        assert_eq!(d, b"ab");
        let mut n = 0;
        d.resize_with(4, || {
            n += 1;
            n
        });
        assert_eq!(d, [b'a', b'b', 1, 2]);
        d.resize_with(1, || 0);
        assert_eq!(d, b"a");
        assert_eq!(&*HipByt::from(b"xy").into_boxed_slice(), b"xy");

        let mut s = HipByt::from(b"abcdef");
        let mut sp = s.splice(1..4, [b'X']);
        assert_eq!(sp.next_back(), Some(b'd'));
        assert!(format!("{sp:?}").contains("Splice"));
        drop(sp);
        assert_eq!(s, b"aXef");
        let d = s.drain(..1);
        assert!(format!("{d:?}").contains("Drain"));
        drop(d);
        let e = s.extract_if(.., |_| false);
        assert!(format!("{e:?}").contains("ExtractIf"));
        drop(e);
        let it = s.clone().into_iter();
        assert!(format!("{it:?}").contains("IntoIter"));
        assert_eq!(it.clone().rev().collect::<Vec<_>>(), b"feX");
    }

    #[test]
    fn mutable_traits() {
        let mut b = HipByt::from(b"ab");
        <HipByt as AsMut<[u8]>>::as_mut(&mut b)[0] = b'x';
        <HipByt as BorrowMut<[u8]>>::borrow_mut(&mut b)[1] = b'y';
        assert_eq!(b, b"xy");
        let mut s = HipStr::from("ab");
        BorrowMut::<str>::borrow_mut(&mut s).make_ascii_uppercase();
        (*s).make_ascii_lowercase();
        assert_eq!(s, "ab");
        assert_eq!(HipStr::from(&String::from("s")), "s");
        assert_eq!(HipStr::from(String::from("m").as_mut_str()), "m");
    }

    #[test]
    #[cfg(feature = "bstr")]
    fn bstr_mutable_traits() {
        let mut b = HipBStr::from("ab");
        (*b).make_ascii_uppercase();
        <HipBStr as AsMut<::bstr::BStr>>::as_mut(&mut b)[0] = b'z';
        <HipBStr as BorrowMut<[u8]>>::borrow_mut(&mut b)[1] = b'q';
        assert_eq!(b.as_bytes(), b"zq");
    }

    #[test]
    fn string_methods() {
        let le: Vec<u8> = "hé".encode_utf16().flat_map(u16::to_le_bytes).collect();
        let be: Vec<u8> = "hé".encode_utf16().flat_map(u16::to_be_bytes).collect();
        assert_eq!(HipStr::from_utf16le(&le).unwrap(), "hé");
        assert_eq!(SmallStr::from_utf16be(&be).unwrap(), "hé");
        assert_eq!(TinyStr::from_utf16le_lossy(&le), "hé");
        assert_eq!(HipStr::from_utf16be_lossy(&be[..3]), "h\u{FFFD}");
        assert_eq!(
            HipStr::from_utf8_lossy_owned(b"a\xffb".to_vec()),
            "a\u{FFFD}b"
        );
        let mut s = HipStr::from("aéb");
        assert_eq!(s.remove(1), 'é');
        assert_eq!(&*s.clone().into_boxed_str(), "ab");
        let d = s.drain(..);
        assert_eq!(<_ as AsRef<str>>::as_ref(&d), "ab");
        assert_eq!(<_ as AsRef<[u8]>>::as_ref(&d), b"ab");
        assert!(format!("{d:?}").contains("Drain"));
        assert_eq!(d.last(), Some('b'));
        assert!(s.is_empty());
    }

    #[test]
    #[should_panic(expected = "cannot remove a char from the end of a string")]
    fn string_remove_at_end() {
        HipStr::from("ab").remove(2);
    }

    #[test]
    #[cfg(all(feature = "std", not(miri)))] // leaks on purpose
    fn leaks() {
        let b: &'static mut [u8] = HipByt::from(LONG.as_bytes()).leak();
        assert_eq!(b, LONG.as_bytes());
        let s: &'static mut str = SmallStr::from(LONG).leak();
        assert_eq!(s, LONG);
        let o: &'static mut std::ffi::OsStr = TinyOsStr::from(LONG).leak();
        assert_eq!(o, LONG);
    }

    #[test]
    #[cfg(feature = "std")]
    fn os_and_path_methods() {
        use std::ffi::{OsStr, OsString};
        use std::io::Write as _;
        use std::path::Path;

        let o: HipOsStr = "x".parse().unwrap();
        assert_eq!(&*o.clone().into_boxed_os_str(), OsStr::new("x"));
        // SAFETY: bytes from `into_encoded_bytes`
        let back =
            unsafe { SmallOsStr::from_encoded_bytes_unchecked(o.clone().into_encoded_bytes()) };
        assert_eq!(back, o);
        assert_eq!(
            HipOsStr::from(Cow::<str>::Owned(String::from("c"))),
            OsStr::new("c")
        );
        let mut cat = HipOsStr::new();
        cat.extend([OsString::from("a")]);
        cat.extend([Cow::Borrowed(OsStr::new("b"))]);
        assert_eq!(cat, OsStr::new("ab"));

        let mut p: HipPath = "/a".parse().unwrap();
        p.push("b");
        assert!(p.pop());
        assert_eq!(p, Path::new("/a"));
        assert!(!HipPath::from("").add_extension("x"));
        assert_eq!(p.clone().into_string().unwrap(), "/a");
        assert_eq!(&*p.clone().into_boxed_path(), Path::new("/a"));
        assert_eq!(
            HipPath::from(Cow::<str>::Owned(String::from("q"))),
            Path::new("q")
        );
        assert_eq!(
            HipPath::from(Cow::<OsStr>::Owned(OsString::from("r"))),
            Path::new("r")
        );

        let mut w = HipByt::new();
        assert_eq!(w.write(b"abc").unwrap(), 3);
        w.write_all(b"d").unwrap();
        assert_eq!(w, b"abcd");
    }

    #[test]
    #[cfg(all(feature = "std", unix))]
    fn os_and_path_non_utf8() {
        use std::os::unix::ffi::OsStrExt;
        let bad = std::ffi::OsStr::from_bytes(b"\xff");
        assert!(HipOsStr::from(bad).into_string().is_err());
        assert!(HipPath::from(bad).into_string().is_err());
    }
}

/// Paths the other tests miss.
mod gaps {
    use super::*;

    #[cfg(feature = "bstr")]
    #[test]
    fn bstr_accessors() {
        use ::bstr::BStr;
        let b = HipBStr::borrowed(BStr::new(b"ab"));
        assert_eq!(b.as_slice(), b"ab");
        assert_eq!(HipBStr::borrowed_bytes(b"ab"), b);
        let bytes = HipByt::from(&b"ab"[..]);
        let as_bstr: &BStr = bytes.as_ref();
        assert_eq!(as_bstr, BStr::new(b"ab"));
    }

    #[test]
    fn cstr_from_vec_with_nul_unchecked() {
        // SAFETY: one NUL, at the end
        let c = unsafe { HipCStr::from_vec_with_nul_unchecked(b"ab\0".to_vec()) };
        assert_eq!(c.as_bytes(), b"ab");
    }

    #[test]
    fn inline_truncate_at_runtime() {
        let mut s = InlineStr::try_inline("abc").unwrap();
        s.truncate(1);
        assert_eq!(s.as_str(), "a");
        s.truncate(5);
        assert_eq!(s.as_str(), "a");
    }

    #[cfg(feature = "std")]
    #[test]
    fn from_static_at_runtime() {
        assert_eq!(SmallOsStr::from_static("ab").as_os_str(), "ab");
        assert_eq!(
            SmallPath::from_static("a/b").as_path(),
            std::path::Path::new("a/b")
        );
    }

    #[test]
    fn vec_ops_edges() {
        let mut b = HipByt::new();
        b.retain_mut(|_| true);
        b.dedup_by(|_, _| true);
        let mut b = HipByt::from(&b"a"[..]);
        b.dedup_by(|_, _| true);
        assert_eq!(b, &b"a"[..]);
        let mut b = HipByt::from(&b"abc"[..]);
        let mut d = b.drain(..);
        assert_eq!(d.next(), Some(b'a'));
        assert_eq!(d.next_back(), Some(b'c'));
        assert_eq!(d.next_back(), Some(b'b'));
        assert_eq!(d.next_back(), None);
        drop(d);
        // nothing removed: no compaction to finish
        let mut b = HipByt::from(&b"abc"[..]);
        b.dedup_by(|_, _| false);
        assert_eq!(b, &b"abc"[..]);
        // empty str drain from the back
        let mut s = HipStr::from("");
        assert_eq!(s.drain(..).next_back(), None);
    }

    #[cfg(feature = "std")]
    #[test]
    fn compact_panic_keeps_the_rest() {
        let mut b = HipByt::from(&b"abcdef"[..]);
        let r = std::panic::catch_unwind(core::panic::AssertUnwindSafe(|| {
            b.retain(|&x| {
                assert!(x != b'd', "stop");
                x != b'b'
            });
        }));
        assert!(r.is_err());
        assert_eq!(b, &b"acdef"[..]);
    }
}

/// Regressions from the soundness review.
mod review {
    use alloc::vec;

    use super::*;

    #[test]
    #[should_panic(expected = "capacity")]
    fn resize_max_on_narrowed_slice() {
        let a = HipByt::from(vec![0u8; 100]);
        let mut b = a.slice(10..100);
        drop(a);
        // used to reserve nothing (`offset + required` wrapped), then write
        // past the buffer
        b.resize(usize::MAX, 0);
    }

    #[test]
    fn reserve_exact_does_not_double() {
        for mut b in [
            HipByt::from(vec![1u8; 1000]),  // adopted vector
            HipByt::from(&[1u8; 1000][..]), // thin buffer
        ] {
            b.shrink_to_fit();
            let cap = b.capacity();
            b.reserve_exact(1);
            assert!(
                b.capacity() < cap + 2 * size_of::<usize>(),
                "{cap} -> {}",
                b.capacity()
            );
            assert!(b.capacity() >= 1001);
            assert!(b.try_reserve_exact(10).is_ok());
            assert!(b.capacity() < 1011 + 2 * size_of::<usize>());
        }
        // the geometric one still doubles
        let mut b = HipByt::from(&[1u8; 1000][..]);
        b.shrink_to_fit();
        b.reserve(1);
        assert!(b.capacity() >= 2000);
    }
}

/// The performance changes after the review.
mod perf {
    use alloc::format;

    use super::*;

    const LONG: &[u8] = b"a1b2c3d4e5f6g7h8i9j0 and more than the inline capacity";

    #[test]
    fn extract_if_unshares_once_and_lazily() {
        let shared = HipByt::from(LONG);
        let mut b = shared.clone();
        {
            let it = b.extract_if(.., |x| x.is_ascii_digit());
            drop(it);
        }
        assert!(
            core::ptr::eq(b.as_ptr(), shared.as_ptr()),
            "not iterated: still shared"
        );
        let mut it = b.extract_if(.., |x| x.is_ascii_digit());
        assert_eq!(it.next(), Some(b'1'));
        // reads through the value while the pointer is cached
        assert!(format!("{it:?}").contains("remaining"));
        assert_eq!(it.next(), Some(b'2'));
        let rest: Vec<u8> = it.collect();
        assert_eq!(rest, b"34567890");
        assert_eq!(b, &b"abcdefghij and more than the inline capacity"[..]);
        assert_eq!(shared, LONG, "the other handle is untouched");
        // mutation through the filter, a partial run, then drop
        let mut b = HipByt::from(LONG);
        let mut it = b.extract_if(..10, |x| {
            x.make_ascii_uppercase();
            *x == b'2'
        });
        assert_eq!(it.next(), Some(b'2'));
        drop(it);
        assert_eq!(&b[..6], b"A1Bc3d");
    }

    #[test]
    fn extract_if_inline_moved_iterator() {
        // inline bytes live in the value: moving the iterator (retagging its
        // borrow) between calls must not invalidate anything
        let mut b = HipByt::from(b"a1b2c3");
        let mut it = b.extract_if(.., |x| x.is_ascii_digit());
        assert_eq!(it.next(), Some(b'1'));
        let moved = it;
        let rest: Vec<u8> = moved.collect();
        assert_eq!(rest, b"23");
        assert_eq!(b, b"abc");
        let mut s = HipStr::from("aéb");
        s.retain(|c| c != 'é');
        assert_eq!(s, "ab");
    }

    #[test]
    fn string_retain_unshares_once() {
        let shared = HipStr::from("héllo wörld, longer than the inline capacity");
        let mut s = shared.clone();
        s.retain(|c| c.is_ascii());
        assert_eq!(s, "hllo wrld, longer than the inline capacity");
        assert_eq!(shared, "héllo wörld, longer than the inline capacity");
    }

    #[allow(clippy::cast_possible_truncation, reason = "wrapping pattern")]
    fn bytes(n: usize) -> Vec<u8> {
        (0..n).map(|i| i as u8).collect()
    }

    #[test]
    fn into_vec_copies_only_the_view() {
        // shared, shortened view: a copy of the view
        let big = SmallByt::from(bytes(1000));
        let mut s = big.clone();
        s.truncate(100);
        let v = s.into_vec();
        assert_eq!(v, bytes(100));
        assert_eq!(v.capacity(), 100, "only the view copied");
        // unique adopted vector: O(1), truncated
        let mut vec = bytes(1000);
        vec.reserve(24);
        let ptr = vec.as_ptr();
        let mut s = SmallByt::from(vec);
        s.truncate(100);
        let v = s.into_vec();
        assert_eq!((v.as_ptr(), v.len()), (ptr, 100));
        // unique thin buffer (wide, tiny): a copy of the elements only
        let mut w = HipByt::from(&bytes(1000)[..]);
        w.truncate(100);
        assert_eq!(w.into_vec().capacity(), 100);
        let t = TinyByt::from(&bytes(1000)[..]);
        assert_eq!(t.into_vec(), bytes(1000));
        let t = TinyByt::from(bytes(1000));
        assert_eq!(t.into_vec(), bytes(1000));
    }

    #[test]
    fn split_off_shares_wide_buffers() {
        let mut b = HipByt::from(bytes(1000));
        let base = b.as_ptr();
        let tail = b.split_off(10);
        assert_eq!(tail.as_ptr(), base.wrapping_add(10), "O(1), shared");
        assert_eq!(tail, &bytes(1000)[10..]);
        assert_eq!(b, &bytes(10)[..]);
        let mut s = HipStr::from("é".repeat(100));
        let tail = s.split_off(100);
        assert_eq!(tail, "é".repeat(50));
        assert_eq!(s, "é".repeat(50));
        // the unique backend cannot share: copies
        let mut u =
            crate::hip::Hip::<crate::enc::Bytes, crate::repr::Wide<'_, Unique>>::from(bytes(1000));
        let tail = u.split_off(500);
        assert_eq!(tail, &bytes(1000)[500..]);
        // small and tiny: copies
        let mut sm = SmallByt::from(bytes(100));
        assert_eq!(sm.split_off(40), &bytes(100)[40..]);
        assert_eq!(sm, &bytes(40)[..]);
    }

    #[test]
    fn shrink_unique_in_place() {
        // thin buffer
        let mut b = HipByt::with_capacity(1000);
        b.extend_from_slice(&bytes(600));
        b.shrink_to_fit();
        assert!(b.capacity() < 600 + size_of::<usize>());
        assert_eq!(b, &bytes(600)[..]);
        // adopted vector
        let mut v = bytes(600);
        v.reserve_exact(400);
        let mut b = HipByt::from(v);
        b.shrink_to(700);
        assert!((700..1000).contains(&b.capacity()), "{}", b.capacity());
        b.shrink_to_fit();
        assert_eq!(b.capacity(), 600);
        // narrowed wide slice: moved to the front, then shrunk
        let whole = HipByt::from(bytes(1000));
        let mut w = whole.slice(100..700);
        drop(whole);
        w.shrink_to_fit();
        assert_eq!(w.capacity(), 600);
        assert_eq!(w, &bytes(700)[100..]);
        // small view, tiny
        let mut sm = SmallByt::from(bytes(1000));
        sm.truncate(600);
        sm.shrink_to_fit();
        assert!(sm.capacity() < 600 + size_of::<usize>());
        let mut t = TinyByt::with_capacity(1000);
        t.extend_from_slice(&bytes(600));
        t.shrink_to_fit();
        assert!(t.capacity() < 600 + size_of::<usize>());
        assert_eq!(t, &bytes(600)[..]);
    }

    #[test]
    fn shrink_shared() {
        // the whole buffer: left alone
        for mut b in [HipByt::from(bytes(1000)), HipByt::from(&bytes(1000)[..])] {
            b.reserve(0);
            let other = b.clone();
            b.shrink_to_fit();
            assert!(core::ptr::eq(b.as_ptr(), other.as_ptr()), "still shared");
        }
        let t = TinyByt::from(bytes(1000));
        let mut t2 = t.clone();
        t2.shrink_to_fit();
        assert!(core::ptr::eq(t.as_ptr(), t2.as_ptr()));
        // part of it: copied, so that the rest may be freed
        let whole = HipByt::from(bytes(1000));
        let mut part = whole.slice(100..700);
        part.shrink_to_fit();
        assert!(!core::ptr::eq(
            part.as_ptr(),
            whole.as_ptr().wrapping_add(100)
        ));
        assert_eq!(part.capacity(), 600);
        assert_eq!(part, &bytes(700)[100..]);
        let big = SmallByt::from(bytes(1000));
        let mut sm = big.clone();
        sm.truncate(600);
        sm.shrink_to_fit();
        assert!(!core::ptr::eq(sm.as_ptr(), big.as_ptr()));
        assert_eq!(sm, &bytes(600)[..]);
    }
}

/// Borrowing iterators (`drain`, `splice`, `extract_if`, `String`-style
/// `drain`) over every representation, inline and heap, moved between calls.
///
/// Inline bytes live in the value itself, so a pointer cached by an iterator
/// is invalidated when the iterator (holding `&mut` to the value) is moved:
/// Miri reports that as undefined behaviour. Run under Miri.
mod moved_iterators {
    use alloc::borrow::ToOwned;
    use alloc::vec;

    use super::*;

    const SHORT: &[u8] = b"a1b2c3";
    const LONG: &[u8] = b"a1b2c3 and enough bytes to be on the heap, every size";

    /// Advances once, moves the iterator through a function, then finishes.
    fn step_move_finish<I: Iterator>(mut it: I) -> (Option<I::Item>, Vec<I::Item>) {
        let first = it.next();
        let moved = core::convert::identity(it);
        (first, moved.collect())
    }

    macro_rules! bytes_case {
        ($name:ident, $t:ty) => {
            #[test]
            fn $name() {
                for src in [SHORT, LONG] {
                    let expected_rest: Vec<u8> = src
                        .iter()
                        .copied()
                        .filter(|b| !b.is_ascii_digit())
                        .collect();

                    let mut b = <$t>::from(src);
                    let (first, rest) = step_move_finish(b.extract_if(.., |x| x.is_ascii_digit()));
                    assert_eq!(first, Some(b'1'));
                    assert_eq!(rest, b"23");
                    assert_eq!(b, &expected_rest[..]);

                    let mut b = <$t>::from(src);
                    let (first, rest) = step_move_finish(b.drain(1..4));
                    assert_eq!((first, rest), (Some(b'1'), vec![b'b', b'2']));
                    assert_eq!(&b[..3], b"ac3");

                    let mut b = <$t>::from(src);
                    let (first, rest) = step_move_finish(b.splice(0..2, *b"XYZ"));
                    assert_eq!((first, rest), (Some(b'a'), vec![b'1']));
                    assert_eq!(&b[..5], b"XYZb2");

                    // shared: unshared by the iterator, the other handle intact
                    let a = <$t>::from(src);
                    let mut b = a.clone();
                    let _ = step_move_finish(b.extract_if(.., |x| x.is_ascii_digit()));
                    assert_eq!(a, src);
                    assert_eq!(b, &expected_rest[..]);
                }
            }
        };
    }

    bytes_case!(hip_byt, HipByt<'_>);
    bytes_case!(small_byt, SmallByt<'_>);
    bytes_case!(tiny_byt, TinyByt);

    macro_rules! str_case {
        ($name:ident, $t:ty) => {
            #[test]
            fn $name() {
                for src in ["aéb", "aéb and enough text to be on the heap, every size"] {
                    let mut s = <$t>::from(src);
                    let (first, rest) = step_move_finish(s.drain(1..4));
                    assert_eq!((first, rest), (Some('é'), vec!['b']));
                    assert_eq!(s, src[..1].to_owned() + &src[4..]);
                }
            }
        };
    }

    str_case!(hip_str, HipStr<'_>);
    str_case!(small_str, SmallStr<'_>);
    str_case!(tiny_str, TinyStr);
}
