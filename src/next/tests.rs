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
                use core::hash::{BuildHasher, Hash};
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
    assert!(s.slice(2..20).is_inline(), "small slices are copied inline");
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
