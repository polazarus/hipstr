//! Differential tests: random operation sequences applied both to std's
//! `Vec<u8>` / `String` and to every size × backend of the byte string and
//! string families, comparing the contents after every step.
//!
//! Values start owned, adopted (from a `Vec`/`String`) or borrowed, and clones
//! are taken and dropped along the way, so that copy-on-write paths are
//! exercised: a mutation must never be visible through a clone.
//!
//! Not run under Miri: too slow, and half of the work would be checking std.
//! The unit tests cover the same code under Miri.

#![cfg(not(miri))]

use std::ops::Range;

use hipstr::backend::{Arc, Rc, Unique};
use hipstr::{bytes, string};
use proptest::prelude::*;

/// Static data for borrowed starts.
static POOL: &str = "Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed \
    do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim \
    veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo";

/// Static UTF-8 data with multi-byte characters.
static UPOOL: &str = "Ça été l'été — ünïcödé ✓ 𝄞 musique, naïve façade, smörgåsbord, \
    jalapeño, crème brûlée, Ελληνικά, Русский, 日本語のテキスト, 한국어 텍스트";

/// No failure files (keeps the repository clean).
fn config() -> ProptestConfig {
    ProptestConfig {
        cases: cases(),
        failure_persistence: None,
        ..ProptestConfig::default()
    }
}

/// Cases per test; `PROPTEST_CASES` overrides the default.
fn cases() -> u32 {
    std::env::var("PROPTEST_CASES")
        .ok()
        .and_then(|n| n.parse().ok())
        .unwrap_or(256)
}

/// Maximal number of operations per case.
const OPS: usize = 48;

/// Maps a raw index to `0..=len`.
fn idx(raw: usize, len: usize) -> usize {
    raw % (len + 1)
}

/// Maps two raw indices to an ordered range within `0..=len`.
fn range(a: usize, b: usize, len: usize) -> Range<usize> {
    let (a, b) = (idx(a, len), idx(b, len));
    a.min(b)..a.max(b)
}

#[derive(Clone, Debug)]
enum Start {
    Slice(Vec<u8>),
    Vec(Vec<u8>),
    Borrowed(usize),
}

fn start() -> impl Strategy<Value = Start> {
    prop_oneof![
        prop::collection::vec(any::<u8>(), 0..64).prop_map(Start::Slice),
        prop::collection::vec(any::<u8>(), 0..64).prop_map(Start::Vec),
        (0..POOL.len()).prop_map(Start::Borrowed),
    ]
}

#[derive(Clone, Debug)]
enum ByteOp {
    Push(u8),
    Pop,
    Insert(usize, u8),
    Remove(usize),
    SwapRemove(usize),
    Truncate(usize),
    Resize(usize, u8),
    Retain(u8),
    Dedup,
    Extend(Vec<u8>),
    ExtendFromWithin(usize, usize),
    Drain(usize, usize, usize),
    Splice(usize, usize, Vec<u8>),
    ExtractIf(usize, usize, u8),
    SplitOff(usize),
    Append(Vec<u8>),
    PopIf(u8),
    Clear,
    Reserve(usize),
    ShrinkToFit,
    MakeAsciiUppercase,
    TakeClone,
    DropClone,
    RoundTrip,
}

fn byte_op() -> impl Strategy<Value = ByteOp> {
    let n = any::<usize>();
    let bytes = || prop::collection::vec(any::<u8>(), 0..40);
    prop_oneof![
        any::<u8>().prop_map(ByteOp::Push),
        Just(ByteOp::Pop),
        (n, any::<u8>()).prop_map(|(i, b)| ByteOp::Insert(i, b)),
        n.prop_map(ByteOp::Remove),
        n.prop_map(ByteOp::SwapRemove),
        n.prop_map(ByteOp::Truncate),
        (0usize..120, any::<u8>()).prop_map(|(n, b)| ByteOp::Resize(n, b)),
        any::<u8>().prop_map(ByteOp::Retain),
        Just(ByteOp::Dedup),
        bytes().prop_map(ByteOp::Extend),
        (n, n).prop_map(|(a, b)| ByteOp::ExtendFromWithin(a, b)),
        (n, n, n).prop_map(|(a, b, k)| ByteOp::Drain(a, b, k)),
        (n, n, bytes()).prop_map(|(a, b, v)| ByteOp::Splice(a, b, v)),
        (n, n, any::<u8>()).prop_map(|(a, b, t)| ByteOp::ExtractIf(a, b, t)),
        n.prop_map(ByteOp::SplitOff),
        bytes().prop_map(ByteOp::Append),
        any::<u8>().prop_map(ByteOp::PopIf),
        Just(ByteOp::Clear),
        (0usize..200).prop_map(ByteOp::Reserve),
        Just(ByteOp::ShrinkToFit),
        Just(ByteOp::MakeAsciiUppercase),
        Just(ByteOp::TakeClone),
        Just(ByteOp::DropClone),
        Just(ByteOp::RoundTrip),
    ]
}

macro_rules! byte_differential {
    ($name:ident, $t:ty, $borrow:ident) => {
        proptest! {
            #![proptest_config(config())]
            #[test]
            fn $name(start in start(), ops in prop::collection::vec(byte_op(), 0..OPS)) {
                type H = $t;
                let (mut h, mut v): (H, Vec<u8>) = match start {
                    Start::Slice(d) => (H::from(d.as_slice()), d),
                    Start::Vec(d) => (H::from(d.clone()), d),
                    Start::Borrowed(at) => {
                        let d = &POOL.as_bytes()[at..];
                        (H::$borrow(d), d.to_vec())
                    }
                };
                let mut clones: Vec<(H, Vec<u8>)> = Vec::new();
                for op in ops {
                    let len = v.len();
                    match op {
                        ByteOp::Push(b) => { h.push(b); v.push(b); }
                        ByteOp::Pop => prop_assert_eq!(h.pop(), v.pop()),
                        ByteOp::Insert(i, b) => {
                            let i = idx(i, len);
                            h.insert(i, b);
                            v.insert(i, b);
                        }
                        ByteOp::Remove(i) if len > 0 => {
                            let i = i % len;
                            prop_assert_eq!(h.remove(i), v.remove(i));
                        }
                        ByteOp::SwapRemove(i) if len > 0 => {
                            let i = i % len;
                            prop_assert_eq!(h.swap_remove(i), v.swap_remove(i));
                        }
                        ByteOp::Remove(_) | ByteOp::SwapRemove(_) => {}
                        ByteOp::Truncate(n) => {
                            let n = idx(n, len);
                            h.truncate(n);
                            v.truncate(n);
                        }
                        ByteOp::Resize(n, b) => { h.resize(n, b); v.resize(n, b); }
                        ByteOp::Retain(m) => {
                            h.retain(|b| b & m != 0);
                            v.retain(|b| b & m != 0);
                        }
                        ByteOp::Dedup => { h.dedup(); v.dedup(); }
                        ByteOp::Extend(d) => {
                            h.extend(d.iter().copied());
                            v.extend(d.iter().copied());
                        }
                        ByteOp::ExtendFromWithin(a, b) => {
                            let r = range(a, b, len);
                            h.extend_from_within(r.clone());
                            v.extend_from_within(r);
                        }
                        ByteOp::Drain(a, b, k) => {
                            let r = range(a, b, len);
                            // consume only part of the iterator
                            let k = k % (r.len() + 1);
                            let hd: Vec<u8> = h.drain(r.clone()).take(k).collect();
                            let vd: Vec<u8> = v.drain(r).take(k).collect();
                            prop_assert_eq!(hd, vd);
                        }
                        ByteOp::Splice(a, b, d) => {
                            let r = range(a, b, len);
                            let hs: Vec<u8> = h.splice(r.clone(), d.iter().copied()).collect();
                            let vs: Vec<u8> = v.splice(r, d.iter().copied()).collect();
                            prop_assert_eq!(hs, vs);
                        }
                        ByteOp::ExtractIf(a, b, t) => {
                            let r = range(a, b, len);
                            let he: Vec<u8> = h.extract_if(r.clone(), |b| *b < t).collect();
                            let ve: Vec<u8> = v.extract_if(r, |b| *b < t).collect();
                            prop_assert_eq!(he, ve);
                        }
                        ByteOp::SplitOff(at) => {
                            let at = idx(at, len);
                            let ht = h.split_off(at);
                            let vt = v.split_off(at);
                            prop_assert_eq!(ht.as_slice(), vt.as_slice());
                        }
                        ByteOp::Append(d) => {
                            let mut other = H::from(d.as_slice());
                            let mut vother = d;
                            h.append(&mut other);
                            v.append(&mut vother);
                            prop_assert!(other.is_empty());
                        }
                        ByteOp::PopIf(t) => {
                            prop_assert_eq!(h.pop_if(|b| *b < t), v.pop_if(|b| *b < t));
                        }
                        ByteOp::Clear => { h.clear(); v.clear(); }
                        ByteOp::Reserve(n) => {
                            h.reserve(n);
                            prop_assert!(h.capacity() >= len + n);
                        }
                        ByteOp::ShrinkToFit => h.shrink_to_fit(),
                        ByteOp::MakeAsciiUppercase => {
                            h.make_ascii_uppercase();
                            v.make_ascii_uppercase();
                        }
                        ByteOp::TakeClone => clones.push((h.clone(), v.clone())),
                        ByteOp::DropClone => { clones.pop(); }
                        ByteOp::RoundTrip => h = H::from(h.into_vec()),
                    }
                    prop_assert_eq!(h.as_slice(), v.as_slice());
                    prop_assert_eq!(h.len(), v.len());
                    prop_assert!(h.capacity() >= h.len());
                    for (c, cv) in &clones {
                        prop_assert_eq!(c.as_slice(), cv.as_slice(), "a clone changed");
                    }
                }
                prop_assert_eq!(h.into_vec(), v);
            }
        }
    };
}

byte_differential!(bytes_wide_arc, bytes::HipByt<'static, Arc>, borrowed);
byte_differential!(bytes_wide_rc, bytes::HipByt<'static, Rc>, borrowed);
byte_differential!(bytes_wide_unique, bytes::HipByt<'static, Unique>, borrowed);
byte_differential!(bytes_small_arc, bytes::SmallByt<'static, Arc>, borrowed);
byte_differential!(bytes_small_rc, bytes::SmallByt<'static, Rc>, borrowed);
byte_differential!(
    bytes_small_unique,
    bytes::SmallByt<'static, Unique>,
    borrowed
);
byte_differential!(bytes_tiny_arc, bytes::TinyByt<Arc>, from);
byte_differential!(bytes_tiny_rc, bytes::TinyByt<Rc>, from);
byte_differential!(bytes_tiny_unique, bytes::TinyByt<Unique>, from);

/// Largest char boundary of `s` that is `<= i`.
fn floor(s: &str, i: usize) -> usize {
    (0..=i.min(s.len()))
        .rev()
        .find(|&i| s.is_char_boundary(i))
        .unwrap()
}

fn char_range(s: &str, a: usize, b: usize) -> Range<usize> {
    let r = range(a, b, s.len());
    floor(s, r.start)..floor(s, r.end)
}

#[derive(Clone, Debug)]
enum StrStart {
    Str(String),
    String(String),
    Borrowed(usize),
}

fn str_start() -> impl Strategy<Value = StrStart> {
    prop_oneof![
        ".{0,24}".prop_map(StrStart::Str),
        ".{0,24}".prop_map(StrStart::String),
        (0..UPOOL.len()).prop_map(StrStart::Borrowed),
    ]
}

#[derive(Clone, Debug)]
enum StrOp {
    Push(char),
    PushStr(String),
    Pop,
    Insert(usize, char),
    InsertStr(usize, String),
    Remove(usize),
    Truncate(usize),
    Retain(u32),
    Drain(usize, usize, usize),
    ReplaceRange(usize, usize, String),
    SplitOff(usize),
    ExtendFromWithin(usize, usize),
    AddAssign(String),
    Clear,
    MakeAsciiLowercase,
    TakeClone,
    DropClone,
    RoundTrip,
}

fn str_op() -> impl Strategy<Value = StrOp> {
    let n = any::<usize>();
    let s = || ".{0,12}";
    prop_oneof![
        any::<char>().prop_map(StrOp::Push),
        s().prop_map(StrOp::PushStr),
        Just(StrOp::Pop),
        (n, any::<char>()).prop_map(|(i, c)| StrOp::Insert(i, c)),
        (n, s()).prop_map(|(i, s)| StrOp::InsertStr(i, s)),
        n.prop_map(StrOp::Remove),
        n.prop_map(StrOp::Truncate),
        any::<u32>().prop_map(StrOp::Retain),
        (n, n, n).prop_map(|(a, b, k)| StrOp::Drain(a, b, k)),
        (n, n, s()).prop_map(|(a, b, s)| StrOp::ReplaceRange(a, b, s)),
        n.prop_map(StrOp::SplitOff),
        (n, n).prop_map(|(a, b)| StrOp::ExtendFromWithin(a, b)),
        s().prop_map(StrOp::AddAssign),
        Just(StrOp::Clear),
        Just(StrOp::MakeAsciiLowercase),
        Just(StrOp::TakeClone),
        Just(StrOp::DropClone),
        Just(StrOp::RoundTrip),
    ]
}

macro_rules! str_differential {
    ($name:ident, $t:ty, $borrow:ident) => {
        proptest! {
            #![proptest_config(config())]
            #[test]
            fn $name(start in str_start(), ops in prop::collection::vec(str_op(), 0..OPS)) {
                type H = $t;
                let (mut h, mut v): (H, String) = match start {
                    StrStart::Str(d) => (H::from(d.as_str()), d),
                    StrStart::String(d) => (H::from(d.clone()), d),
                    StrStart::Borrowed(at) => {
                        let d = &UPOOL[floor(UPOOL, at)..];
                        (H::$borrow(d), d.to_string())
                    }
                };
                let mut clones: Vec<(H, String)> = Vec::new();
                for op in ops {
                    match op {
                        StrOp::Push(c) => { h.push(c); v.push(c); }
                        StrOp::PushStr(s) => { h.push_str(&s); v.push_str(&s); }
                        StrOp::Pop => prop_assert_eq!(h.pop(), v.pop()),
                        StrOp::Insert(i, c) => {
                            let i = floor(&v, i);
                            h.insert(i, c);
                            v.insert(i, c);
                        }
                        StrOp::InsertStr(i, s) => {
                            let i = floor(&v, i);
                            h.insert_str(i, &s);
                            v.insert_str(i, &s);
                        }
                        StrOp::Remove(i) => {
                            let i = floor(&v, i);
                            if i < v.len() {
                                prop_assert_eq!(h.remove(i), v.remove(i));
                            }
                        }
                        StrOp::Truncate(n) => {
                            let n = floor(&v, n);
                            h.truncate(n);
                            v.truncate(n);
                        }
                        StrOp::Retain(m) => {
                            h.retain(|c| (c as u32) & m != 0);
                            v.retain(|c| (c as u32) & m != 0);
                        }
                        StrOp::Drain(a, b, k) => {
                            let r = char_range(&v, a, b);
                            let k = k % (r.len() + 1);
                            let hd: String = h.drain(r.clone()).take(k).collect();
                            let vd: String = v.drain(r).take(k).collect();
                            prop_assert_eq!(hd, vd);
                        }
                        StrOp::ReplaceRange(a, b, s) => {
                            let r = char_range(&v, a, b);
                            h.replace_range(r.clone(), &s);
                            v.replace_range(r, &s);
                        }
                        StrOp::SplitOff(at) => {
                            let at = floor(&v, at);
                            let ht = h.split_off(at);
                            let vt = v.split_off(at);
                            prop_assert_eq!(ht.as_str(), vt.as_str());
                        }
                        StrOp::ExtendFromWithin(a, b) => {
                            let r = char_range(&v, a, b);
                            h.extend_from_within(r.clone());
                            v.extend_from_within(r);
                        }
                        StrOp::AddAssign(s) => { h += &s; v += &s; }
                        StrOp::Clear => { h.clear(); v.clear(); }
                        StrOp::MakeAsciiLowercase => {
                            h.make_ascii_lowercase();
                            v.make_ascii_lowercase();
                        }
                        StrOp::TakeClone => clones.push((h.clone(), v.clone())),
                        StrOp::DropClone => { clones.pop(); }
                        StrOp::RoundTrip => h = H::from(h.into_string()),
                    }
                    prop_assert_eq!(h.as_str(), v.as_str());
                    for (c, cv) in &clones {
                        prop_assert_eq!(c.as_str(), cv.as_str(), "a clone changed");
                    }
                }
                prop_assert_eq!(h.into_string(), v);
            }
        }
    };
}

str_differential!(str_wide_arc, string::HipStr<'static, Arc>, borrowed);
str_differential!(str_wide_rc, string::HipStr<'static, Rc>, borrowed);
str_differential!(str_wide_unique, string::HipStr<'static, Unique>, borrowed);
str_differential!(str_small_arc, string::SmallStr<'static, Arc>, borrowed);
str_differential!(str_small_rc, string::SmallStr<'static, Rc>, borrowed);
str_differential!(
    str_small_unique,
    string::SmallStr<'static, Unique>,
    borrowed
);
str_differential!(str_tiny_arc, string::TinyStr<Arc>, from);
str_differential!(str_tiny_rc, string::TinyStr<Rc>, from);
str_differential!(str_tiny_unique, string::TinyStr<Unique>, from);

/// Wide-only: O(1) slices behave like copies of the sub-slice.
mod slices {
    use super::*;

    proptest! {
        #![proptest_config(config())]
        #[test]
        fn slice_then_mutate(d in prop::collection::vec(any::<u8>(), 0..100),
                             a in any::<usize>(), b in any::<usize>(),
                             ops in prop::collection::vec(byte_op(), 0..OPS)) {
            let h = hipstr::HipByt::from(d.clone());
            let r = range(a, b, d.len());
            let mut s = h.slice(r.clone());
            let mut v = d[r].to_vec();
            for op in ops {
                if let ByteOp::Push(x) | ByteOp::Insert(_, x) = op {
                    s.push(x);
                    v.push(x);
                } else if let ByteOp::Truncate(n) = op {
                    let n = idx(n, v.len());
                    s.truncate(n);
                    v.truncate(n);
                } else if let ByteOp::Extend(e) = op {
                    s.extend_from_slice(&e);
                    v.extend_from_slice(&e);
                }
                prop_assert_eq!(s.as_slice(), v.as_slice());
                prop_assert_eq!(h.as_slice(), d.as_slice(), "the source changed");
            }
        }
    }
}
