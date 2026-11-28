//! The comparison table: every review finding, both directions.

#![allow(
    clippy::nonminimal_bool,
    clippy::eq_op,
    clippy::cmp_owned,
    clippy::op_ref,
    clippy::manual_assert_eq,
    clippy::redundant_comparisons,
    clippy::suspicious_operation_groupings,
    reason = "exercises each impl, in both directions, with owned operands"
)]

use alloc::borrow::Cow;
use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;
use core::cmp::Ordering;

use crate::inline::{InlineByt, InlineStr};
use crate::{HipByt, HipStr, SmallStr, TinyStr};

#[test]
fn bytes_with_std_types() {
    let h = HipByt::from(b"abc");
    let i = InlineByt::<8>::inline(b"abc");
    // arrays, boxes and cows, for inline values too
    assert!(h == b"abc" && b"abc" == h && i == b"abc" && *b"abc" == i);
    assert!(i == Box::<[u8]>::from(&b"abc"[..]) && Cow::Borrowed(&b"abc"[..]) == i);
    assert!(i == alloc::vec![b'a', b'b', b'c'] && &Vec::from(&b"abc"[..]) == i);
    assert!(i < b"abd" && b"abb" < i);
    assert_eq!(h.partial_cmp(&b"abd"[..]), Some(Ordering::Less));
}

#[test]
fn strings_with_std_types() {
    let i = InlineStr::<8>::inline("abc");
    assert!(i == String::from("abc") && &String::from("abc") == i);
    assert!(i == Box::<str>::from("abc") && Cow::Borrowed("abc") == i);
    assert!("abd" > i && i < "abd");
    #[cfg(feature = "std")]
    {
        use std::ffi::{OsStr, OsString};
        assert!(i == OsStr::new("abc") && OsString::from("abc") == i);
        assert!(HipStr::from("abc") < OsStr::new("abd"));
    }
}

#[test]
fn hip_and_inline_order() {
    let h = SmallStr::from("abc");
    let i = InlineStr::<4>::inline("abd");
    assert!(h < i && i > h);
    assert_eq!(
        h.partial_cmp(&InlineStr::<4>::inline("abc")),
        Some(Ordering::Equal)
    );
}

#[cfg(feature = "std")]
#[test]
fn paths_compare_as_paths() {
    use std::ffi::{OsStr, OsString};
    use std::path::Path;

    use crate::inline::InlinePath;
    use crate::{HipOsStr, HipPath, TinyPath};

    let p = HipPath::from("a//b");
    // every OS string form compares as a path (the review's bug: `Box`)
    assert!(p == OsStr::new("a/b"));
    assert!(p == OsString::from("a/b"));
    assert!(p == Box::<OsStr>::from(OsStr::new("a/b")));
    assert!(&Box::<OsStr>::from(OsStr::new("a/b")) == p);
    assert!(p == Cow::Borrowed(OsStr::new("a/b")));
    let inline = InlinePath::<8>::try_from_inner(Path::new("a//b")).unwrap();
    assert!(inline == Box::<OsStr>::from(OsStr::new("a/b")));

    // between families, any representation, lifetime and capacity
    let os = HipOsStr::from("a/b");
    assert!(p == os && os == p);
    assert_eq!(p.partial_cmp(&os), Some(Ordering::Equal));
    let t = TinyPath::from("a/c");
    assert!(os < t && t > os);
    assert!(inline == os && os == inline);
    // OS strings among themselves: bytes
    assert!(HipOsStr::from("a//b") != os);
}

#[cfg(feature = "std")]
#[test]
fn strings_and_os_strings() {
    use crate::inline::InlineOsStr;
    use crate::{HipOsStr, TinyOsStr};

    let s = HipStr::from("abc");
    let os = TinyOsStr::from("abc");
    assert!(s == os && os == s);
    assert!(HipOsStr::from("abd") > s);
    assert!(InlineOsStr::<4>::try_from_inner(std::ffi::OsStr::new("abc")).unwrap() == s);
    assert!(os == "abc" && "abc" == os && os == String::from("abc"));
    // shared bytes (same buffer): equal without reading them
    let long = HipStr::from("a string long enough to live on the heap");
    let shared: HipOsStr = long.to_converted();
    assert_eq!(shared.as_encoded_bytes().as_ptr(), long.as_ptr());
    assert!(long == shared);
}

#[cfg(feature = "bstr")]
#[test]
fn bstr_with_bytes_and_strings() {
    use ::bstr::{BStr, BString};

    use crate::HipBStr;

    let b = HipBStr::from(&b"abc"[..]);
    assert!(b == HipByt::from(b"abc") && HipByt::from(b"abc") == b);
    assert!(b == HipStr::from("abc") && TinyStr::from("abd") > b);
    assert!(b == "abc" && b == *b"abc");
    assert!(HipByt::from(b"abc") == BStr::new("abc") && BString::from("abd") > HipStr::from("abc"));
    let i = InlineByt::<4>::inline(b"abc");
    assert!(i == BStr::new("abc") && b == i);
}

#[test]
fn as_ref_views() {
    let s = HipStr::from("abc");
    assert_eq!(<HipStr as AsRef<str>>::as_ref(&s), "abc");
    #[cfg(feature = "bstr")]
    {
        let b = crate::HipBStr::from(&b"abc"[..]);
        assert_eq!(<crate::HipBStr as AsRef<[u8]>>::as_ref(&b), b"abc");
    }
}
