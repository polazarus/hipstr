//! Comparisons with other types, generated from one table per family.
//!
//! Comparisons between values of the same family (any representation,
//! backend or inline capacity) are generic, in [`hip`](crate::hip) and
//! [`inline`](crate::inline). This table covers the rest, for `Hip` and
//! `Inline` values alike, each pair in both directions, with `PartialEq`
//! and `PartialOrd`:
//!
//! - std types, compared as a view type (for example `str` for
//!   `String`, `Box<str>`, `Cow<str>`, …);
//! - other families, as std compares their std forms: strings with OS strings
//!   (as OS strings), OS strings with paths (as paths, component-wise),
//!   `bstr` byte strings with bytes and strings (as bytes).
//!
//! Two `Hip` values that share their bytes (clones, or borrowed from the same
//! storage) are equal without reading them.

use alloc::borrow::Cow;
use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;
use core::cmp::Ordering;

use crate::enc::{self, Encoding};
use crate::hip::Hip;
use crate::inline::Inline;
use crate::repr::Repr;

/// One pair of types, compared as `$view`, in both directions.
macro_rules! pair {
    // both sides are `Hip` values: shared bytes are equal
    (@shared $a:ident, $b:ident) => {
        crate::hip::same_bytes($a.bytes(), $b.bytes())
    };

    (
        $view:ty; [$($g:tt)*]
        $a:ty => |$x:ident| $va:expr;
        $b:ty => |$y:ident| $vb:expr;
        $($fast:ident)?
    ) => {
        impl<$($g)*> PartialEq<$b> for $a {
            #[inline]
            fn eq(&self, other: &$b) -> bool {
                $(if pair!(@$fast self, other) { return true; })?
                let ($x, $y) = (self, other);
                let (a, b): (&$view, &$view) = ($va, $vb);
                a == b
            }
        }

        impl<$($g)*> PartialEq<$a> for $b {
            #[inline]
            fn eq(&self, other: &$a) -> bool {
                other == self
            }
        }

        impl<$($g)*> PartialOrd<$b> for $a {
            #[inline]
            fn partial_cmp(&self, other: &$b) -> Option<Ordering> {
                $(if pair!(@$fast self, other) { return Some(Ordering::Equal); })?
                let ($x, $y) = (self, other);
                let (a, b): (&$view, &$view) = ($va, $vb);
                a.partial_cmp(b)
            }
        }

        impl<$($g)*> PartialOrd<$a> for $b {
            #[inline]
            fn partial_cmp(&self, other: &$a) -> Option<Ordering> {
                other.partial_cmp(self).map(Ordering::reverse)
            }
        }
    };

}

/// The view of a `Hip` or `Inline` value of family `$e`.
macro_rules! view {
    ($e:ident as $view:ty, $x:expr) => {
        <<enc::$e as Encoding>::Slice as AsRef<$view>>::as_ref($x.as_inner())
    };
}

/// A family's comparisons with std types, as one view type: each listed
/// type, viewed through `AsRef<$view>` (or the given accessor), against both
/// `Hip` and `Inline` values.
macro_rules! with_std {
    ($f:literal $e:ident as $view:ty $(, if $extra:literal)?: $($rest:tt)*) => {
        with_std!(@rows [$f $e $view [$($extra)?]] $($rest)*);
    };

    (@rows $ctx:tt) => {};
    (@rows $ctx:tt [$($g:tt)*] $t:ty = |$v:ident| $acc:expr, $($rest:tt)*) => {
        with_std!(@one $ctx [$($g)*] $t => |$v| $acc);
        with_std!(@rows $ctx $($rest)*);
    };
    (@rows $ctx:tt [$($g:tt)*] $t:ty, $($rest:tt)*) => {
        with_std!(@one $ctx [$($g)*] $t => |v| AsRef::as_ref(v));
        with_std!(@rows $ctx $($rest)*);
    };

    (@one [$f:literal $e:ident $view:ty [$($extra:literal)?]] [$($g:tt)*] $t:ty => |$v:ident| $acc:expr) => {
        #[cfg(all(feature = $f $(, feature = $extra)?))]
        pair! {
            $view; ['a, R: Repr<'a>, $($g)*]
            Hip<enc::$e, R> => |x| view!($e as $view, x);
            $t => |$v| $acc;
        }

        #[cfg(all(feature = $f $(, feature = $extra)?))]
        pair! {
            $view; [const N: usize, $($g)*]
            Inline<enc::$e, N> => |x| view!($e as $view, x);
            $t => |$v| $acc;
        }
    };
}

/// Two families, compared as `$view`: `Hip` and `Inline` values of each, in
/// every combination.
macro_rules! families {
    ($($f1:literal $e1:ident <=> $f2:literal $e2:ident as $view:ty;)*) => {$(
        #[cfg(all(feature = $f1, feature = $f2))]
        pair! {
            $view; ['a, 'b, R1: Repr<'a>, R2: Repr<'b>]
            Hip<enc::$e1, R1> => |x| view!($e1 as $view, x);
            Hip<enc::$e2, R2> => |y| view!($e2 as $view, y);
            shared
        }

        #[cfg(all(feature = $f1, feature = $f2))]
        pair! {
            $view; ['a, R: Repr<'a>, const N: usize]
            Hip<enc::$e1, R> => |x| view!($e1 as $view, x);
            Inline<enc::$e2, N> => |y| view!($e2 as $view, y);
        }

        #[cfg(all(feature = $f1, feature = $f2))]
        pair! {
            $view; ['a, R: Repr<'a>, const N: usize]
            Inline<enc::$e1, N> => |x| view!($e1 as $view, x);
            Hip<enc::$e2, R> => |y| view!($e2 as $view, y);
        }

        #[cfg(all(feature = $f1, feature = $f2))]
        pair! {
            $view; [const N: usize, const M: usize]
            Inline<enc::$e1, N> => |x| view!($e1 as $view, x);
            Inline<enc::$e2, M> => |y| view!($e2 as $view, y);
        }
    )*};
}

// ----- bytes -----

with_std! { "bytes" Bytes as [u8]:
    [] [u8], [] &[u8], [const L: usize] [u8; L], [const L: usize] &[u8; L],
    [] Vec<u8>, [] &Vec<u8>, [] Box<[u8]>, [] &Box<[u8]>, [] Cow<'_, [u8]>, [] &Cow<'_, [u8]>,
}

with_std! { "bytes" Bytes as ::bstr::BStr, if "bstr":
    [] ::bstr::BStr, [] &::bstr::BStr, [] ::bstr::BString, [] &::bstr::BString,
}

// ----- strings -----

with_std! { "str" Utf8 as str:
    [] str, [] &str, [] String, [] &String, [] Box<str>, [] &Box<str>,
    [] Cow<'_, str>, [] &Cow<'_, str>,
}

with_std! { "str" Utf8 as std::ffi::OsStr, if "std":
    [] std::ffi::OsStr, [] &std::ffi::OsStr, [] std::ffi::OsString, [] &std::ffi::OsString,
}

with_std! { "str" Utf8 as ::bstr::BStr, if "bstr":
    [] ::bstr::BStr, [] &::bstr::BStr, [] ::bstr::BString, [] &::bstr::BString,
}

// ----- C strings -----

with_std! { "cstr" CStr as core::ffi::CStr:
    [] core::ffi::CStr, [] &core::ffi::CStr, [] alloc::ffi::CString, [] &alloc::ffi::CString,
    [] Box<core::ffi::CStr>, [] &Box<core::ffi::CStr>,
    [] Cow<'_, core::ffi::CStr>, [] &Cow<'_, core::ffi::CStr>,
}

// ----- bstr byte strings -----

with_std! { "bstr" BStr as ::bstr::BStr:
    [] ::bstr::BStr, [] &::bstr::BStr, [] ::bstr::BString, [] &::bstr::BString,
    [] Cow<'_, ::bstr::BStr>, [] &Cow<'_, ::bstr::BStr>,
}

with_std! { "bstr" BStr as [u8]:
    [] [u8], [] &[u8], [const L: usize] [u8; L], [const L: usize] &[u8; L],
    [] Vec<u8>, [] &Vec<u8>, [] str, [] &str, [] String, [] &String,
}

// ----- OS strings -----

with_std! { "osstr" OsStr as std::ffi::OsStr:
    [] std::ffi::OsStr, [] &std::ffi::OsStr, [] std::ffi::OsString, [] &std::ffi::OsString,
    [] Box<std::ffi::OsStr>, [] &Box<std::ffi::OsStr>,
    [] Cow<'_, std::ffi::OsStr>, [] &Cow<'_, std::ffi::OsStr>,
    [] str, [] &str, [] String, [] &String,
}

with_std! { "osstr" OsStr as std::path::Path:
    [] std::path::Path, [] &std::path::Path, [] std::path::PathBuf, [] &std::path::PathBuf,
    [] Box<std::path::Path>, [] &Box<std::path::Path>,
    [] Cow<'_, std::path::Path>, [] &Cow<'_, std::path::Path>,
}

// ----- paths -----

with_std! { "path" Path as std::path::Path:
    [] std::path::Path, [] &std::path::Path, [] std::path::PathBuf, [] &std::path::PathBuf,
    [] Box<std::path::Path>, [] &Box<std::path::Path>,
    [] Cow<'_, std::path::Path>, [] &Cow<'_, std::path::Path>,
    // OS strings compare as paths, as std does
    [] std::ffi::OsStr, [] &std::ffi::OsStr, [] std::ffi::OsString, [] &std::ffi::OsString,
    [] Cow<'_, std::ffi::OsStr>, [] &Cow<'_, std::ffi::OsStr>,
    [] Box<std::ffi::OsStr> = |v| std::path::Path::new(&**v),
    [] &Box<std::ffi::OsStr> = |v| std::path::Path::new(&***v),
}

// ----- between families -----

families! {
    "str" Utf8 <=> "osstr" OsStr as std::ffi::OsStr;
    "osstr" OsStr <=> "path" Path as std::path::Path;
    "bstr" BStr <=> "bytes" Bytes as [u8];
    "bstr" BStr <=> "str" Utf8 as [u8];
}
