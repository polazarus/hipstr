//! `bstr` byte strings: [`HipBStr`], [`SmallBStr`], [`TinyBStr`].
//!
//! Requires the `bstr` feature. These types dereference to [`BStr`], so they
//! get `bstr`'s string-like API (`find`, `lines`, `to_str_lossy`, …) and its
//! `Debug`/`Display`, which show the bytes as text. Conversions with the other
//! byte families ([`HipByt`](crate::HipByt), [`HipStr`](crate::HipStr), …)
//! keep the storage.
//!
//! # Examples
//!
//! ```
//! use bstr::ByteSlice;
//! use hipstr::HipBStr;
//!
//! const GREETING: HipBStr = HipBStr::borrowed_bytes(b"Hello, \xF0\x9F\xA6\x80!");
//! assert_eq!(GREETING.find("!"), Some(11));
//! assert_eq!(format!("{GREETING}"), "Hello, 🦀!");
//! ```

use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

use ::bstr::{BStr, BString};

use super::enc::{self, Bytes, Utf8};
use super::family::{impl_borrowed_ctors, impl_std_glue};
use super::hip::Hip;
use super::repr::Repr;
pub use crate::hip::RefMut;
pub use crate::std_traits::IntoIter;
pub use crate::vec_ops::{Drain, ExtractIf, Splice};

super::generic_aliases!(
    enc::BStr,
    HipBStr,
    SmallBStr,
    TinyBStr,
    "`bstr` byte string"
);

/// `&[u8]` to `&BStr`, in a `const` context.
///
/// `bstr` guarantees that `&BStr` has the same representation as `&[u8]`
/// (`BStr` is `#[repr(transparent)]` over `[u8]`), so this is a cast.
pub(crate) const fn bstr_from_bytes(bytes: &[u8]) -> &BStr {
    // SAFETY: same representation (documented by `bstr`)
    unsafe { &*(core::ptr::from_ref(bytes) as *const BStr) }
}

/// `&BStr` to `&[u8]`, in a `const` context.
const fn bytes_from_bstr(bstr: &BStr) -> &[u8] {
    // SAFETY: same representation (documented by `bstr`)
    unsafe { &*(core::ptr::from_ref(bstr) as *const [u8]) }
}

// `BString` has no `From<Box<BStr>>`
impl_std_glue!(enc::BStr, BStr, BString, no_box);
impl_borrowed_ctors!(enc::BStr, BStr, |value| bytes_from_bstr(value));
super::hip::impl_const_typed_accessors!(enc::BStr, BStr, |b| bstr_from_bytes(b), |v| {
    bytes_from_bstr(v)
});

/// `const` accessors and constructors, per representation.
macro_rules! impl_const_bstr {
    ($(#[$m:meta] [$($lt:lifetime)?] $repr:ty),* $(,)?) => {$(
        #[$m]
        impl<$($lt,)? B: super::backend::Backend> Hip<enc::BStr, $repr> {
            /// The `BStr` slice.
            #[inline]
            #[must_use]
            pub const fn as_bstr(&self) -> &BStr {
                self.as_typed()
            }

            /// The bytes.
            #[inline]
            #[must_use]
            pub const fn as_bytes(&self) -> &[u8] {
                self.repr().as_slice()
            }

            /// The bytes (same as [`as_bytes`](Self::as_bytes), as on `Vec`).
            #[inline]
            #[must_use]
            pub const fn as_slice(&self) -> &[u8] {
                self.repr().as_slice()
            }
        }
    )*};
}

crate::repr::for_each_repr!(impl_const_bstr);

/// `const` borrowing from plain bytes (byte string literals), for the
/// borrowing representations.
macro_rules! impl_borrowed_bytes {
    ($($feat:literal $repr:ident),*) => {$(
        #[cfg(feature = $feat)]
        impl<'a, B: super::backend::Backend> Hip<enc::BStr, super::repr::$repr<'a, B>> {
            /// Borrows bytes without copying, in a `const` context too.
            #[inline]
            #[must_use]
            pub const fn borrowed_bytes(bytes: &'a [u8]) -> Self {
                Self::borrowed(bstr_from_bytes(bytes))
            }
        }
    )*};
}

impl_borrowed_bytes!("hip" Wide, "small" Small);

impl<'a, R: Repr<'a>> Hip<enc::BStr, R> {
    /// Adopts a byte vector (inline if it fits).
    #[cfg(feature = "borsh")]
    #[inline]
    pub(crate) fn from_owned_bytes(bytes: Vec<u8>) -> Self {
        Self::from_owned(BString::new(bytes))
    }

    /// Converts into a `BString`, in O(1) when the value uniquely owns an
    /// adopted buffer, by copying otherwise.
    #[inline]
    #[must_use]
    pub fn into_bstring(self) -> BString {
        self.into_owned_std()
    }

    /// Converts into bytes, keeping the representation (no copy).
    #[inline]
    #[must_use]
    pub const fn into_bytes(self) -> Hip<Bytes, R> {
        // SAFETY: no invariant on bytes
        unsafe { Hip::from_repr(self.into_repr()) }
    }

    /// Converts into a UTF-8 string, keeping the representation (no copy).
    ///
    /// # Errors
    ///
    /// Returns `Err(self)` if the bytes are not valid UTF-8.
    pub fn into_str(self) -> Result<Hip<Utf8, R>, Self> {
        if core::str::from_utf8(self.bytes()).is_ok() {
            // SAFETY: checked UTF-8
            Ok(unsafe { Hip::from_repr(self.into_repr()) })
        } else {
            Err(self)
        }
    }

    /// Mutable access without copying, if inline or uniquely owned.
    #[inline]
    pub fn as_mut_bytes(&mut self) -> Option<&mut [u8]> {
        if self.repr().is_unique() {
            Some(self.to_mut_bytes())
        } else {
            None
        }
    }

    /// Mutable access, copying first if borrowed or shared.
    #[inline]
    #[allow(
        clippy::wrong_self_convention,
        reason = "same name pattern as the other families"
    )]
    pub fn to_mut_bytes(&mut self) -> &mut [u8] {
        // SAFETY: no invariant on bytes
        unsafe { self.repr_mut() }.to_mut_slice()
    }

    /// Appends a byte.
    #[inline]
    pub fn push(&mut self, byte: u8) {
        // SAFETY: no invariant on bytes
        unsafe { self.push_bytes(&[byte]) }
    }

    /// Appends bytes (or a string, through `AsRef<[u8]>`).
    #[inline]
    pub fn push_slice(&mut self, addition: impl AsRef<[u8]>) {
        // SAFETY: no invariant on bytes
        unsafe { self.push_bytes(addition.as_ref()) }
    }

    /// Appends a character, UTF-8 encoded.
    #[inline]
    pub fn push_char(&mut self, ch: char) {
        self.push_slice(ch.encode_utf8(&mut [0; 4]));
    }

    /// Removes and returns the last byte.
    #[inline]
    pub fn pop(&mut self) -> Option<u8> {
        // SAFETY: no invariant on bytes
        unsafe { self.repr_mut() }.pop()
    }

    /// Shortens to `new_len` bytes; no-op if `new_len` is greater than the length.
    #[inline]
    pub fn truncate(&mut self, new_len: usize) {
        // SAFETY: no invariant on bytes
        unsafe { self.truncate_bytes(new_len) }
    }
}

impl<'a, R: Repr<'a>> fmt::Display for Hip<enc::BStr, R> {
    /// Lossy UTF-8, like `BStr`'s `Display`.
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.as_inner(), f)
    }
}

impl<'a, R: Repr<'a>> fmt::Write for Hip<enc::BStr, R> {
    #[inline]
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.push_slice(s);
        Ok(())
    }
}

impl<'a, R: Repr<'a>> AsRef<[u8]> for Hip<enc::BStr, R> {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.bytes()
    }
}

impl<'a, R: Repr<'a>> core::borrow::Borrow<[u8]> for Hip<enc::BStr, R> {
    /// Consistent with `Hash`: `BStr` hashes like `[u8]`.
    #[inline]
    fn borrow(&self) -> &[u8] {
        self.bytes()
    }
}

/// Conversions from plain bytes and strings, copying or adopting like
/// [`HipByt`](crate::HipByt).
macro_rules! impl_from_plain {
    ($($t:ty => |$v:ident| $e:expr),* $(,)?) => {$(
        impl<'a, R: Repr<'a>> From<$t> for Hip<enc::BStr, R> {
            #[inline]
            fn from($v: $t) -> Self {
                $e
            }
        }
    )*};
}

impl_from_plain!(
    &[u8] => |v| Self::from_inner(bstr_from_bytes(v)),
    &str => |v| Self::from_inner(bstr_from_bytes(v.as_bytes())),
    Vec<u8> => |v| Self::from_owned(BString::new(v)),
    String => |v| Self::from_owned(BString::new(v.into_bytes())),
    Box<[u8]> => |v| Self::from_owned(BString::new(v.into_vec())),
);

impl<'a, R: Repr<'a>, const N: usize> From<&[u8; N]> for Hip<enc::BStr, R> {
    #[inline]
    fn from(value: &[u8; N]) -> Self {
        Self::from_inner(bstr_from_bytes(value))
    }
}

impl<'a, R: Repr<'a>> From<Hip<enc::BStr, R>> for Vec<u8> {
    /// O(1) when the value uniquely owns an adopted buffer.
    #[inline]
    fn from(value: Hip<enc::BStr, R>) -> Self {
        value.into_bstring().into()
    }
}

#[cfg(test)]
mod tests {
    use alloc::format;
    use alloc::vec::Vec;
    use core::fmt::Write;

    use ::bstr::{BString, ByteSlice};

    use crate::{HipBStr, HipByt, HipStr, SmallBStr, TinyBStr};

    const LONG: &[u8] = b"a byte string that is definitely longer than any inline capacity";

    #[test]
    fn construct_and_read() {
        for b in [b"".as_slice(), b"ab", LONG, b"\xff\xfe"] {
            let h = SmallBStr::from(b);
            assert_eq!(h.as_bytes(), b);
            assert_eq!(h.as_bstr(), b.as_bstr());
            assert_eq!(h, b);
            assert_eq!(b, h);
            assert_eq!(h, BString::from(b));
            assert_eq!(h.len(), b.len());
        }
        assert_eq!(HipBStr::from("text"), "text");
        assert!(TinyBStr::from(b"ab").is_inline());
        assert!(TinyBStr::from(LONG).is_allocated());
    }

    #[test]
    fn deref_to_bstr_api() {
        let h = HipBStr::from(b"one\ntwo\n\xff".as_slice());
        assert_eq!(h.lines().count(), 3);
        assert_eq!(h.find("two"), Some(4));
        assert_eq!(format!("{h}"), "one\ntwo\n\u{FFFD}");
        assert_eq!(format!("{h:?}"), r#""one\ntwo\n\xff""#);
    }

    #[test]
    fn zero_copy_conversions() {
        let v = LONG.to_vec();
        let ptr = v.as_ptr();
        let b = HipBStr::from(v);
        assert_eq!(b.as_ptr(), ptr);
        let byt: HipByt<'_> = b.clone().into_bytes();
        assert_eq!(byt.as_ptr(), ptr);
        let s: HipStr<'_> = b.clone().into_str().unwrap();
        assert_eq!(s.as_ptr(), ptr);
        assert_eq!(HipBStr::from(s).as_ptr(), ptr);
        drop(byt);
        assert_eq!(b.into_bstring().as_ptr(), ptr);
        assert!(HipBStr::from(b"\xff".as_slice()).into_str().is_err());
    }

    #[test]
    fn mutation_and_consts() {
        const C: SmallBStr<'static> = SmallBStr::borrowed_bytes(b"static");
        const I: TinyBStr = TinyBStr::new();
        let mut m = C.clone();
        assert!(m.is_borrowed());
        m.push_char('é');
        m.push(b'!');
        write!(m, "{}", 1).unwrap();
        assert_eq!(m, "staticé!1");
        assert!(C.is_borrowed(), "copy on write");
        assert!(I.is_empty());
        let collected: TinyBStr = LONG.iter().copied().collect();
        assert_eq!(collected, LONG);
    }

    #[test]
    #[cfg(feature = "std")]
    fn hash_and_borrow_consistency() {
        let mut set = std::collections::HashSet::new();
        set.insert(crate::LocalTinyBStr::from(LONG));
        assert!(set.contains(LONG));
        assert!(set.contains(LONG.as_bstr()));
    }

    #[test]
    fn into_vec() {
        let v: Vec<u8> = TinyBStr::from(LONG).into();
        assert_eq!(v, LONG);
    }
}
