//! Std trait parity: the trait impls of `Vec<u8>`, `String`, `CString`,
//! `OsString` and `PathBuf` that the families did not have yet.
//!
//! Mutable access (`DerefMut`, `AsMut`, `BorrowMut`, `&mut` iteration) is
//! copy-on-write: a borrowed or shared value is copied first, as with the
//! `to_mut_*` methods. It is provided for the families whose slice type is
//! usefully mutable (bytes, `str`, `BStr`).

// ---------------------------------------------------------------------------
// conversions into std's shared and boxed slices

macro_rules! into_smart {
    ($enc:ty => $slice:ty) => {
        impl<'a, R: $crate::repr::Repr<'a>> From<$crate::hip::Hip<$enc, R>>
            for alloc::boxed::Box<$slice>
        {
            #[inline]
            fn from(value: $crate::hip::Hip<$enc, R>) -> Self {
                value.into_owned_std().into()
            }
        }

        impl<'a, R: $crate::repr::Repr<'a>> From<$crate::hip::Hip<$enc, R>>
            for alloc::rc::Rc<$slice>
        {
            #[inline]
            fn from(value: $crate::hip::Hip<$enc, R>) -> Self {
                alloc::rc::Rc::from(value.as_inner())
            }
        }

        impl<'a, R: $crate::repr::Repr<'a>> From<$crate::hip::Hip<$enc, R>>
            for alloc::sync::Arc<$slice>
        {
            #[inline]
            fn from(value: $crate::hip::Hip<$enc, R>) -> Self {
                alloc::sync::Arc::from(value.as_inner())
            }
        }
    };
}

#[cfg(feature = "bytes")]
into_smart!(crate::enc::Bytes => [u8]);
#[cfg(feature = "str")]
into_smart!(crate::enc::Utf8 => str);
#[cfg(feature = "cstr")]
into_smart!(crate::enc::CStr => core::ffi::CStr);
#[cfg(feature = "osstr")]
into_smart!(crate::enc::OsStr => std::ffi::OsStr);
#[cfg(feature = "path")]
into_smart!(crate::enc::Path => std::path::Path);

// ---------------------------------------------------------------------------
// byte strings (bytes and `BStr`)

#[cfg(any(feature = "bytes", feature = "bstr"))]
pub use byte_strings::IntoIter;

#[cfg(any(feature = "bytes", feature = "bstr"))]
mod byte_strings {
    use core::borrow::BorrowMut;
    use core::iter::FusedIterator;
    use core::ops::DerefMut;

    #[cfg(feature = "bytes")]
    use alloc::{ffi::CString, string::String};

    #[cfg(feature = "bstr")]
    use crate::enc;
    #[cfg(feature = "bytes")]
    use crate::enc::Bytes;
    use crate::enc::Unconstrained;
    use crate::hip::Hip;
    use crate::repr::Repr;

    impl<'a, E: Unconstrained, R: Repr<'a>> Extend<u8> for Hip<E, R> {
        fn extend<I: IntoIterator<Item = u8>>(&mut self, iter: I) {
            let iter = iter.into_iter();
            let (lower, _) = iter.size_hint();
            if lower > 0 {
                self.reserve(lower);
            }
            // SAFETY: no invariant
            let repr = unsafe { self.repr_mut() };
            iter.for_each(|b| repr.push(b));
        }
    }

    impl<'a, 'b, E: Unconstrained, R: Repr<'a>> Extend<&'b u8> for Hip<E, R> {
        #[inline]
        fn extend<I: IntoIterator<Item = &'b u8>>(&mut self, iter: I) {
            self.extend(iter.into_iter().copied());
        }
    }

    impl<'a, E: Unconstrained, R: Repr<'a>> FromIterator<u8> for Hip<E, R> {
        fn from_iter<I: IntoIterator<Item = u8>>(iter: I) -> Self {
            let mut result = Self::default();
            result.extend(iter);
            result
        }
    }

    impl<'a, E: Unconstrained, R: Repr<'a>> AsMut<[u8]> for Hip<E, R> {
        #[inline]
        fn as_mut(&mut self) -> &mut [u8] {
            self.to_mut_slice()
        }
    }

    #[cfg(feature = "bytes")]
    impl<'a, R: Repr<'a>> DerefMut for Hip<Bytes, R> {
        /// Copy-on-write: copies a borrowed or shared value first.
        #[inline]
        fn deref_mut(&mut self) -> &mut [u8] {
            self.to_mut_slice()
        }
    }

    #[cfg(feature = "bytes")]
    impl<'a, R: Repr<'a>> BorrowMut<[u8]> for Hip<Bytes, R> {
        #[inline]
        fn borrow_mut(&mut self) -> &mut [u8] {
            self.to_mut_slice()
        }
    }

    #[cfg(feature = "bstr")]
    impl<'a, R: Repr<'a>> DerefMut for Hip<enc::BStr, R> {
        /// Copy-on-write: copies a borrowed or shared value first.
        #[inline]
        fn deref_mut(&mut self) -> &mut ::bstr::BStr {
            ::bstr::ByteSlice::as_bstr_mut(self.to_mut_slice())
        }
    }

    #[cfg(feature = "bstr")]
    impl<'a, R: Repr<'a>> AsMut<::bstr::BStr> for Hip<enc::BStr, R> {
        #[inline]
        fn as_mut(&mut self) -> &mut ::bstr::BStr {
            self
        }
    }

    #[cfg(feature = "bstr")]
    impl<'a, R: Repr<'a>> BorrowMut<[u8]> for Hip<enc::BStr, R> {
        #[inline]
        fn borrow_mut(&mut self) -> &mut [u8] {
            self.to_mut_slice()
        }
    }

    macro_rules! bytes_from {
        ($($(#[$m:meta])* [$($g:tt)*] $t:ty => |$v:ident| $e:expr;)*) => {$(
            $(#[$m])*
            impl<'a, R: Repr<'a>, $($g)*> From<$t> for Hip<Bytes, R> {
                #[inline]
                fn from($v: $t) -> Self {
                    $e
                }
            }
        )*};
    }

    #[cfg(feature = "bytes")]
    bytes_from! {
        [const N: usize] &mut [u8; N] => |v| Self::from_inner(v);
        [const N: usize] [u8; N] => |v| Self::from_inner(&v);
        [] &str => |v| Self::from_inner(v.as_bytes());
        /// Adopts the string's buffer when it does not fit inline.
        [] String => |v| Self::from_owned(v.into_bytes());
        /// Adopts the string's buffer (without the NUL) when it does not fit inline.
        [] CString => |v| Self::from_owned(v.into_bytes());
    }

    impl<'a, E: Unconstrained, R: Repr<'a>, const N: usize> TryFrom<Hip<E, R>> for [u8; N] {
        type Error = Hip<E, R>;

        /// Gives the value back if its length is not `N`.
        #[inline]
        fn try_from(value: Hip<E, R>) -> Result<Self, Self::Error> {
            <[u8; N]>::try_from(value.bytes()).map_err(|_| value)
        }
    }

    #[cfg(feature = "std")]
    impl<'a, E: Unconstrained, R: Repr<'a>> std::io::Write for Hip<E, R> {
        #[inline]
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            self.extend_from_slice(buf);
            Ok(buf.len())
        }

        #[inline]
        fn write_all(&mut self, buf: &[u8]) -> std::io::Result<()> {
            self.extend_from_slice(buf);
            Ok(())
        }

        #[inline]
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }

    /// Owning iterator over the bytes of a byte string, returned by
    /// `IntoIterator::into_iter`.
    pub struct IntoIter<E: Unconstrained, R> {
        hip: Hip<E, R>,
        front: usize,
        back: usize,
    }

    impl<'a, E: Unconstrained, R: Repr<'a>> Clone for IntoIter<E, R> {
        fn clone(&self) -> Self {
            Self {
                hip: self.hip.clone(),
                front: self.front,
                back: self.back,
            }
        }
    }

    impl<'a, E: Unconstrained, R: Repr<'a>> core::fmt::Debug for IntoIter<E, R> {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            f.debug_tuple("IntoIter").field(&self.as_slice()).finish()
        }
    }

    impl<'a, E: Unconstrained, R: Repr<'a>> IntoIter<E, R> {
        /// The bytes not yet yielded.
        #[must_use]
        pub fn as_slice(&self) -> &[u8] {
            &self.hip.bytes()[self.front..self.back]
        }
    }

    impl<'a, E: Unconstrained, R: Repr<'a>> Iterator for IntoIter<E, R> {
        type Item = u8;

        #[inline]
        fn next(&mut self) -> Option<u8> {
            if self.front == self.back {
                return None;
            }
            self.front += 1;
            Some(self.hip.bytes()[self.front - 1])
        }

        #[inline]
        fn size_hint(&self) -> (usize, Option<usize>) {
            let n = self.back - self.front;
            (n, Some(n))
        }
    }

    impl<'a, E: Unconstrained, R: Repr<'a>> DoubleEndedIterator for IntoIter<E, R> {
        #[inline]
        fn next_back(&mut self) -> Option<u8> {
            if self.front == self.back {
                return None;
            }
            self.back -= 1;
            Some(self.hip.bytes()[self.back])
        }
    }

    impl<'a, E: Unconstrained, R: Repr<'a>> ExactSizeIterator for IntoIter<E, R> {}
    impl<'a, E: Unconstrained, R: Repr<'a>> FusedIterator for IntoIter<E, R> {}

    impl<'a, E: Unconstrained, R: Repr<'a>> IntoIterator for Hip<E, R> {
        type Item = u8;
        type IntoIter = IntoIter<E, R>;

        #[inline]
        fn into_iter(self) -> IntoIter<E, R> {
            IntoIter {
                back: self.bytes().len(),
                front: 0,
                hip: self,
            }
        }
    }

    impl<'h, 'a, E: Unconstrained, R: Repr<'a>> IntoIterator for &'h Hip<E, R> {
        type Item = &'h u8;
        type IntoIter = core::slice::Iter<'h, u8>;

        #[inline]
        fn into_iter(self) -> Self::IntoIter {
            self.bytes().iter()
        }
    }

    impl<'h, 'a, E: Unconstrained, R: Repr<'a>> IntoIterator for &'h mut Hip<E, R> {
        type Item = &'h mut u8;
        type IntoIter = core::slice::IterMut<'h, u8>;

        /// Copy-on-write: copies a borrowed or shared value first.
        #[inline]
        fn into_iter(self) -> Self::IntoIter {
            self.to_mut_slice().iter_mut()
        }
    }
}

// ---------------------------------------------------------------------------
// strings

#[cfg(feature = "str")]
mod strings {
    use alloc::borrow::Cow;
    use alloc::boxed::Box;
    use alloc::ffi::CString;
    use alloc::string::String;
    use core::borrow::BorrowMut;
    use core::ops::{Add, AddAssign, DerefMut};

    use crate::enc::Utf8;
    use crate::hip::Hip;
    use crate::repr::Repr;

    impl<'a, R: Repr<'a>> DerefMut for Hip<Utf8, R> {
        /// Copy-on-write: copies a borrowed or shared value first.
        #[inline]
        fn deref_mut(&mut self) -> &mut str {
            self.to_mut_str()
        }
    }

    impl<'a, R: Repr<'a>> AsMut<str> for Hip<Utf8, R> {
        #[inline]
        fn as_mut(&mut self) -> &mut str {
            self.to_mut_str()
        }
    }

    impl<'a, R: Repr<'a>> BorrowMut<str> for Hip<Utf8, R> {
        #[inline]
        fn borrow_mut(&mut self) -> &mut str {
            self.to_mut_str()
        }
    }

    impl<'a, R: Repr<'a>> Add<&str> for Hip<Utf8, R> {
        type Output = Self;

        /// Appends `other` (see `String + &str`).
        #[inline]
        fn add(mut self, other: &str) -> Self {
            self.push_str(other);
            self
        }
    }

    impl<'a, R: Repr<'a>> AddAssign<&str> for Hip<Utf8, R> {
        #[inline]
        fn add_assign(&mut self, other: &str) {
            self.push_str(other);
        }
    }

    impl<'a, R: Repr<'a>> TryFrom<CString> for Hip<Utf8, R> {
        type Error = alloc::ffi::IntoStringError;

        /// Reuses the buffer (without the NUL) when valid UTF-8.
        #[inline]
        fn try_from(value: CString) -> Result<Self, Self::Error> {
            value.into_string().map(Self::from)
        }
    }

    /// `Extend` and `FromIterator` from the string types `String` accepts.
    macro_rules! str_extend {
        ($([$($g:tt)*] $t:ty => |$s:ident, $v:ident| $e:expr;)*) => {$(
            impl<'a, $($g)*> Extend<$t> for Hip<Utf8, R> {
                fn extend<I: IntoIterator<Item = $t>>(&mut self, iter: I) {
                    iter.into_iter().for_each(|$v| {
                        let $s = &mut *self;
                        $e;
                    });
                }
            }

            impl<'a, $($g)*> FromIterator<$t> for Hip<Utf8, R> {
                fn from_iter<I: IntoIterator<Item = $t>>(iter: I) -> Self {
                    let mut result = Self::default();
                    result.extend(iter);
                    result
                }
            }
        )*};
    }

    str_extend! {
        ['c, R: Repr<'a>] &'c char => |s, c| s.push(*c);
        [R: Repr<'a>] String => |s, v| s.push_str(&v);
        [R: Repr<'a>] Box<str> => |s, v| s.push_str(&v);
        ['c, R: Repr<'a>] Cow<'c, str> => |s, v| s.push_str(&v);
        ['b, R: Repr<'a>, R2: Repr<'b>] Hip<Utf8, R2> => |s, v| s.push_str(v.as_inner());
    }
}

// ---------------------------------------------------------------------------
// C strings

#[cfg(feature = "cstr")]
mod c_strings {
    use alloc::ffi::CString;
    use alloc::vec::Vec;
    use core::num::NonZero;

    use crate::enc;
    use crate::hip::Hip;
    use crate::repr::Repr;

    impl<'a, R: Repr<'a>> From<Vec<NonZero<u8>>> for Hip<enc::CStr, R> {
        /// Appends the terminator, reusing the buffer when it does not fit inline.
        #[inline]
        fn from(value: Vec<NonZero<u8>>) -> Self {
            Self::from_owned(CString::from(value))
        }
    }

    impl<'a, R: Repr<'a>> core::str::FromStr for Hip<enc::CStr, R> {
        type Err = alloc::ffi::NulError;

        /// Like `CString::from_str`: fails on an interior NUL.
        #[inline]
        fn from_str(s: &str) -> Result<Self, Self::Err> {
            Self::try_from(s)
        }
    }
}

// ---------------------------------------------------------------------------
// OS strings and paths

#[cfg(feature = "osstr")]
mod os {
    use alloc::borrow::Cow;
    use std::ffi::{OsStr, OsString};
    #[cfg(feature = "path")]
    use std::path::{Path, PathBuf};

    use crate::enc;
    use crate::hip::Hip;
    use crate::repr::Repr;

    macro_rules! os_extend {
        ($([$($g:tt)*] $t:ty => |$s:ident, $v:ident| $e:expr;)*) => {$(
            impl<'a, $($g)*> Extend<$t> for Hip<enc::OsStr, R> {
                fn extend<I: IntoIterator<Item = $t>>(&mut self, iter: I) {
                    iter.into_iter().for_each(|$v| {
                        let $s = &mut *self;
                        $e;
                    });
                }
            }

            impl<'a, $($g)*> FromIterator<$t> for Hip<enc::OsStr, R> {
                fn from_iter<I: IntoIterator<Item = $t>>(iter: I) -> Self {
                    let mut result = Self::default();
                    result.extend(iter);
                    result
                }
            }
        )*};
    }

    os_extend! {
        ['c, R: Repr<'a>] &'c OsStr => |s, v| s.push(v);
        [R: Repr<'a>] OsString => |s, v| s.push(v);
        ['c, R: Repr<'a>] Cow<'c, OsStr> => |s, v| s.push(v);
    }

    impl<'a, R: Repr<'a>> core::str::FromStr for Hip<enc::OsStr, R> {
        type Err = core::convert::Infallible;

        #[inline]
        fn from_str(s: &str) -> Result<Self, Self::Err> {
            Ok(Self::from(s))
        }
    }

    impl<'a, R: Repr<'a>> core::fmt::Write for Hip<enc::OsStr, R> {
        #[inline]
        fn write_str(&mut self, s: &str) -> core::fmt::Result {
            self.push(s);
            Ok(())
        }
    }

    #[cfg(feature = "path")]
    impl<'a, R: Repr<'a>, P: AsRef<Path>> Extend<P> for Hip<enc::Path, R> {
        /// Pushes each path (see `PathBuf::push`).
        fn extend<I: IntoIterator<Item = P>>(&mut self, iter: I) {
            let mut path = self.mutate();
            iter.into_iter().for_each(|p| path.push(p));
        }
    }

    #[cfg(feature = "path")]
    impl<'a, R: Repr<'a>, P: AsRef<Path>> FromIterator<P> for Hip<enc::Path, R> {
        fn from_iter<I: IntoIterator<Item = P>>(iter: I) -> Self {
            Self::from(iter.into_iter().collect::<PathBuf>())
        }
    }

    #[cfg(feature = "path")]
    impl<'a, R: Repr<'a>> core::str::FromStr for Hip<enc::Path, R> {
        type Err = core::convert::Infallible;

        #[inline]
        fn from_str(s: &str) -> Result<Self, Self::Err> {
            Ok(Self::from(s))
        }
    }

    #[cfg(feature = "path")]
    impl<'h, 'a, R: Repr<'a>> IntoIterator for &'h Hip<enc::Path, R> {
        type Item = &'h OsStr;
        type IntoIter = std::path::Iter<'h>;

        #[inline]
        fn into_iter(self) -> Self::IntoIter {
            self.as_path().iter()
        }
    }
}
