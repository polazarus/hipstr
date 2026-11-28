//! Conversions between families, representations and backends.
//!
//! [`Hip::convert`] and [`Hip::try_convert`] change any of the three at
//! once. They keep the buffer whenever the target can hold it:
//!
//! - **families** share their bytes: a conversion only checks them (for
//!   example, that bytes are UTF-8) and, to or from C strings, adds or drops
//!   the NUL terminator;
//! - **representations** hand over their buffer (see the table below);
//! - **backends** hand over a uniquely owned buffer, by rewriting its
//!   counter in place, and copy a shared one.
//!
//! What a representation keeps without copying:
//!
//! | From ↓ to →           | 3 words (`Hip*`) | 2 words (`Small*`)  | 1 word (`Tiny*`)          |
//! |-----------------------|------------------|---------------------|---------------------------|
//! | inline                | yes              | if it fits          | if it fits                |
//! | borrowed              | yes              | yes                 | copied (never borrows)    |
//! | heap (own buffer)     | yes, any slice   | from its start      | the whole buffer, or unique |
//! | heap (adopted `Vec`)  | yes              | copied              | copied                    |
//!
//! A heap value short enough for the target's inline storage is copied
//! inline, which releases the buffer.
//!
//! Family conversions, by rule (see [`Recode`]):
//!
//! | From ↓ to → | bytes | str | bstr | cstr | osstr | path |
//! |-------------|-------|-----|------|------|-------|------|
//! | bytes       | –     | UTF-8 | ✓  | NUL  | OS    | OS   |
//! | str         | ✓     | –   | ✓    | NUL  | ✓     | ✓    |
//! | bstr        | ✓     | UTF-8 | –  | NUL  | OS    | OS   |
//! | cstr        | ✓     | UTF-8 | ✓  | –    | OS    | OS   |
//! | osstr       | ✓     | UTF-8 | ✓  | NUL  | –     | ✓    |
//! | path        | ✓     | UTF-8 | ✓  | NUL  | ✓     | –    |
//!
//! ✓: always succeeds; UTF-8: fails on invalid UTF-8 ([`Utf8Error`]); NUL:
//! fails on an interior NUL ([`InteriorNulError`]); OS: fails on bytes that
//! are not an OS string of the platform ([`OsStrError`], never on Unix and
//! WASI, where any bytes are).
//!
//! [`Hip::convert`]: crate::Hip::convert
//! [`Hip::try_convert`]: crate::Hip::try_convert

use core::convert::Infallible;
use core::fmt;
use core::str::Utf8Error;

use crate::enc::Encoding;

/// A failed conversion: the value, unchanged, and the reason.
#[derive(Clone, PartialEq, Eq)]
pub struct ConvertError<S, W> {
    source: S,
    reason: W,
}

impl<S, W> ConvertError<S, W> {
    pub(crate) const fn new(source: S, reason: W) -> Self {
        Self { source, reason }
    }

    /// The value that failed to convert.
    #[inline]
    #[must_use]
    pub const fn as_source(&self) -> &S {
        &self.source
    }

    /// Why the conversion failed.
    #[inline]
    #[must_use]
    pub const fn reason(&self) -> &W {
        &self.reason
    }

    /// The value that failed to convert, unchanged.
    #[inline]
    #[must_use]
    pub fn into_source(self) -> S {
        self.source
    }

    /// The value and the reason.
    #[inline]
    #[must_use]
    pub fn into_parts(self) -> (S, W) {
        (self.source, self.reason)
    }
}

impl<S, W: fmt::Debug> fmt::Debug for ConvertError<S, W> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ConvertError")
            .field("reason", &self.reason)
            .finish_non_exhaustive()
    }
}

impl<S, W: fmt::Display> fmt::Display for ConvertError<S, W> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.reason.fmt(f)
    }
}

impl<S, W: core::error::Error + 'static> core::error::Error for ConvertError<S, W> {
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)> {
        Some(&self.reason)
    }
}

/// A NUL byte inside a value converted to a C string.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InteriorNulError {
    position: usize,
}

impl InteriorNulError {
    /// Position of the first NUL byte.
    #[inline]
    #[must_use]
    pub const fn nul_position(&self) -> usize {
        self.position
    }
}

impl fmt::Display for InteriorNulError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "interior NUL byte at position {}", self.position)
    }
}

impl core::error::Error for InteriorNulError {}

/// Bytes that are not an OS string of the platform.
///
/// Never happens on Unix and WASI, where any bytes are. Elsewhere, the bytes
/// must be UTF-8: OS strings make no other guarantee on their encoding.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OsStrError {
    pub(crate) valid_up_to: usize,
}

impl OsStrError {
    /// Length of the valid prefix.
    #[inline]
    #[must_use]
    pub const fn valid_up_to(&self) -> usize {
        self.valid_up_to
    }
}

impl fmt::Display for OsStrError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "not a valid OS string from position {}",
            self.valid_up_to
        )
    }
}

impl core::error::Error for OsStrError {}

/// The conversion rule from the family `Self` to the family `E2`.
///
/// The bytes are shared: a conversion only checks the content (the bytes
/// without a terminator) and moves the terminator (adding or dropping the
/// NUL of C strings), so that it keeps the buffer whenever possible.
///
/// # Safety
///
/// Content accepted by [`check`](Self::check), followed by `E2`'s terminator,
/// must be valid for `E2`.
pub unsafe trait Recode<E2: Encoding>: Encoding {
    /// The reason of a failure ([`Infallible`] for conversions that always
    /// succeed).
    type Error;

    /// Checks that the content (the bytes without `Self`'s terminator) is
    /// valid for `E2`.
    ///
    /// # Errors
    ///
    /// If it is not.
    fn check(content: &[u8]) -> Result<(), Self::Error>;
}

#[inline]
#[allow(
    clippy::unnecessary_wraps,
    reason = "same signature as the other checks"
)]
const fn always(_: &[u8]) -> Result<(), Infallible> {
    Ok(())
}

#[inline]
fn utf8(content: &[u8]) -> Result<(), Utf8Error> {
    core::str::from_utf8(content).map(|_| ())
}

#[inline]
fn no_nul(content: &[u8]) -> Result<(), InteriorNulError> {
    content
        .iter()
        .position(|&b| b == 0)
        .map_or(Ok(()), |position| Err(InteriorNulError { position }))
}

/// Any bytes are an OS string on Unix and WASI.
#[cfg(any(unix, target_os = "wasi"))]
#[inline]
#[allow(
    clippy::unnecessary_wraps,
    reason = "same signature as the other checks"
)]
const fn os(_: &[u8]) -> Result<(), OsStrError> {
    Ok(())
}

/// Elsewhere, only UTF-8 is guaranteed to be valid (the encoding of OS
/// strings is otherwise unspecified).
#[cfg(not(any(unix, target_os = "wasi")))]
#[inline]
fn os(content: &[u8]) -> Result<(), OsStrError> {
    core::str::from_utf8(content)
        .map(|_| ())
        .map_err(|e| OsStrError {
            valid_up_to: e.valid_up_to(),
        })
}

/// Implements [`Recode`] for each pair of families, gated by the features
/// of both, and the matching `From` (`from`, infallible) or `TryFrom` (`try`)
/// conversions, by value and by reference (which clones, sharing the buffer
/// when possible), for every representation.
macro_rules! recode {
    ($($f1:literal $e1:ident => $f2:literal $e2:ident : $kind:ident $err:ty = $check:ident;)*) => {$(
        #[cfg(all(feature = $f1, feature = $f2))]
        // SAFETY: the check matches the target family's invariant
        unsafe impl Recode<crate::enc::$e2> for crate::enc::$e1 {
            type Error = $err;

            #[inline]
            fn check(content: &[u8]) -> Result<(), $err> {
                $check(content)
            }
        }

        recode!(@$kind $f1 $e1 => $f2 $e2: $err);
    )*};

    (@same $f1:literal $e1:ident => $f2:literal $e2:ident: $err:ty) => {};

    (@from $f1:literal $e1:ident => $f2:literal $e2:ident: $err:ty) => {
        #[cfg(all(feature = $f1, feature = $f2, any(feature = "hip", feature = "small", feature = "tiny")))]
        impl<'a, R: crate::repr::Repr<'a>> From<crate::hip::Hip<crate::enc::$e1, R>>
            for crate::hip::Hip<crate::enc::$e2, R>
        {
            /// Keeps the buffer (see [`Hip::convert`](crate::Hip::convert)).
            #[inline]
            fn from(value: crate::hip::Hip<crate::enc::$e1, R>) -> Self {
                value.convert()
            }
        }

        #[cfg(all(feature = $f1, feature = $f2, any(feature = "hip", feature = "small", feature = "tiny")))]
        impl<'a, 'h, R: crate::repr::Repr<'a>> From<&'h crate::hip::Hip<crate::enc::$e1, R>>
            for crate::hip::Hip<crate::enc::$e2, R>
        {
            /// Shares the buffer when possible (see
            /// [`Hip::to_converted`](crate::Hip::to_converted)).
            #[inline]
            fn from(value: &'h crate::hip::Hip<crate::enc::$e1, R>) -> Self {
                value.to_converted()
            }
        }
    };

    (@try $f1:literal $e1:ident => $f2:literal $e2:ident: $err:ty) => {
        #[cfg(all(feature = $f1, feature = $f2, any(feature = "hip", feature = "small", feature = "tiny")))]
        impl<'a, R: crate::repr::Repr<'a>> TryFrom<crate::hip::Hip<crate::enc::$e1, R>>
            for crate::hip::Hip<crate::enc::$e2, R>
        {
            type Error = ConvertError<crate::hip::Hip<crate::enc::$e1, R>, $err>;

            /// Keeps the buffer (see [`Hip::try_convert`](crate::Hip::try_convert)).
            #[inline]
            fn try_from(value: crate::hip::Hip<crate::enc::$e1, R>) -> Result<Self, Self::Error> {
                value.try_convert()
            }
        }

        #[cfg(all(feature = $f1, feature = $f2, any(feature = "hip", feature = "small", feature = "tiny")))]
        impl<'a, 'h, R: crate::repr::Repr<'a>> TryFrom<&'h crate::hip::Hip<crate::enc::$e1, R>>
            for crate::hip::Hip<crate::enc::$e2, R>
        {
            type Error = ConvertError<crate::hip::Hip<crate::enc::$e1, R>, $err>;

            /// Shares the buffer when possible (see
            /// [`Hip::try_to_converted`](crate::Hip::try_to_converted)).
            #[inline]
            fn try_from(value: &'h crate::hip::Hip<crate::enc::$e1, R>) -> Result<Self, Self::Error> {
                value.try_to_converted()
            }
        }
    };
}

recode! {
    "bytes" Bytes => "bytes" Bytes: same Infallible = always;
    "bytes" Bytes => "str" Utf8: try Utf8Error = utf8;
    "bytes" Bytes => "bstr" BStr: from Infallible = always;
    "bytes" Bytes => "cstr" CStr: try InteriorNulError = no_nul;
    "bytes" Bytes => "osstr" OsStr: try OsStrError = os;
    "bytes" Bytes => "path" Path: try OsStrError = os;

    "str" Utf8 => "bytes" Bytes: from Infallible = always;
    "str" Utf8 => "str" Utf8: same Infallible = always;
    "str" Utf8 => "bstr" BStr: from Infallible = always;
    "str" Utf8 => "cstr" CStr: try InteriorNulError = no_nul;
    "str" Utf8 => "osstr" OsStr: from Infallible = always;
    "str" Utf8 => "path" Path: from Infallible = always;

    "bstr" BStr => "bytes" Bytes: from Infallible = always;
    "bstr" BStr => "str" Utf8: try Utf8Error = utf8;
    "bstr" BStr => "bstr" BStr: same Infallible = always;
    "bstr" BStr => "cstr" CStr: try InteriorNulError = no_nul;
    "bstr" BStr => "osstr" OsStr: try OsStrError = os;
    "bstr" BStr => "path" Path: try OsStrError = os;

    "cstr" CStr => "bytes" Bytes: from Infallible = always;
    "cstr" CStr => "str" Utf8: try Utf8Error = utf8;
    "cstr" CStr => "bstr" BStr: from Infallible = always;
    "cstr" CStr => "cstr" CStr: same Infallible = always;
    "cstr" CStr => "osstr" OsStr: try OsStrError = os;
    "cstr" CStr => "path" Path: try OsStrError = os;

    "osstr" OsStr => "bytes" Bytes: from Infallible = always;
    "osstr" OsStr => "str" Utf8: try Utf8Error = utf8;
    "osstr" OsStr => "bstr" BStr: from Infallible = always;
    "osstr" OsStr => "cstr" CStr: try InteriorNulError = no_nul;
    "osstr" OsStr => "osstr" OsStr: same Infallible = always;
    "osstr" OsStr => "path" Path: from Infallible = always;

    "path" Path => "bytes" Bytes: from Infallible = always;
    "path" Path => "str" Utf8: try Utf8Error = utf8;
    "path" Path => "bstr" BStr: from Infallible = always;
    "path" Path => "cstr" CStr: try InteriorNulError = no_nul;
    "path" Path => "osstr" OsStr: from Infallible = always;
    "path" Path => "path" Path: same Infallible = always;
}

/// `From` between representations (same family and backend), by value
/// (generic over the family) and by reference (per family: coherence
/// forbids a generic impl next to `From<&E::Slice>`).
macro_rules! repr_from {
    ($($f1:literal [$($l1:lifetime)?] $r1:ident => $f2:literal [$($l2:lifetime)?] $r2:ident;)*) => {
        $(
            #[cfg(all(feature = $f1, feature = $f2))]
            impl<'a, E, B> From<crate::hip::Hip<E, crate::repr::$r1<$($l1,)? B>>>
                for crate::hip::Hip<E, crate::repr::$r2<$($l2,)? B>>
            where
                E: Recode<E, Error = Infallible>,
                B: crate::backend::Backend,
            {
                /// Keeps the buffer when the target can hold it (see
                /// [`Hip::convert`](crate::Hip::convert)).
                #[inline]
                fn from(value: crate::hip::Hip<E, crate::repr::$r1<$($l1,)? B>>) -> Self {
                    value.convert()
                }
            }
        )*
        repr_from!(@ref "bytes" Bytes; $($f1 [$($l1)?] $r1 => $f2 [$($l2)?] $r2;)*);
        repr_from!(@ref "str" Utf8; $($f1 [$($l1)?] $r1 => $f2 [$($l2)?] $r2;)*);
        repr_from!(@ref "bstr" BStr; $($f1 [$($l1)?] $r1 => $f2 [$($l2)?] $r2;)*);
        repr_from!(@ref "cstr" CStr; $($f1 [$($l1)?] $r1 => $f2 [$($l2)?] $r2;)*);
        repr_from!(@ref "osstr" OsStr; $($f1 [$($l1)?] $r1 => $f2 [$($l2)?] $r2;)*);
        repr_from!(@ref "path" Path; $($f1 [$($l1)?] $r1 => $f2 [$($l2)?] $r2;)*);
    };

    (@ref $f:literal $e:ident; $($f1:literal [$($l1:lifetime)?] $r1:ident => $f2:literal [$($l2:lifetime)?] $r2:ident;)*) => {$(
        #[cfg(all(feature = $f, feature = $f1, feature = $f2))]
        impl<'a, 'h, B: crate::backend::Backend>
            From<&'h crate::hip::Hip<crate::enc::$e, crate::repr::$r1<$($l1,)? B>>>
            for crate::hip::Hip<crate::enc::$e, crate::repr::$r2<$($l2,)? B>>
        {
            /// Shares the buffer when the target can hold it (see
            /// [`Hip::to_converted`](crate::Hip::to_converted)).
            #[inline]
            fn from(value: &'h crate::hip::Hip<crate::enc::$e, crate::repr::$r1<$($l1,)? B>>) -> Self {
                value.to_converted()
            }
        }
    )*};
}

repr_from! {
    "hip" ['a] Wide => "small" ['a] Small;
    "hip" ['a] Wide => "tiny" [] Tiny;
    "small" ['a] Small => "hip" ['a] Wide;
    "small" ['a] Small => "tiny" [] Tiny;
    "tiny" [] Tiny => "hip" ['a] Wide;
    "tiny" [] Tiny => "small" ['a] Small;
}

/// Why an inline value failed to convert to another family.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InlineConvertError<W> {
    /// The bytes are not valid for the target family.
    Invalid(W),
    /// The NUL terminator added for a C string does not fit.
    Capacity(crate::inline::CapacityError),
}

impl<W: fmt::Display> fmt::Display for InlineConvertError<W> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Invalid(reason) => reason.fmt(f),
            Self::Capacity(reason) => reason.fmt(f),
        }
    }
}

impl<W: core::error::Error + 'static> core::error::Error for InlineConvertError<W> {
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)> {
        match self {
            Self::Invalid(reason) => Some(reason),
            Self::Capacity(reason) => Some(reason),
        }
    }
}

impl<E: Encoding, const N: usize> crate::inline::Inline<E, N> {
    /// Converts to another family, with the same capacity, in a `const`
    /// context too (see the [module](self) documentation).
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::inline::{InlineByt, InlineStr};
    ///
    /// const B: InlineByt<8> = InlineStr::<8>::inline("abc").convert();
    /// assert_eq!(B.as_slice(), b"abc");
    /// ```
    #[inline]
    #[must_use]
    #[allow(clippy::missing_panics_doc, reason = "cannot fail")]
    pub const fn convert<E2: Encoding>(self) -> crate::inline::Inline<E2, N>
    where
        E: Recode<E2, Error = Infallible>,
    {
        // nothing to check, and infallible conversions never add a
        // terminator: the content fits
        // SAFETY: valid content for `E2` (infallible conversion)
        unsafe { crate::inline::Inline::<E2, N>::try_from_bytes(self.bytes()) }
            .expect("no terminator added")
    }

    /// Converts to another family, with the same capacity, checking the
    /// bytes (see the [module](self) documentation).
    ///
    /// # Errors
    ///
    /// If the bytes are not valid for the target family, or if the NUL
    /// terminator of a C string does not fit; the value is given back.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::convert::InlineConvertError;
    /// use hipstr::inline::{InlineByt, InlineCStr, InlineStr};
    ///
    /// let s: InlineStr<4> = InlineByt::<4>::inline(b"abc").try_convert().unwrap();
    /// assert_eq!(s, "abc");
    /// let c: Result<InlineCStr<4>, _> = s.try_convert();
    /// assert_eq!(c.unwrap().as_bytes_with_nul(), b"abc\0");
    ///
    /// let full = InlineStr::<4>::inline("abcd");
    /// let c: Result<InlineCStr<4>, _> = full.try_convert();
    /// assert!(matches!(c.unwrap_err().reason(), InlineConvertError::Capacity(_)));
    /// ```
    pub fn try_convert<E2: Encoding>(
        self,
    ) -> Result<crate::inline::Inline<E2, N>, ConvertError<Self, InlineConvertError<E::Error>>>
    where
        E: Recode<E2>,
    {
        let content = self.bytes();
        if let Err(reason) = E::check(content) {
            return Err(ConvertError::new(self, InlineConvertError::Invalid(reason)));
        }
        // SAFETY: checked content; the terminator is added
        unsafe { crate::inline::Inline::<E2, N>::try_from_bytes(content) }.ok_or_else(|| {
            ConvertError::new(
                self,
                InlineConvertError::Capacity(crate::inline::CapacityError),
            )
        })
    }
}

#[cfg(any(feature = "hip", feature = "small", feature = "tiny"))]
mod methods {
    use core::convert::Infallible;

    use super::{ConvertError, Recode};
    use crate::enc::Encoding;
    use crate::hip::Hip;
    use crate::repr::{Repr, parts};

    impl<'a, E: Encoding, R: Repr<'a>> Hip<E, R> {
        /// Converts to another family, representation or backend (or several
        /// at once), keeping the buffer whenever the target can hold it (see
        /// the [`convert`](crate::convert) module).
        ///
        /// For the conversions that can fail (for example from bytes to a
        /// string), see [`try_convert`](Self::try_convert).
        ///
        /// # Examples
        ///
        /// ```
        /// use hipstr::{HipByt, HipStr, LocalSmallStr, TinyStr};
        ///
        /// let s = HipStr::from("a string long enough to be on the heap");
        /// let ptr = s.as_ptr();
        ///
        /// // representation: the buffer is kept
        /// let tiny: TinyStr = s.convert();
        /// assert_eq!(tiny.as_ptr(), ptr);
        ///
        /// // backend (`Arc` to `Rc`): kept too, since it is not shared
        /// let local: LocalSmallStr = tiny.convert();
        /// assert_eq!(local.as_ptr(), ptr);
        ///
        /// // family: same bytes
        /// let bytes: HipByt = local.convert();
        /// assert_eq!(bytes.as_ptr(), ptr);
        /// ```
        #[inline]
        #[must_use]
        pub fn convert<E2: Encoding, R2: Repr<'a>>(self) -> Hip<E2, R2>
        where
            E: Recode<E2, Error = Infallible>,
        {
            match self.try_convert() {
                Ok(value) => value,
                Err(error) => match error.reason {},
            }
        }

        /// Converts to another family, representation or backend (or several
        /// at once), checking the bytes for the target family, and keeping
        /// the buffer whenever the target can hold it (see the
        /// [`convert`](crate::convert) module).
        ///
        /// # Errors
        ///
        /// If the bytes are not valid for the target family; the value is
        /// given back, unchanged.
        ///
        /// # Examples
        ///
        /// ```
        /// use hipstr::{HipByt, HipCStr, SmallStr};
        ///
        /// let bytes = HipByt::borrowed(b"hello");
        /// let s: SmallStr = bytes.try_convert().unwrap();
        /// assert_eq!(s, "hello");
        ///
        /// let c: HipCStr = s.try_convert().unwrap();
        /// assert_eq!(c.to_bytes_with_nul(), b"hello\0");
        ///
        /// let bad = HipByt::borrowed(b"\xff");
        /// let result: Result<SmallStr, _> = bad.try_convert();
        /// let error = result.unwrap_err();
        /// assert_eq!(error.reason().valid_up_to(), 0);
        /// assert_eq!(error.into_source().as_slice(), b"\xff");
        /// ```
        pub fn try_convert<E2: Encoding, R2: Repr<'a>>(
            self,
        ) -> Result<Hip<E2, R2>, ConvertError<Self, E::Error>>
        where
            E: Recode<E2>,
        {
            let content = self.repr().len() - E::TERMINATOR;
            if let Err(reason) = E::check(&self.bytes()[..content]) {
                return Err(ConvertError::new(self, reason));
            }
            let mut repr = self.into_repr();
            // the terminator: dropped where views shrink in O(1), added in
            // the target (where the buffer is unique or copied anyway)
            let strip = E::TERMINATOR > E2::TERMINATOR;
            let strip_in_source = strip && R::BORROWS;
            if strip_in_source {
                repr.truncate(content);
            }
            let mut target: R2 = parts::convert(repr);
            if strip && !strip_in_source {
                target.truncate(content);
            }
            if E2::TERMINATOR > E::TERMINATOR {
                target.push(0);
            }
            // SAFETY: checked content, with `E2`'s terminator
            Ok(unsafe { Hip::from_repr(target) })
        }

        /// Converts a clone (sharing the buffer when possible), see
        /// [`convert`](Self::convert).
        #[inline]
        #[must_use]
        pub fn to_converted<E2: Encoding, R2: Repr<'a>>(&self) -> Hip<E2, R2>
        where
            E: Recode<E2, Error = Infallible>,
        {
            self.clone().convert()
        }

        /// Converts a clone (sharing the buffer when possible), see
        /// [`try_convert`](Self::try_convert).
        ///
        /// # Errors
        ///
        /// If the bytes are not valid for the target family (the clone is
        /// given back).
        #[inline]
        pub fn try_to_converted<E2: Encoding, R2: Repr<'a>>(
            &self,
        ) -> Result<Hip<E2, R2>, ConvertError<Self, E::Error>>
        where
            E: Recode<E2>,
        {
            self.clone().try_convert()
        }
    }
}
