//! Fixed-capacity, always-inline values: [`InlineStr`](crate::InlineStr),
//! [`InlineByt`](crate::InlineByt), [`InlineCStr`](crate::InlineCStr), ….
//!
//! An [`Inline<E, N>`] holds up to `N` bytes in place, never allocates, never
//! borrows, and is `Copy`. Most of its API is `const`: construction,
//! accessors and edits (`push`, `push_str`, `pop`, `truncate`, `insert`,
//! `remove`, …) can run at compile time.
//!
//! Its size is `N + 1` bytes (one length byte), with a niche:
//! `Option<InlineStr<N>>` is as large as `InlineStr<N>`. `N` is at most 254.
//! C strings store their NUL terminator in the `N` bytes, so an
//! `InlineCStr<N>` holds up to `N - 1` bytes before it.
//!
//! Edits that do not fit panic; their `try_` versions return
//! [`CapacityError`] and leave the value unchanged.
//!
//! # Examples
//!
//! ```
//! use hipstr::InlineStr;
//!
//! const GREETING: InlineStr = {
//!     let mut s = InlineStr::inline("Hello");
//!     s.push_str(", world");
//!     s.push('!');
//!     s
//! };
//! assert_eq!(GREETING, "Hello, world!");
//! assert_eq!(size_of::<InlineStr>(), 24);
//!
//! // any capacity, up to 254 bytes
//! let mut tiny = hipstr::inline::InlineStr::<4>::new();
//! assert!(tiny.try_push_str("hello").is_err());
//! tiny.push_str("hey");
//! assert_eq!(tiny.remaining_capacity(), 1);
//! ```

use core::borrow::Borrow;
use core::cmp::Ordering;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::num::NonZeroU8;
use core::ops::Deref;

use crate::enc::{self, Bytes, Encoding, Unconstrained, Utf8};
use crate::hip::Hip;
use crate::repr::Repr;

/// The default capacity: as many bytes as `HipStr` holds inline on 64-bit
/// platforms (`InlineStr` is then 24 bytes).
pub const DEFAULT_CAPACITY: usize = 23;

/// Inline string of up to `N` bytes.
#[cfg(feature = "str")]
pub type InlineStr<const N: usize = DEFAULT_CAPACITY> = Inline<Utf8, N>;
/// Inline byte string of up to `N` bytes.
#[cfg(feature = "bytes")]
pub type InlineByt<const N: usize = DEFAULT_CAPACITY> = Inline<Bytes, N>;
/// Inline C string of up to `N` bytes, NUL included.
#[cfg(feature = "cstr")]
pub type InlineCStr<const N: usize = DEFAULT_CAPACITY> = Inline<enc::CStr, N>;
/// Inline `bstr` byte string of up to `N` bytes.
#[cfg(feature = "bstr")]
pub type InlineBStr<const N: usize = DEFAULT_CAPACITY> = Inline<enc::BStr, N>;
/// Inline OS string of up to `N` bytes.
#[cfg(feature = "osstr")]
pub type InlineOsStr<const N: usize = DEFAULT_CAPACITY> = Inline<enc::OsStr, N>;
/// Inline path of up to `N` bytes.
#[cfg(feature = "path")]
pub type InlinePath<const N: usize = DEFAULT_CAPACITY> = Inline<enc::Path, N>;

/// Error of the `try_` methods: the value does not fit.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub struct CapacityError;

impl fmt::Display for CapacityError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("insufficient capacity")
    }
}

impl core::error::Error for CapacityError {}

/// Up to `N` bytes of encoding `E`, stored inline (see the [module](self)).
#[repr(C)]
pub struct Inline<E: Encoding, const N: usize = DEFAULT_CAPACITY> {
    /// Fully initialized (zeroes past the length): the value is `Copy` and
    /// its bytes can be read in `const`.
    data: [u8; N],
    /// Stored length plus one, which gives the niche.
    len: NonZeroU8,
    encoding: PhantomData<E>,
}

impl<E: Encoding, const N: usize> Clone for Inline<E, N> {
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}

impl<E: Encoding, const N: usize> Copy for Inline<E, N> {}

/// Encoding-agnostic `const` core, on the stored bytes (terminator included).
impl<E: Encoding, const N: usize> Inline<E, N> {
    const CHECK: () = {
        assert!(
            N <= 254,
            "the capacity of an inline value is at most 254 bytes"
        );
        assert!(
            N >= E::EMPTY.len(),
            "the capacity cannot hold the empty value"
        );
    };

    /// The empty value.
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        let () = Self::CHECK;
        let mut this = Self {
            data: [0; N],
            len: NonZeroU8::MIN,
            encoding: PhantomData,
        };
        // SAFETY: `EMPTY` fits (checked) and is a valid value
        unsafe { this.set_stored(E::EMPTY) };
        this
    }

    /// Maximal length (excluding the NUL of C strings).
    #[inline]
    #[must_use]
    pub const fn capacity() -> usize {
        N - E::TERMINATOR
    }

    /// Length in bytes (excluding the NUL of C strings).
    #[inline]
    #[must_use]
    pub const fn len(&self) -> usize {
        self.stored_len() - E::TERMINATOR
    }

    /// Whether the value is empty.
    #[inline]
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Bytes that can still be added.
    #[inline]
    #[must_use]
    pub const fn remaining_capacity(&self) -> usize {
        N - self.stored_len()
    }

    /// Whether no byte can be added.
    #[inline]
    #[must_use]
    pub const fn is_full(&self) -> bool {
        self.remaining_capacity() == 0
    }

    /// Raw pointer to the bytes.
    #[inline]
    #[must_use]
    pub const fn as_ptr(&self) -> *const u8 {
        self.data.as_ptr()
    }

    #[inline]
    const fn stored_len(&self) -> usize {
        self.len.get() as usize - 1
    }

    /// The stored bytes (with the terminator of C strings).
    #[inline]
    pub(crate) const fn stored(&self) -> &[u8] {
        self.data.split_at(self.stored_len()).0
    }

    /// The bytes, without the terminator.
    #[inline]
    pub(crate) const fn bytes(&self) -> &[u8] {
        self.data.split_at(self.len()).0
    }

    /// Mutable bytes, without the terminator.
    ///
    /// # Safety
    ///
    /// Writes must keep `E`'s invariant.
    #[inline]
    pub(crate) const unsafe fn bytes_mut(&mut self) -> &mut [u8] {
        let len = self.len();
        self.data.split_at_mut(len).0
    }

    /// Replaces the whole content.
    ///
    /// # Safety
    ///
    /// `stored.len() <= N`, and `stored` must be a valid stored value for `E`
    /// (with its terminator).
    #[inline]
    const unsafe fn set_stored(&mut self, stored: &[u8]) {
        let (head, tail) = self.data.split_at_mut(stored.len());
        head.copy_from_slice(stored);
        // keep the zeroes past the length: equal values have equal bytes
        let mut i = 0;
        while i < tail.len() {
            tail[i] = 0;
            i += 1;
        }
        self.set_stored_len(stored.len());
    }

    #[inline]
    const fn set_stored_len(&mut self, len: usize) {
        debug_assert!(len <= N);
        // SAFETY: `len <= N <= 254`, so `len + 1` is in `1..=255`
        self.len = unsafe { NonZeroU8::new_unchecked(len as u8 + 1) };
    }

    /// Copies `bytes` as a value (adding the terminator), if it fits.
    ///
    /// # Safety
    ///
    /// `bytes` must satisfy `E`'s invariant, terminator excluded.
    #[inline]
    pub(crate) const unsafe fn try_from_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() > Self::capacity() {
            return None;
        }
        let mut this = Self::new();
        this.data.split_at_mut(bytes.len()).0.copy_from_slice(bytes);
        // the terminator (NUL) is already there: the data is zeroed
        this.set_stored_len(bytes.len() + E::TERMINATOR);
        Some(this)
    }

    /// The same value with another capacity, in a `const` context too.
    ///
    /// # Errors
    ///
    /// If the value is longer than `M` allows.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::inline::InlineStr;
    ///
    /// let s = InlineStr::<8>::inline("abc");
    /// let t: InlineStr<4> = s.try_resize().unwrap();
    /// assert_eq!(t, "abc");
    /// assert!(s.try_resize::<2>().is_err());
    /// ```
    #[inline]
    pub const fn try_resize<const M: usize>(self) -> Result<Inline<E, M>, CapacityError> {
        // SAFETY: the bytes of a valid value
        match unsafe { Inline::<E, M>::try_from_bytes(self.bytes()) } {
            Some(value) => Ok(value),
            None => Err(CapacityError),
        }
    }

    /// The same value with a capacity at least as large, in a `const`
    /// context too; a smaller `M` does not compile.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::inline::InlineStr;
    ///
    /// const S: InlineStr<16> = InlineStr::<4>::inline("abc").widen();
    /// assert_eq!(S, "abc");
    /// ```
    ///
    /// ```compile_fail
    /// use hipstr::inline::InlineStr;
    ///
    /// const S: InlineStr<2> = InlineStr::<4>::inline("abc").widen();
    /// ```
    #[inline]
    #[must_use]
    pub const fn widen<const M: usize>(self) -> Inline<E, M> {
        const { assert!(M >= N, "`widen` cannot reduce the capacity") };
        // SAFETY: the bytes of a valid value, which fit (`M >= N`)
        unsafe { Inline::<E, M>::try_from_bytes(self.bytes()) }.expect("fits")
    }

    /// Inserts `bytes` at byte `index` (before the terminator).
    ///
    /// # Safety
    ///
    /// `index <= len`, and the result must satisfy `E`'s invariant.
    pub(crate) const unsafe fn try_insert_bytes(
        &mut self,
        index: usize,
        bytes: &[u8],
    ) -> Result<(), CapacityError> {
        let stored = self.stored_len();
        if bytes.len() > N - stored {
            return Err(CapacityError);
        }
        let data = self.data.as_mut_ptr();
        // SAFETY: `index <= stored` and `stored + bytes.len() <= N`; `bytes`
        // cannot alias `self` (it is uniquely borrowed)
        unsafe {
            core::ptr::copy(
                data.add(index),
                data.add(index + bytes.len()),
                stored - index,
            );
            core::ptr::copy_nonoverlapping(bytes.as_ptr(), data.add(index), bytes.len());
        }
        self.set_stored_len(stored + bytes.len());
        Ok(())
    }

    /// Removes the bytes in `start..end` (before the terminator).
    ///
    /// # Safety
    ///
    /// `start <= end <= len`, and the result must satisfy `E`'s invariant.
    pub(crate) const unsafe fn remove_bytes(&mut self, start: usize, end: usize) {
        let stored = self.stored_len();
        let data = self.data.as_mut_ptr();
        // SAFETY: in bounds (precondition)
        unsafe {
            core::ptr::copy(data.add(end), data.add(start), stored - end);
            // zero the freed tail: equal values have equal bytes
            core::ptr::write_bytes(data.add(stored - (end - start)), 0, end - start);
        }
        self.set_stored_len(stored - (end - start));
    }

    /// Shortens to `len` bytes (before the terminator); no effect if longer.
    ///
    /// # Safety
    ///
    /// The result must satisfy `E`'s invariant.
    #[inline]
    pub(crate) const unsafe fn truncate_bytes(&mut self, len: usize) {
        let cur = self.len();
        if len < cur {
            // SAFETY: precondition, `len <= cur`
            unsafe { self.remove_bytes(len, cur) };
        }
    }

    /// Empties the value.
    #[inline]
    pub const fn clear(&mut self) {
        // SAFETY: shrinking to empty keeps every invariant (the terminator
        // stays)
        unsafe { self.truncate_bytes(0) };
    }

    /// The value as its std borrowed form.
    #[inline]
    pub(crate) fn as_inner(&self) -> &E::Slice {
        // SAFETY: type invariant
        unsafe { E::from_bytes_unchecked(self.stored()) }
    }

    /// Copies `value` inline, if it fits (works for every family, including
    /// OS strings and paths; `try_inline` is the `const` version).
    ///
    /// # Errors
    ///
    /// Returns an error if `value` does not fit.
    #[inline]
    pub fn try_from_inner(value: &E::Slice) -> Result<Self, CapacityError> {
        let stored = E::as_bytes(value);
        if stored.len() > N {
            return Err(CapacityError);
        }
        let mut this = Self::new();
        // SAFETY: a valid stored value, fits
        unsafe { this.set_stored(stored) };
        Ok(this)
    }
}

impl<E: Encoding, const N: usize> Default for Inline<E, N> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<E: Encoding, const N: usize> Deref for Inline<E, N> {
    type Target = E::Slice;

    #[inline]
    fn deref(&self) -> &E::Slice {
        self.as_inner()
    }
}

impl<E: Encoding, const N: usize> AsRef<E::Slice> for Inline<E, N> {
    #[inline]
    fn as_ref(&self) -> &E::Slice {
        self.as_inner()
    }
}

impl<E: Encoding, const N: usize> fmt::Debug for Inline<E, N>
where
    E::Slice: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_inner().fmt(f)
    }
}

impl<E: Encoding, const N: usize> Hash for Inline<E, N>
where
    E::Slice: Hash,
{
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_inner().hash(state);
    }
}

impl<E: Encoding, const N: usize, const M: usize> PartialEq<Inline<E, M>> for Inline<E, N>
where
    E::Slice: PartialEq,
{
    #[inline]
    fn eq(&self, other: &Inline<E, M>) -> bool {
        self.as_inner() == other.as_inner()
    }
}

impl<E: Encoding, const N: usize> Eq for Inline<E, N> where E::Slice: Eq {}

impl<E: Encoding, const N: usize, const M: usize> PartialOrd<Inline<E, M>> for Inline<E, N>
where
    E::Slice: PartialOrd,
{
    #[inline]
    fn partial_cmp(&self, other: &Inline<E, M>) -> Option<Ordering> {
        self.as_inner().partial_cmp(other.as_inner())
    }
}

impl<E: Encoding, const N: usize> Ord for Inline<E, N>
where
    E::Slice: Ord,
{
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_inner().cmp(other.as_inner())
    }
}

impl<'a, E: Encoding, R: Repr<'a>, const N: usize> From<Inline<E, N>> for Hip<E, R> {
    /// Copies the value (inline when it fits the representation).
    #[inline]
    fn from(value: Inline<E, N>) -> Self {
        Self::from(value.as_inner())
    }
}

impl<'a, E: Encoding, R: Repr<'a>, const N: usize> TryFrom<Hip<E, R>> for Inline<E, N> {
    type Error = crate::convert::ConvertError<Hip<E, R>, CapacityError>;

    /// Gives the value back if it does not fit.
    #[inline]
    fn try_from(value: Hip<E, R>) -> Result<Self, Self::Error> {
        Self::try_from_inner(value.as_inner())
            .map_err(|error| crate::convert::ConvertError::new(value, error))
    }
}

impl<'a, E: Encoding, R: Repr<'a>, const N: usize> TryFrom<&Hip<E, R>> for Inline<E, N> {
    type Error = CapacityError;

    #[inline]
    fn try_from(value: &Hip<E, R>) -> Result<Self, CapacityError> {
        Self::try_from_inner(value)
    }
}

impl<'a, E: Encoding, R: Repr<'a>, const N: usize> PartialEq<Inline<E, N>> for Hip<E, R>
where
    E::Slice: PartialEq,
{
    #[inline]
    fn eq(&self, other: &Inline<E, N>) -> bool {
        **self == *other.as_inner()
    }
}

impl<'a, E: Encoding, R: Repr<'a>, const N: usize> PartialEq<Hip<E, R>> for Inline<E, N>
where
    E::Slice: PartialEq,
{
    #[inline]
    fn eq(&self, other: &Hip<E, R>) -> bool {
        *self.as_inner() == **other
    }
}

/// `Borrow`, comparisons with the std types, per family.
macro_rules! family_glue {
    ($enc:ty, $slice:ty; $($other:ty),* $(,)?) => {
        impl<const N: usize> TryFrom<&$slice> for Inline<$enc, N> {
            type Error = CapacityError;

            #[inline]
            fn try_from(value: &$slice) -> Result<Self, CapacityError> {
                Self::try_from_inner(value)
            }
        }

        impl<const N: usize> Borrow<$slice> for Inline<$enc, N> {
            #[inline]
            fn borrow(&self) -> &$slice {
                self.as_inner()
            }
        }

        $(
            impl<const N: usize> PartialEq<$other> for Inline<$enc, N> {
                #[inline]
                fn eq(&self, other: &$other) -> bool {
                    self.as_inner() == <$other as AsRef<$slice>>::as_ref(other)
                }
            }

            impl<const N: usize> PartialEq<Inline<$enc, N>> for $other {
                #[inline]
                fn eq(&self, other: &Inline<$enc, N>) -> bool {
                    <$other as AsRef<$slice>>::as_ref(self) == other.as_inner()
                }
            }

            impl<const N: usize> PartialOrd<$other> for Inline<$enc, N> {
                #[inline]
                fn partial_cmp(&self, other: &$other) -> Option<Ordering> {
                    self.as_inner().partial_cmp(<$other as AsRef<$slice>>::as_ref(other))
                }
            }

            impl<const N: usize> PartialOrd<Inline<$enc, N>> for $other {
                #[inline]
                fn partial_cmp(&self, other: &Inline<$enc, N>) -> Option<Ordering> {
                    <$other as AsRef<$slice>>::as_ref(self).partial_cmp(other.as_inner())
                }
            }
        )*
    };
}

#[cfg(feature = "bytes")]
family_glue!(Bytes, [u8]; [u8], &[u8], alloc::vec::Vec<u8>);
#[cfg(feature = "str")]
family_glue!(Utf8, str; str, &str, alloc::string::String);
#[cfg(feature = "cstr")]
family_glue!(enc::CStr, core::ffi::CStr; core::ffi::CStr, &core::ffi::CStr, alloc::ffi::CString);
#[cfg(feature = "bstr")]
family_glue!(enc::BStr, ::bstr::BStr; ::bstr::BStr, &::bstr::BStr, ::bstr::BString);
#[cfg(feature = "osstr")]
family_glue!(enc::OsStr, std::ffi::OsStr; std::ffi::OsStr, &std::ffi::OsStr, std::ffi::OsString);
#[cfg(feature = "path")]
family_glue!(enc::Path, std::path::Path; std::path::Path, &std::path::Path, std::path::PathBuf);

// ---------------------------------------------------------------------------
// byte strings (`InlineByt`, `InlineBStr`): the `const` `Vec`-like API

impl<E: Unconstrained, const N: usize> Inline<E, N> {
    /// The bytes.
    #[inline]
    #[must_use]
    pub const fn as_slice(&self) -> &[u8] {
        self.bytes()
    }

    /// The bytes, mutably.
    #[inline]
    #[must_use]
    pub const fn as_mut_slice(&mut self) -> &mut [u8] {
        // SAFETY: no invariant
        unsafe { self.bytes_mut() }
    }

    /// Copies `bytes`, if they fit.
    #[inline]
    #[must_use]
    pub const fn try_inline(bytes: &[u8]) -> Option<Self> {
        // SAFETY: no invariant
        unsafe { Self::try_from_bytes(bytes) }
    }

    /// Copies `bytes`.
    ///
    /// # Panics
    ///
    /// Panics if `bytes` is longer than the capacity.
    #[inline]
    #[must_use]
    #[track_caller]
    pub const fn inline(bytes: &[u8]) -> Self {
        Self::try_inline(bytes).expect("too long for the inline capacity")
    }

    /// Appends a byte, if it fits.
    ///
    /// # Errors
    ///
    /// Returns an error, leaving the value unchanged, if it is full.
    #[inline]
    pub const fn try_push(&mut self, byte: u8) -> Result<(), CapacityError> {
        self.try_extend_from_slice(&[byte])
    }

    /// Appends a byte.
    ///
    /// # Panics
    ///
    /// Panics if the value is full.
    #[inline]
    #[track_caller]
    pub const fn push(&mut self, byte: u8) {
        assert!(self.try_push(byte).is_ok(), "insufficient capacity");
    }

    /// Appends bytes, if they fit.
    ///
    /// # Errors
    ///
    /// Returns an error, leaving the value unchanged, if they do not fit.
    #[inline]
    pub const fn try_extend_from_slice(&mut self, bytes: &[u8]) -> Result<(), CapacityError> {
        let len = self.len();
        // SAFETY: no invariant, `len <= len`
        unsafe { self.try_insert_bytes(len, bytes) }
    }

    /// Appends bytes.
    ///
    /// # Panics
    ///
    /// Panics if they do not fit.
    #[inline]
    #[track_caller]
    pub const fn extend_from_slice(&mut self, bytes: &[u8]) {
        assert!(
            self.try_extend_from_slice(bytes).is_ok(),
            "insufficient capacity"
        );
    }

    /// Removes and returns the last byte.
    #[inline]
    pub const fn pop(&mut self) -> Option<u8> {
        let len = self.len();
        if len == 0 {
            return None;
        }
        let last = self.bytes()[len - 1];
        // SAFETY: no invariant
        unsafe { self.truncate_bytes(len - 1) };
        Some(last)
    }

    /// Shortens to `len` bytes; no effect if already shorter.
    #[inline]
    pub const fn truncate(&mut self, len: usize) {
        // SAFETY: no invariant
        unsafe { self.truncate_bytes(len) };
    }

    /// Inserts a byte at `index`.
    ///
    /// # Panics
    ///
    /// Panics if `index > len` or if the value is full.
    #[inline]
    #[track_caller]
    pub const fn insert(&mut self, index: usize, byte: u8) {
        assert!(index <= self.len(), "insertion index out of bounds");
        // SAFETY: no invariant, checked index
        assert!(
            unsafe { self.try_insert_bytes(index, &[byte]) }.is_ok(),
            "insufficient capacity"
        );
    }

    /// Removes and returns the byte at `index`.
    ///
    /// # Panics
    ///
    /// Panics if `index >= len`.
    #[inline]
    #[track_caller]
    pub const fn remove(&mut self, index: usize) -> u8 {
        assert!(index < self.len(), "removal index out of bounds");
        let byte = self.bytes()[index];
        // SAFETY: no invariant, checked index
        unsafe { self.remove_bytes(index, index + 1) };
        byte
    }

    /// Removes the byte at `index`, replacing it by the last one.
    ///
    /// # Panics
    ///
    /// Panics if `index >= len`.
    #[inline]
    #[track_caller]
    pub const fn swap_remove(&mut self, index: usize) -> u8 {
        let len = self.len();
        assert!(index < len, "swap_remove index out of bounds");
        let bytes = self.as_mut_slice();
        let byte = bytes[index];
        bytes[index] = bytes[len - 1];
        self.truncate(len - 1);
        byte
    }
}

impl<E: Unconstrained, const N: usize> Extend<u8> for Inline<E, N> {
    /// # Panics
    ///
    /// Panics if the bytes do not fit.
    fn extend<I: IntoIterator<Item = u8>>(&mut self, iter: I) {
        iter.into_iter().for_each(|b| self.push(b));
    }
}

impl<'b, E: Unconstrained, const N: usize> Extend<&'b u8> for Inline<E, N> {
    /// # Panics
    ///
    /// Panics if the bytes do not fit.
    fn extend<I: IntoIterator<Item = &'b u8>>(&mut self, iter: I) {
        iter.into_iter().for_each(|&b| self.push(b));
    }
}

#[cfg(feature = "bstr")]
impl<const N: usize> AsRef<[u8]> for Inline<enc::BStr, N> {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.bytes()
    }
}

impl<E: Unconstrained, const N: usize> AsMut<[u8]> for Inline<E, N> {
    #[inline]
    fn as_mut(&mut self) -> &mut [u8] {
        self.as_mut_slice()
    }
}

impl<const N: usize> core::ops::DerefMut for Inline<Bytes, N> {
    #[inline]
    fn deref_mut(&mut self) -> &mut [u8] {
        self.as_mut_slice()
    }
}

// ---------------------------------------------------------------------------
// strings (`InlineStr`)

/// Length of the UTF-8 character whose first byte is `b`.
const fn utf8_width(b: u8) -> usize {
    if b < 0x80 {
        1
    } else if b < 0xE0 {
        2
    } else if b < 0xF0 {
        3
    } else {
        4
    }
}

/// Decodes the character at the start of `bytes` (valid, non-empty UTF-8).
const fn decode_utf8(bytes: &[u8]) -> char {
    let b0 = bytes[0] as u32;
    let c = match utf8_width(bytes[0]) {
        1 => b0,
        2 => (b0 & 0x1F) << 6 | (bytes[1] as u32 & 0x3F),
        3 => (b0 & 0x0F) << 12 | (bytes[1] as u32 & 0x3F) << 6 | (bytes[2] as u32 & 0x3F),
        _ => {
            (b0 & 0x07) << 18
                | (bytes[1] as u32 & 0x3F) << 12
                | (bytes[2] as u32 & 0x3F) << 6
                | (bytes[3] as u32 & 0x3F)
        }
    };
    // SAFETY: decoded from valid UTF-8
    unsafe { char::from_u32_unchecked(c) }
}

impl<const N: usize> Inline<Utf8, N> {
    /// The string slice.
    #[inline]
    #[must_use]
    pub const fn as_str(&self) -> &str {
        // SAFETY: type invariant
        unsafe { core::str::from_utf8_unchecked(self.bytes()) }
    }

    /// The string slice, mutably.
    #[inline]
    #[must_use]
    pub const fn as_mut_str(&mut self) -> &mut str {
        // SAFETY: `str`'s API keeps UTF-8
        unsafe { core::str::from_utf8_unchecked_mut(self.bytes_mut()) }
    }

    /// The bytes.
    #[inline]
    #[must_use]
    pub const fn as_bytes(&self) -> &[u8] {
        self.bytes()
    }

    /// Copies `s`, if it fits.
    #[inline]
    #[must_use]
    pub const fn try_inline(s: &str) -> Option<Self> {
        // SAFETY: UTF-8
        unsafe { Self::try_from_bytes(s.as_bytes()) }
    }

    /// Copies `s`.
    ///
    /// # Panics
    ///
    /// Panics if `s` is longer than the capacity.
    #[inline]
    #[must_use]
    #[track_caller]
    pub const fn inline(s: &str) -> Self {
        Self::try_inline(s).expect("too long for the inline capacity")
    }

    /// Converts bytes into a string, checking UTF-8.
    ///
    /// # Errors
    ///
    /// Returns an error if the bytes are not UTF-8.
    #[inline]
    pub const fn from_utf8(bytes: Inline<Bytes, N>) -> Result<Self, core::str::Utf8Error> {
        match core::str::from_utf8(bytes.bytes()) {
            // SAFETY: checked UTF-8, same layout
            Ok(_) => Ok(Self {
                data: bytes.data,
                len: bytes.len,
                encoding: PhantomData,
            }),
            Err(e) => Err(e),
        }
    }

    /// Converts into bytes.
    #[inline]
    #[must_use]
    pub const fn into_bytes(self) -> Inline<Bytes, N> {
        Inline {
            data: self.data,
            len: self.len,
            encoding: PhantomData,
        }
    }

    /// Appends a string slice, if it fits.
    ///
    /// # Errors
    ///
    /// Returns an error, leaving the value unchanged, if it does not fit.
    #[inline]
    pub const fn try_push_str(&mut self, s: &str) -> Result<(), CapacityError> {
        let len = self.len();
        // SAFETY: UTF-8 appended to UTF-8
        unsafe { self.try_insert_bytes(len, s.as_bytes()) }
    }

    /// Appends a string slice.
    ///
    /// # Panics
    ///
    /// Panics if it does not fit.
    #[inline]
    #[track_caller]
    pub const fn push_str(&mut self, s: &str) {
        assert!(self.try_push_str(s).is_ok(), "insufficient capacity");
    }

    /// Appends a character, if it fits.
    ///
    /// # Errors
    ///
    /// Returns an error, leaving the value unchanged, if it does not fit.
    #[inline]
    pub const fn try_push(&mut self, ch: char) -> Result<(), CapacityError> {
        self.try_push_str(ch.encode_utf8(&mut [0; 4]))
    }

    /// Appends a character.
    ///
    /// # Panics
    ///
    /// Panics if it does not fit.
    #[inline]
    #[track_caller]
    pub const fn push(&mut self, ch: char) {
        assert!(self.try_push(ch).is_ok(), "insufficient capacity");
    }

    /// Removes and returns the last character.
    #[inline]
    pub const fn pop(&mut self) -> Option<char> {
        let bytes = self.bytes();
        let mut start = bytes.len();
        if start == 0 {
            return None;
        }
        start -= 1;
        // back to the first byte of the last character
        while bytes[start] & 0xC0 == 0x80 {
            start -= 1;
        }
        let ch = decode_utf8(bytes.split_at(start).1);
        // SAFETY: cut at a char boundary
        unsafe { self.truncate_bytes(start) };
        Some(ch)
    }

    /// Shortens to `new_len` bytes; no effect if already shorter.
    ///
    /// # Panics
    ///
    /// Panics if `new_len` is not on a char boundary.
    #[inline]
    #[track_caller]
    pub const fn truncate(&mut self, new_len: usize) {
        if new_len < self.len() {
            assert!(
                self.as_str().is_char_boundary(new_len),
                "new length is not a char boundary"
            );
            // SAFETY: char boundary
            unsafe { self.truncate_bytes(new_len) };
        }
    }

    /// Inserts a string slice at byte `index`, if it fits.
    ///
    /// # Errors
    ///
    /// Returns an error, leaving the value unchanged, if it does not fit.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds or not on a char boundary.
    #[inline]
    #[track_caller]
    pub const fn try_insert_str(&mut self, index: usize, s: &str) -> Result<(), CapacityError> {
        assert!(
            self.as_str().is_char_boundary(index),
            "insertion index is not a char boundary"
        );
        // SAFETY: char boundary, UTF-8 inserted
        unsafe { self.try_insert_bytes(index, s.as_bytes()) }
    }

    /// Inserts a string slice at byte `index`.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds or not on a char boundary, or if
    /// it does not fit.
    #[inline]
    #[track_caller]
    pub const fn insert_str(&mut self, index: usize, s: &str) {
        assert!(
            self.try_insert_str(index, s).is_ok(),
            "insufficient capacity"
        );
    }

    /// Inserts a character at byte `index`.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds or not on a char boundary, or if
    /// it does not fit.
    #[inline]
    #[track_caller]
    pub const fn insert(&mut self, index: usize, ch: char) {
        self.insert_str(index, ch.encode_utf8(&mut [0; 4]));
    }

    /// Removes and returns the character at byte `index`.
    ///
    /// # Panics
    ///
    /// Panics if `index` is not on a char boundary or not before the end.
    #[inline]
    #[track_caller]
    pub const fn remove(&mut self, index: usize) -> char {
        assert!(
            index < self.len() && self.as_str().is_char_boundary(index),
            "removal index is out of bounds or not a char boundary"
        );
        let ch = decode_utf8(self.bytes().split_at(index).1);
        // SAFETY: a whole character
        unsafe { self.remove_bytes(index, index + ch.len_utf8()) };
        ch
    }

    /// Converts ASCII letters to uppercase.
    #[inline]
    pub const fn make_ascii_uppercase(&mut self) {
        self.as_mut_str().make_ascii_uppercase();
    }

    /// Converts ASCII letters to lowercase.
    #[inline]
    pub const fn make_ascii_lowercase(&mut self) {
        self.as_mut_str().make_ascii_lowercase();
    }

    /// Keeps the characters for which `f` returns `true`.
    pub fn retain(&mut self, mut f: impl FnMut(char) -> bool) {
        let mut kept = Self::new();
        for ch in self.as_str().chars() {
            if f(ch) {
                kept.push(ch);
            }
        }
        *self = kept;
    }
}

impl<const N: usize> core::ops::DerefMut for Inline<Utf8, N> {
    #[inline]
    fn deref_mut(&mut self) -> &mut str {
        self.as_mut_str()
    }
}

impl<const N: usize> AsRef<[u8]> for Inline<Utf8, N> {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.bytes()
    }
}

impl<const N: usize> fmt::Display for Inline<Utf8, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.as_str(), f)
    }
}

impl<const N: usize> fmt::Write for Inline<Utf8, N> {
    /// Fails (`fmt::Error`) if the string does not fit.
    #[inline]
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.try_push_str(s).map_err(|_| fmt::Error)
    }
}

impl<const N: usize> core::str::FromStr for Inline<Utf8, N> {
    type Err = CapacityError;

    #[inline]
    fn from_str(s: &str) -> Result<Self, CapacityError> {
        Self::try_inline(s).ok_or(CapacityError)
    }
}

impl<const N: usize> Extend<char> for Inline<Utf8, N> {
    /// # Panics
    ///
    /// Panics if the characters do not fit.
    fn extend<I: IntoIterator<Item = char>>(&mut self, iter: I) {
        iter.into_iter().for_each(|c| self.push(c));
    }
}

impl<'b, const N: usize> Extend<&'b str> for Inline<Utf8, N> {
    /// # Panics
    ///
    /// Panics if the strings do not fit.
    fn extend<I: IntoIterator<Item = &'b str>>(&mut self, iter: I) {
        iter.into_iter().for_each(|s| self.push_str(s));
    }
}

// ---------------------------------------------------------------------------
// C strings (`InlineCStr`)

impl<const N: usize> Inline<enc::CStr, N> {
    /// The C string slice.
    #[inline]
    #[must_use]
    pub const fn as_c_str(&self) -> &core::ffi::CStr {
        // SAFETY: type invariant: ends with the only NUL
        unsafe { core::ffi::CStr::from_bytes_with_nul_unchecked(self.stored()) }
    }

    /// The bytes, without the NUL.
    #[inline]
    #[must_use]
    pub const fn as_bytes(&self) -> &[u8] {
        self.bytes()
    }

    /// The bytes, with the NUL.
    #[inline]
    #[must_use]
    pub const fn as_bytes_with_nul(&self) -> &[u8] {
        self.stored()
    }

    /// Copies a C string, if it fits (NUL included).
    #[inline]
    #[must_use]
    pub const fn try_inline(c: &core::ffi::CStr) -> Option<Self> {
        // SAFETY: NUL-free bytes
        unsafe { Self::try_from_bytes(c.to_bytes()) }
    }

    /// Copies a C string.
    ///
    /// # Panics
    ///
    /// Panics if it does not fit (NUL included).
    #[inline]
    #[must_use]
    #[track_caller]
    pub const fn inline(c: &core::ffi::CStr) -> Self {
        Self::try_inline(c).expect("too long for the inline capacity")
    }

    /// Shortens to `len` bytes (before the NUL); no effect if already
    /// shorter.
    #[inline]
    pub const fn truncate(&mut self, len: usize) {
        // SAFETY: a prefix of a NUL-free sequence is NUL-free
        unsafe { self.truncate_bytes(len) };
    }
}

// ---------------------------------------------------------------------------
// bstr byte strings (`InlineBStr`)

#[cfg(feature = "bstr")]
impl<const N: usize> Inline<enc::BStr, N> {
    /// The `BStr` slice.
    #[inline]
    #[must_use]
    pub const fn as_bstr(&self) -> &::bstr::BStr {
        crate::bstr::bstr_from_bytes(self.bytes())
    }

    /// The bytes.
    #[inline]
    #[must_use]
    pub const fn as_bytes(&self) -> &[u8] {
        self.bytes()
    }
}

#[cfg(feature = "bstr")]
impl<const N: usize> fmt::Display for Inline<enc::BStr, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.as_bstr(), f)
    }
}

// ---------------------------------------------------------------------------
// OS strings and paths (`InlineOsStr`, `InlinePath`): std's conversions are
// not `const`, so these only have the generic `const` core

#[cfg(feature = "osstr")]
impl<const N: usize> Inline<enc::OsStr, N> {
    /// The OS string slice.
    #[inline]
    #[must_use]
    pub fn as_os_str(&self) -> &std::ffi::OsStr {
        self.as_inner()
    }

    /// The encoded bytes (see `OsStr::as_encoded_bytes`).
    #[inline]
    #[must_use]
    pub const fn as_encoded_bytes(&self) -> &[u8] {
        self.bytes()
    }

    /// Appends an OS string, if it fits.
    ///
    /// # Errors
    ///
    /// Returns an error, leaving the value unchanged, if it does not fit.
    pub fn try_push(&mut self, s: impl AsRef<std::ffi::OsStr>) -> Result<(), CapacityError> {
        let len = self.len();
        // SAFETY: concatenated OS strings
        unsafe { self.try_insert_bytes(len, s.as_ref().as_encoded_bytes()) }
    }
}

#[cfg(feature = "path")]
impl<const N: usize> Inline<enc::Path, N> {
    /// The path slice.
    #[inline]
    #[must_use]
    pub fn as_path(&self) -> &std::path::Path {
        self.as_inner()
    }

    /// The encoded bytes (see `OsStr::as_encoded_bytes`).
    #[inline]
    #[must_use]
    pub const fn as_encoded_bytes(&self) -> &[u8] {
        self.bytes()
    }
}

#[cfg(test)]
mod tests {
    use alloc::string::String;

    use super::*;
    use crate::{HipStr, TinyStr};

    /// Most of the API, evaluated at compile time.
    const BUILT: InlineStr = {
        let mut s = InlineStr::inline("héllo");
        s.push(' ');
        s.push_str("wörld");
        assert!(s.try_push_str("this does not fit at all").is_err());
        s.insert(0, '¡');
        s.insert_str(s.len(), "!");
        let c = s.remove(0);
        assert!(c == '¡');
        let last = s.pop();
        assert!(matches!(last, Some('!')));
        s.make_ascii_uppercase();
        s.truncate(6);
        s
    };

    const BYTES: InlineByt<8> = {
        let mut b = InlineByt::<8>::new();
        b.extend_from_slice(b"abc");
        b.push(b'd');
        b.insert(0, b'z');
        let _ = b.remove(1);
        let _ = b.swap_remove(0);
        b.truncate(3);
        b
    };

    const C: InlineCStr<8> = InlineCStr::inline(c"abc");

    #[test]
    fn const_api() {
        assert_eq!(BUILT, "HéLLO");
        assert_eq!(BUILT.as_str(), "HéLLO");
        assert_eq!(BYTES.as_slice(), b"dbc");
        assert_eq!(C.as_c_str(), c"abc");
        assert_eq!(C.as_bytes_with_nul(), b"abc\0");
        assert_eq!(C.len(), 3);
        assert_eq!(InlineCStr::<8>::capacity(), 7);
        assert!(InlineCStr::<4>::try_inline(c"abcd").is_none());
        assert!(InlineCStr::<5>::try_inline(c"abcd").is_some());
    }

    #[test]
    fn sizes_and_defaults() {
        assert_eq!(size_of::<InlineStr>(), 24);
        assert_eq!(size_of::<Option<InlineStr>>(), 24);
        assert_eq!(size_of::<InlineStr<7>>(), 8);
        assert_eq!(size_of::<InlineStr<254>>(), 255);
        assert_eq!(InlineStr::<23>::capacity(), 23);
        let s = crate::InlineStr::new(); // root alias: no annotation needed
        assert!(s.is_empty() && s.remaining_capacity() == 23);
        assert_eq!(InlineStr::<0>::new(), "");
        assert_eq!(InlineCStr::<1>::new().as_c_str(), c"");
    }

    #[test]
    fn edits_and_errors() {
        let mut s = InlineStr::<4>::new();
        s.push_str("ab");
        assert_eq!(s.try_push('é'), Ok(()));
        assert!(s.is_full());
        assert_eq!(s.try_push('x'), Err(CapacityError));
        assert_eq!(s, "abé", "unchanged after a failed push");
        assert_eq!(s.pop(), Some('é'));
        s.clear();
        assert!(s.is_empty());
        // removed bytes are zeroed: equal values have equal bytes
        assert_eq!(s.data, [0; 4]);
        let mut r = InlineStr::<16>::inline("a1b2c3");
        r.retain(|c| c.is_alphabetic());
        assert_eq!(r, "abc");
        let b = InlineStr::<8>::from_utf8(InlineByt::inline(b"ok")).unwrap();
        assert_eq!(b.into_bytes().as_slice(), b"ok");
        assert!(InlineStr::<8>::from_utf8(InlineByt::inline(b"\xff")).is_err());
    }

    #[test]
    #[should_panic(expected = "insufficient capacity")]
    fn push_overflow_panics() {
        InlineStr::<2>::inline("ab").push('c');
    }

    #[test]
    #[should_panic(expected = "not a char boundary")]
    fn truncate_off_boundary_panics() {
        InlineStr::<4>::inline("é").truncate(1);
    }

    #[test]
    fn traits_and_conversions() {
        use core::fmt::Write;
        let mut s: InlineStr = "abc".parse().unwrap();
        write!(s, "{}", 12).unwrap();
        assert_eq!(s, "abc12");
        assert!(write!(InlineStr::<2>::new(), "abc").is_err());
        assert_eq!(alloc::format!("{s}|{s:?}"), "abc12|\"abc12\"");
        s.extend(['x', 'y']);
        s.extend(["z"]);
        assert_eq!(&*s, "abc12xyz");
        assert!(s == String::from("abc12xyz") && "abc12xyz" == s);
        assert!(s < InlineStr::<4>::inline("b"));

        let h: HipStr = s.into();
        assert_eq!(h, "abc12xyz");
        assert!(h == s && s == h);
        let back = InlineStr::<8>::try_from(&h).unwrap();
        assert_eq!(back, s);
        assert!(InlineStr::<4>::try_from(&h).is_err());
        let t: TinyStr = InlineStr::<4>::inline("ab").into();
        assert!(t.is_inline());
        assert_eq!(InlineStr::<8>::try_from("x").unwrap(), "x");

        #[cfg(feature = "std")]
        {
            let mut set = std::collections::HashSet::new();
            set.insert(InlineStr::<8>::inline("k"));
            assert!(set.contains("k"), "hashes like `str`");
        }
    }

    /// The `const` API again at run time (coverage does not see `const`
    /// evaluation), with the traits.
    #[test]
    #[allow(clippy::clone_on_copy, reason = "tests `Clone`")]
    fn runtime_api() {
        let mut b = InlineByt::<6>::default();
        b.extend_from_slice(b"abc");
        b.try_push(b'd').unwrap();
        b.push(b'e');
        assert_eq!(b.try_extend_from_slice(b"xy"), Err(CapacityError));
        b.insert(0, b'z');
        assert!(b.is_full());
        assert_eq!(b.remove(0), b'z');
        assert_eq!(b.swap_remove(0), b'a');
        assert_eq!(b.pop(), Some(b'd'));
        b.truncate(2);
        b.as_mut_slice()[0] = b'E';
        <InlineByt<6> as AsMut<[u8]>>::as_mut(&mut b)[1] = b'B';
        (*b).reverse();
        b.extend([b'1']);
        b.extend(&[b'2']);
        assert_eq!(b.as_slice(), b"BE12");
        assert_eq!(<InlineByt<6> as AsRef<[u8]>>::as_ref(&b), b"BE12");
        assert!(!b.as_ptr().is_null());
        assert!(b == b"BE12".as_slice() && b"BE12".as_slice() == b);
        assert!(b < b"C".as_slice() && b"A".as_slice() < b);
        assert_eq!(b.clone(), b);
        assert_eq!(b.cmp(&b), Ordering::Equal);
        assert_eq!(alloc::format!("{b:?}"), "[66, 69, 49, 50]");
        let mut empty = InlineByt::<2>::new();
        assert_eq!(empty.pop(), None);
        empty.clear();

        let mut s = InlineStr::<16>::inline("héllo");
        s.push(' ');
        assert_eq!(s.try_insert_str(0, "¡"), Ok(()));
        assert_eq!(
            s.try_insert_str(0, "far too long to fit"),
            Err(CapacityError)
        );
        s.insert(s.len(), '!');
        s.insert_str(0, ">");
        assert_eq!(s.remove(0), '>');
        assert_eq!(s.remove(0), '¡');
        assert_eq!(s.pop(), Some('!'));
        assert_eq!(s.pop(), Some(' '));
        s.make_ascii_uppercase();
        assert_eq!(s.as_str(), "HéLLO");
        s.make_ascii_lowercase();
        (*s).make_ascii_uppercase();
        s.as_mut_str().make_ascii_lowercase();
        assert_eq!(s.as_bytes(), "héllo".as_bytes());
        s.truncate(3);
        assert_eq!(s, "hé");
        assert_eq!(<InlineStr<16> as AsRef<[u8]>>::as_ref(&s), "hé".as_bytes());
        assert!(s > "ha" && "ha" < s);
        let mut multi = InlineStr::<16>::inline("a€𝄞");
        assert_eq!(multi.pop(), Some('𝄞'));
        assert_eq!(multi.pop(), Some('€'));
        assert_eq!(InlineStr::<4>::new().pop(), None);

        let c = InlineCStr::<8>::inline(c"abc");
        let mut c2 = c;
        c2.truncate(1);
        assert_eq!(c2.as_c_str(), c"a");
        assert_eq!(c.as_bytes(), b"abc");
        assert!(c == c"abc" && c"abc" == c);
        assert_eq!(InlineCStr::<8>::try_from(c"x").unwrap(), c"x");
        assert_eq!(alloc::format!("{CapacityError}"), "insufficient capacity");
    }

    #[test]
    #[cfg(feature = "bstr")]
    fn runtime_bstr() {
        let b = InlineBStr::<8>::try_from_inner(::bstr::BStr::new("ab")).unwrap();
        assert_eq!(b.as_bstr(), "ab");
        assert_eq!(b.as_bytes(), b"ab");
        assert_eq!(<InlineBStr<8> as AsRef<[u8]>>::as_ref(&b), b"ab");
        assert_eq!(alloc::format!("{b}"), "ab");
    }

    #[test]
    #[cfg(feature = "std")]
    fn runtime_os_and_path() {
        use std::ffi::OsStr;
        use std::path::Path;

        let mut o = InlineOsStr::<8>::try_from_inner(OsStr::new("ab")).unwrap();
        o.try_push("cd").unwrap();
        assert!(o.try_push("too long").is_err());
        assert_eq!(o.as_os_str(), "abcd");
        assert_eq!(o.as_encoded_bytes(), b"abcd");
        assert!(o == OsStr::new("abcd"));
        let p = InlinePath::<8>::try_from_inner(Path::new("/x")).unwrap();
        assert_eq!(p.as_path(), Path::new("/x"));
        assert_eq!(p.as_encoded_bytes(), b"/x");
        assert!(InlinePath::<1>::try_from_inner(Path::new("/x")).is_err());
    }
}
