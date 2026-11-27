//! `borsh` support for strings, byte strings and C strings, every size, and
//! for their fixed-capacity inline versions.
//!
//! The format is borsh's for `str` / `Vec<u8>` (a `u32` length, then the
//! bytes); C strings are written without their NUL terminator. OS strings
//! and paths have no portable byte encoding, so they are not supported (as in
//! borsh itself).
//!
//! Decoding goes through borsh's own `Vec<u8>`/`String` decoders, whose
//! buffer is then adopted without copying (or inlined when short). Unlike
//! pre-allocating the announced length, this does not trust the length
//! prefix of untrusted input.

use alloc::string::{String, ToString};
use alloc::vec::Vec;

use borsh::io::{self, Error, ErrorKind};
use borsh::{BorshDeserialize, BorshSerialize};

use super::enc::{Bytes, Utf8};
use super::hip::Hip;
use super::repr::Repr;

impl<'a, R: Repr<'a>> BorshSerialize for Hip<Bytes, R> {
    #[inline]
    fn serialize<W: io::Write>(&self, writer: &mut W) -> io::Result<()> {
        self.bytes().serialize(writer)
    }
}

impl<'a, R: Repr<'a>> BorshDeserialize for Hip<Bytes, R> {
    #[inline]
    fn deserialize_reader<Rd: io::Read>(reader: &mut Rd) -> io::Result<Self> {
        Vec::<u8>::deserialize_reader(reader).map(Self::from_owned)
    }
}

impl<'a, R: Repr<'a>> BorshSerialize for Hip<Utf8, R> {
    #[inline]
    fn serialize<W: io::Write>(&self, writer: &mut W) -> io::Result<()> {
        self.bytes().serialize(writer)
    }
}

impl<'a, R: Repr<'a>> BorshDeserialize for Hip<Utf8, R> {
    fn deserialize_reader<Rd: io::Read>(reader: &mut Rd) -> io::Result<Self> {
        let bytes = Vec::<u8>::deserialize_reader(reader)?;
        String::from_utf8(bytes)
            .map(Self::from_owned)
            .map_err(|e| Error::new(ErrorKind::InvalidData, e.to_string()))
    }
}

#[cfg(feature = "bstr")]
impl<'a, R: Repr<'a>> BorshSerialize for Hip<crate::enc::BStr, R> {
    #[inline]
    fn serialize<W: io::Write>(&self, writer: &mut W) -> io::Result<()> {
        self.bytes().serialize(writer)
    }
}

#[cfg(feature = "bstr")]
impl<'a, R: Repr<'a>> BorshDeserialize for Hip<crate::enc::BStr, R> {
    #[inline]
    fn deserialize_reader<Rd: io::Read>(reader: &mut Rd) -> io::Result<Self> {
        Vec::<u8>::deserialize_reader(reader).map(Self::from_owned_bytes)
    }
}

impl<'a, R: Repr<'a>> BorshSerialize for Hip<crate::enc::CStr, R> {
    /// The bytes, without the NUL terminator.
    #[inline]
    fn serialize<W: io::Write>(&self, writer: &mut W) -> io::Result<()> {
        self.as_inner().to_bytes().serialize(writer)
    }
}

impl<'a, R: Repr<'a>> BorshDeserialize for Hip<crate::enc::CStr, R> {
    /// Rejects interior NULs (like `CString::new`).
    fn deserialize_reader<Rd: io::Read>(reader: &mut Rd) -> io::Result<Self> {
        let bytes = Vec::<u8>::deserialize_reader(reader)?;
        alloc::ffi::CString::new(bytes)
            .map(Self::from_owned)
            .map_err(|e| Error::new(ErrorKind::InvalidData, e.to_string()))
    }
}

/// Inline values: same format; decoding reads into a fixed buffer, without
/// allocating, and rejects a length prefix beyond the capacity before reading.
mod inline {
    use super::*;
    use crate::enc::{self, Encoding};
    use crate::inline::Inline;

    /// Validation of decoded bytes (terminator excluded).
    trait Check: Encoding {
        fn check(bytes: &[u8]) -> io::Result<()>;
    }

    impl Check for Bytes {
        fn check(_: &[u8]) -> io::Result<()> {
            Ok(())
        }
    }

    #[cfg(feature = "bstr")]
    impl Check for enc::BStr {
        fn check(_: &[u8]) -> io::Result<()> {
            Ok(())
        }
    }

    impl Check for Utf8 {
        fn check(bytes: &[u8]) -> io::Result<()> {
            core::str::from_utf8(bytes)
                .map(|_| ())
                .map_err(|e| Error::new(ErrorKind::InvalidData, e.to_string()))
        }
    }

    impl Check for enc::CStr {
        fn check(bytes: &[u8]) -> io::Result<()> {
            if bytes.contains(&0) {
                Err(Error::new(ErrorKind::InvalidData, "interior NUL byte"))
            } else {
                Ok(())
            }
        }
    }

    impl<E: Check, const N: usize> BorshSerialize for Inline<E, N> {
        #[inline]
        fn serialize<W: io::Write>(&self, writer: &mut W) -> io::Result<()> {
            self.bytes().serialize(writer)
        }
    }

    impl<E: Check, const N: usize> BorshDeserialize for Inline<E, N> {
        fn deserialize_reader<Rd: io::Read>(reader: &mut Rd) -> io::Result<Self> {
            let len = u32::deserialize_reader(reader)? as usize;
            if len > Self::capacity() {
                return Err(Error::new(
                    ErrorKind::InvalidData,
                    "length exceeds the inline capacity",
                ));
            }
            // `N <= 254`: a fixed buffer
            let mut buf = [0u8; 254];
            reader.read_exact(&mut buf[..len])?;
            E::check(&buf[..len])?;
            // SAFETY: checked for `E`, fits
            Ok(unsafe { Self::try_from_bytes(&buf[..len]) }.expect("checked length"))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{HipByt, HipStr, SmallByt, TinyStr};

    const LONG: &str = "a string that is definitely longer than any inline capacity";

    #[test]
    fn round_trips() {
        let encoded = borsh::to_vec(&HipStr::from(LONG)).unwrap();
        assert_eq!(encoded, borsh::to_vec(LONG).unwrap(), "same format as str");
        let s: TinyStr = borsh::from_slice(&encoded).unwrap();
        assert_eq!(s, LONG);

        let encoded = borsh::to_vec(&SmallByt::from(b"abc")).unwrap();
        let b: HipByt<'_> = borsh::from_slice(&encoded).unwrap();
        assert_eq!(b, b"abc".as_slice());
    }

    #[test]
    #[cfg(feature = "bstr")]
    fn bstr_byte_strings() {
        let b = crate::SmallBStr::from(b"\xffab".as_slice());
        let encoded = borsh::to_vec(&b).unwrap();
        assert_eq!(encoded, borsh::to_vec(b"\xffab".as_slice()).unwrap());
        let back: crate::TinyBStr = borsh::from_slice(&encoded).unwrap();
        assert_eq!(back, b);
    }

    #[test]
    fn invalid_utf8() {
        let encoded = borsh::to_vec(&[0xffu8, 0xfe].as_slice()).unwrap();
        let err = borsh::from_slice::<HipStr<'_>>(&encoded).unwrap_err();
        assert_eq!(err.kind(), ErrorKind::InvalidData);
    }

    #[test]
    fn huge_length_prefix_does_not_allocate_upfront() {
        // announces 4 GiB but carries 3 bytes
        let input = [0xff, 0xff, 0xff, 0xff, 1, 2, 3];
        assert!(borsh::from_slice::<HipByt<'_>>(&input).is_err());
    }

    #[test]
    fn c_strings() {
        let c = crate::HipCStr::from(c"abc");
        let encoded = borsh::to_vec(&c).unwrap();
        assert_eq!(
            encoded,
            borsh::to_vec(b"abc".as_slice()).unwrap(),
            "bytes without NUL"
        );
        let back: crate::TinyCStr = borsh::from_slice(&encoded).unwrap();
        assert_eq!(back, c"abc");
        let nul = borsh::to_vec(b"a\0b".as_slice()).unwrap();
        assert!(borsh::from_slice::<crate::HipCStr>(&nul).is_err());
    }

    #[test]
    fn inline_values() {
        use crate::inline::{InlineByt, InlineCStr, InlineStr};

        let s = InlineStr::<8>::inline("héllo");
        let encoded = borsh::to_vec(&s).unwrap();
        assert_eq!(
            encoded,
            borsh::to_vec("héllo").unwrap(),
            "same format as str"
        );
        assert_eq!(borsh::from_slice::<InlineStr<8>>(&encoded).unwrap(), s);
        // the length prefix is checked before reading
        assert!(borsh::from_slice::<InlineStr<4>>(&encoded).is_err());
        let huge = [0xFF, 0xFF, 0xFF, 0xFF];
        assert!(borsh::from_slice::<InlineStr<8>>(&huge).is_err());
        let bad = borsh::to_vec(b"\xff".as_slice()).unwrap();
        assert!(
            borsh::from_slice::<InlineStr<8>>(&bad).is_err(),
            "not UTF-8"
        );

        let b = InlineByt::<4>::inline(b"ab");
        let encoded = borsh::to_vec(&b).unwrap();
        assert_eq!(encoded, borsh::to_vec(&HipByt::from(b"ab")).unwrap());
        assert_eq!(borsh::from_slice::<InlineByt<4>>(&encoded).unwrap(), b);

        let c = InlineCStr::<8>::inline(c"abc");
        let encoded = borsh::to_vec(&c).unwrap();
        assert_eq!(
            encoded,
            borsh::to_vec(&crate::HipCStr::from(c"abc")).unwrap()
        );
        assert_eq!(borsh::from_slice::<InlineCStr<8>>(&encoded).unwrap(), c);
        assert!(
            borsh::from_slice::<InlineCStr<3>>(&encoded).is_err(),
            "no room for the NUL"
        );
        let nul = borsh::to_vec(b"a\0".as_slice()).unwrap();
        assert!(borsh::from_slice::<InlineCStr<8>>(&nul).is_err());
    }

    #[test]
    #[cfg(feature = "bstr")]
    fn inline_bstr() {
        let b = crate::inline::InlineBStr::<4>::try_from_inner(::bstr::BStr::new("ab")).unwrap();
        let encoded = borsh::to_vec(&b).unwrap();
        assert_eq!(
            borsh::from_slice::<crate::inline::InlineBStr<4>>(&encoded).unwrap(),
            b
        );
    }
}
