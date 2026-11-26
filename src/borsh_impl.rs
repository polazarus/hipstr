//! `borsh` support for strings and byte strings, every size.
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

impl<'a, R: Repr<'a, u8>> BorshSerialize for Hip<Bytes, R> {
    #[inline]
    fn serialize<W: io::Write>(&self, writer: &mut W) -> io::Result<()> {
        self.bytes().serialize(writer)
    }
}

impl<'a, R: Repr<'a, u8>> BorshDeserialize for Hip<Bytes, R> {
    #[inline]
    fn deserialize_reader<Rd: io::Read>(reader: &mut Rd) -> io::Result<Self> {
        Vec::<u8>::deserialize_reader(reader).map(Self::from_owned)
    }
}

impl<'a, R: Repr<'a, u8>> BorshSerialize for Hip<Utf8, R> {
    #[inline]
    fn serialize<W: io::Write>(&self, writer: &mut W) -> io::Result<()> {
        self.bytes().serialize(writer)
    }
}

impl<'a, R: Repr<'a, u8>> BorshDeserialize for Hip<Utf8, R> {
    fn deserialize_reader<Rd: io::Read>(reader: &mut Rd) -> io::Result<Self> {
        let bytes = Vec::<u8>::deserialize_reader(reader)?;
        String::from_utf8(bytes)
            .map(Self::from_owned)
            .map_err(|e| Error::new(ErrorKind::InvalidData, e.to_string()))
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
}
