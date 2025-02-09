//! Borsh support for `HipStr`.

use alloc::string::ToString;

use borsh::io::{Error, ErrorKind};
use borsh::{io, BorshDeserialize, BorshSerialize};

use super::HipStr;
use crate::bytes::HipByt;
use crate::Backend;

#[cfg(test)]
mod tests;

impl<B: Backend> BorshDeserialize for HipStr<'_, B> {
    fn deserialize_reader<R: io::Read>(reader: &mut R) -> io::Result<Self> {
        let bytes: HipByt<B> = HipByt::deserialize_reader(reader)?;
        Self::try_from(bytes).map_err(|err| {
            let msg = err.to_string();
            Error::new(ErrorKind::InvalidData, msg)
        })
    }
}

impl<B: Backend> BorshSerialize for HipStr<'_, B> {
    fn serialize<W: io::Write>(&self, writer: &mut W) -> io::Result<()> {
        self.as_bytes().serialize(writer)
    }
}
