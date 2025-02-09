//! Borsh support for `HipByt`.

use borsh::io::{self};
use borsh::{BorshDeserialize, BorshSerialize};

use super::HipByt;
use crate::Backend;

#[cfg(test)]
mod tests;

impl<B: Backend> BorshDeserialize for HipByt<'_, B> {
    fn deserialize_reader<R: io::Read>(reader: &mut R) -> io::Result<Self> {
        let len = u32::deserialize_reader(reader)? as usize;
        if len == 0 {
            Ok(Self::new())
        } else {
            let mut result = Self::with_capacity(len);
            let slice = result.spare_capacity_mut();
            for byte in slice.iter_mut().take(len) {
                byte.write(u8::deserialize_reader(reader)?);
            }
            unsafe {
                result.set_len(len);
            }
            Ok(result)
        }
    }
}

impl<B: Backend> BorshSerialize for HipByt<'_, B> {
    fn serialize<W: io::Write>(&self, writer: &mut W) -> io::Result<()> {
        self.as_slice().serialize(writer)
    }
}
