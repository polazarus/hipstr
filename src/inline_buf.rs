//! Inline byte buffers: the bytes and a one-byte tagged length, within the
//! value (`WORDS` machine words).
//!
//! The tagged length shares a word with the bytes:
//!
//! - **low** layouts (`HIGH = false`) keep it in the least significant byte of
//!   the first word, with bit 0 set: an aligned pointer in that word has bit 0
//!   clear, so the two are told apart;
//! - **high** layouts (`HIGH = true`) keep it in the most significant byte of
//!   the last word, with its two top bits set, so that the first word can
//!   hold any (even unaligned) pointer.
//!
//! In memory, the length byte is therefore the first or the last byte of the
//! value, depending on the layout and the endianness; the bytes fill the
//! rest. Every byte is always initialized (zeroes past the length).

/// An inline buffer of `WORDS` words, holding up to `WORDS * size_of::<usize>() - 1`
/// bytes.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Inline<const WORDS: usize, const HIGH: bool>([usize; WORDS]);

/// The 3-word buffer (23 bytes on 64-bit).
pub type Basic = Inline<3, false>;
/// The 2-word buffer, its tag in the top bits (15 bytes on 64-bit).
pub type Small = Inline<2, true>;
/// The 1-word buffer (7 bytes on 64-bit).
pub type Tiny = Inline<1, false>;

const W: usize = size_of::<usize>();

/// Little-endian value of the `m` bytes at `p`, zero
/// extended, without a byte-wise copy: two (possibly overlapping) loads.
///
/// # Safety
///
/// `p` valid for reads of `m` bytes, `1 <= m <= size_of::<usize>()`.
#[inline]
const unsafe fn load_le(p: *const u8, m: usize) -> usize {
    macro_rules! pair {
        ($t:ty) => {{
            const N: usize = size_of::<$t>();
            // SAFETY: `N <= m`: both reads are in bounds
            let (lo, hi) = unsafe {
                (
                    <$t>::from_le_bytes(p.cast::<[u8; N]>().read_unaligned()),
                    <$t>::from_le_bytes(p.add(m - N).cast::<[u8; N]>().read_unaligned()),
                )
            };
            // overlapping bytes have the same value in both halves
            lo as usize | (hi as usize) << ((m - N) * 8)
        }};
    }
    if m == W {
        // SAFETY: precondition
        usize::from_le_bytes(unsafe { p.cast::<[u8; W]>().read_unaligned() })
    } else if W == 8 && m >= 4 {
        pair!(u32)
    } else if m >= 2 {
        pair!(u16)
    } else {
        debug_assert!(m == 1);
        // SAFETY: precondition
        unsafe { p.read() as usize }
    }
}

impl<const WORDS: usize, const HIGH: bool> Inline<WORDS, HIGH> {
    /// Size in bytes.
    const SIZE: usize = WORDS * W;

    /// Maximal length.
    pub const CAPACITY: usize = Self::SIZE - 1;

    /// Whether the length byte is the first byte in memory (otherwise the
    /// last): the low byte of the first word on little endian, the high byte
    /// of the first word on big endian.
    const LEN_FIRST: bool = HIGH == cfg!(target_endian = "big");

    /// Offset of the length byte.
    const LEN_OFFSET: usize = if Self::LEN_FIRST { 0 } else { Self::SIZE - 1 };

    /// Offset of the bytes.
    const DATA_OFFSET: usize = if Self::LEN_FIRST { 1 } else { 0 };

    const CHECK: () = {
        assert!(WORDS >= 1 && WORDS <= 4);
        // the tagged length must fit its byte
        assert!(Self::CAPACITY <= if HIGH { 0x3F } else { 0x7F });
    };

    /// The length byte for `len`.
    #[inline]
    const fn tag(len: usize) -> u8 {
        if HIGH {
            len as u8 | 0b1100_0000
        } else {
            (len as u8) << 1 | 1
        }
    }

    /// The empty buffer.
    #[inline]
    pub const fn new() -> Self {
        Self::from_slice_copy(&[])
    }

    /// Copies `bytes`, in a `const` context too.
    ///
    /// The value is built in registers, word by word, then stored as whole
    /// words: writing the bytes and the length to memory and reading the
    /// value back as words would stall store-to-load forwarding (~25 cycles).
    /// The memory image, read as a little-endian integer, is
    /// `bytes << (8 * DATA_OFFSET) | tag << (8 * LEN_OFFSET)`; each word is
    /// stored in native order (`from_le`), so it works on big endian too.
    ///
    /// # Panics
    ///
    /// Panics if `bytes` is longer than [`CAPACITY`](Self::CAPACITY).
    #[inline]
    #[track_caller]
    pub const fn from_slice_copy(bytes: &[u8]) -> Self {
        let () = Self::CHECK;
        let len = bytes.len();
        assert!(len <= Self::CAPACITY, "too long to be inlined");
        let src = bytes.as_ptr();

        // bytes as little-endian limbs, zero extended
        let mut limbs = [0usize; WORDS];
        let mut k = 0;
        while k * W < len {
            let m = if len - k * W < W { len - k * W } else { W };
            // SAFETY: `k * W + m <= len` bytes readable
            limbs[k] = unsafe { load_le(src.add(k * W), m) };
            k += 1;
        }
        // shift by the data offset (0 or 1 byte)
        if Self::DATA_OFFSET == 1 {
            let mut k = WORDS;
            while k > 0 {
                k -= 1;
                let carry = if k > 0 {
                    limbs[k - 1] >> (8 * (W - 1))
                } else {
                    0
                };
                limbs[k] = (limbs[k] << 8) | carry;
            }
        }
        // the length byte
        limbs[Self::LEN_OFFSET / W] |= (Self::tag(len) as usize) << (8 * (Self::LEN_OFFSET % W));
        // native order
        let mut k = 0;
        while k < WORDS {
            limbs[k] = usize::from_le(limbs[k]);
            k += 1;
        }
        Self(limbs)
    }

    #[inline]
    const fn byte_ptr(&self) -> *const u8 {
        (&raw const self.0).cast()
    }

    /// The length.
    #[inline]
    pub const fn len(&self) -> usize {
        // SAFETY: in bounds, initialized
        let tag = unsafe { self.byte_ptr().add(Self::LEN_OFFSET).read() };
        if HIGH {
            (tag & 0b0011_1111) as usize
        } else {
            (tag >> 1) as usize
        }
    }

    /// Sets the length.
    ///
    /// # Safety
    ///
    /// `len <= CAPACITY` (every byte is initialized, so no other condition).
    #[inline]
    pub const unsafe fn set_len(&mut self, len: usize) {
        debug_assert!(len <= Self::CAPACITY);
        // SAFETY: in bounds
        unsafe {
            (&raw mut self.0)
                .cast::<u8>()
                .add(Self::LEN_OFFSET)
                .write(Self::tag(len))
        };
    }

    /// Raw pointer to the bytes.
    #[inline]
    pub const fn as_ptr(&self) -> *const u8 {
        // SAFETY: in bounds
        unsafe { self.byte_ptr().add(Self::DATA_OFFSET) }
    }

    /// Raw mutable pointer to the bytes (`CAPACITY` of them, all initialized).
    #[inline]
    pub const fn as_mut_ptr(&mut self) -> *mut u8 {
        // SAFETY: in bounds
        unsafe { (&raw mut self.0).cast::<u8>().add(Self::DATA_OFFSET) }
    }

    /// The bytes.
    #[inline]
    pub const fn as_slice(&self) -> &[u8] {
        // SAFETY: `len <= CAPACITY` initialized bytes
        unsafe { core::slice::from_raw_parts(self.as_ptr(), self.len()) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn every_length<const WORDS: usize, const HIGH: bool>() {
        let src: [u8; 32] = core::array::from_fn(|i| i as u8 + 1);
        for len in 0..=Inline::<WORDS, HIGH>::CAPACITY {
            let mut b = Inline::<WORDS, HIGH>::from_slice_copy(&src[..len]);
            assert_eq!(b.as_slice(), &src[..len], "{WORDS} {HIGH} {len}");
            // SAFETY: in bounds
            unsafe {
                b.as_mut_ptr().write(0xAA);
                b.set_len(len.max(1));
            }
            assert_eq!(b.as_slice()[0], 0xAA);
        }
    }

    #[test]
    fn layouts() {
        assert_eq!(Basic::CAPACITY, 3 * W - 1);
        assert_eq!(Small::CAPACITY, 2 * W - 1);
        assert_eq!(Tiny::CAPACITY, W - 1);
        every_length::<3, false>();
        every_length::<2, true>();
        every_length::<1, false>();
    }

    /// Tag of high layouts, in the coordinates of a full word.
    const HIGH_TAG: usize = 0b11 << (usize::BITS - 2);

    #[test]
    fn tags() {
        // low: bit 0 of the first word set; high: top two bits of the last
        // word set (what the reprs rely on)
        const BE: bool = cfg!(target_endian = "big");
        const LOW_WORD: usize = if BE { 2 } else { 0 };
        const HIGH_WORD: usize = if BE { 0 } else { 1 };
        let b = Basic::from_slice_copy(b"ab");
        assert_eq!(b.0[LOW_WORD] & 1, 1);
        let s = Small::from_slice_copy(b"ab");
        assert_eq!(s.0[HIGH_WORD] & HIGH_TAG, HIGH_TAG);
        assert_eq!(Tiny::new().0[0], 1, "empty low buffer: only the tag");
    }

    #[test]
    fn const_copy() {
        const B: Basic = Basic::from_slice_copy(b"0123456789");
        assert_eq!(B.as_slice(), b"0123456789");
    }
}
