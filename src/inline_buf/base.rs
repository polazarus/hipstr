//! Inline buffers: a bit-packed length and the elements, within the value.
//!
//! Only what the representations need: construction, length and raw access.
use core::marker::PhantomData;
use core::slice;

use super::layouts::{self, Layout};

/// Copies `len` bytes without a `memcpy` call for short lengths: two
/// (possibly overlapping) unaligned loads and stores of the largest power of
/// two that fits. Inlinable and usable in `const`.
///
/// # Safety
///
/// `src` valid for reads and `dst` for writes of `len` bytes, not overlapping.
#[inline]
const unsafe fn copy_short(src: *const u8, dst: *mut u8, len: usize) {
    macro_rules! pair {
        ($t:ty) => {{
            const N: usize = size_of::<$t>();
            // SAFETY: `N <= len`: both ends are in bounds of `src` and `dst`
            unsafe {
                let head = src.cast::<$t>().read_unaligned();
                let tail = src.add(len - N).cast::<$t>().read_unaligned();
                dst.cast::<$t>().write_unaligned(head);
                dst.add(len - N).cast::<$t>().write_unaligned(tail);
            }
        }};
    }
    if len > 32 {
        // SAFETY: precondition
        unsafe { dst.copy_from_nonoverlapping(src, len) };
    } else if len >= 16 {
        pair!(u128);
    } else if len >= 8 {
        pair!(u64);
    } else if len >= 4 {
        pair!(u32);
    } else if len >= 2 {
        pair!(u16);
    } else if len == 1 {
        // SAFETY: precondition
        unsafe { dst.write(src.read()) };
    }
}

/// Little-endian value of the `m <= size_of::<usize>()` bytes at `p`, zero
/// extended, without a byte-wise copy: two (possibly overlapping) loads.
///
/// # Safety
///
/// `p` valid for reads of `m` bytes.
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
    const W: usize = size_of::<usize>();
    if m == W {
        // SAFETY: precondition
        usize::from_le_bytes(unsafe { p.cast::<[u8; W]>().read_unaligned() })
    } else if W == 8 && m >= 4 {
        pair!(u32)
    } else if m >= 2 {
        pair!(u16)
    } else if m == 1 {
        // SAFETY: precondition
        unsafe { p.read() as usize }
    } else {
        0
    }
}

#[repr(transparent)]
pub struct Base<T, L: Layout<T>> {
    repr: L,
    phantom: PhantomData<T>,
}

impl<T, L: Layout<T>> Base<T, L> {
    pub const CAPACITY: usize = L::CAPACITY;

    #[inline]
    pub const fn new() -> Self {
        Self {
            repr: L::EMPTY,
            phantom: PhantomData,
        }
    }

    /// Copies `slice` inline, in a `const` context too.
    ///
    /// # Panics
    ///
    /// Panics if `slice` is longer than [`CAPACITY`](Self::CAPACITY).
    #[inline]
    #[track_caller]
    pub const fn from_slice_copy(slice: &[T]) -> Self
    where
        T: Copy,
    {
        assert!(slice.len() <= L::CAPACITY, "too long to be inlined");
        if Self::WORDWISE {
            // SAFETY: byte elements (checked by `WORDWISE`), length checked
            return unsafe { Self::from_bytes_wordwise(slice.as_ptr().cast(), slice.len()) };
        }
        // A zeroed (fully initialized) buffer rather than `Self::new()`'s
        // uninitialized one: it is then moved as whole words, instead of
        // piecewise around the uninitialized bytes.
        let mut this = core::mem::MaybeUninit::<L>::zeroed();
        let raw = this.as_mut_ptr();
        // SAFETY: room for `slice.len()` elements (checked), copyable
        // elements, and `this` is fresh so the buffers do not overlap; the
        // tagged length makes the value valid
        unsafe {
            let data = layouts::data_mut_ptr_raw::<T, L>(raw);
            if size_of::<T>() == 1 {
                copy_short(slice.as_ptr().cast(), data.cast(), slice.len());
            } else {
                data.copy_from_nonoverlapping(slice.as_ptr(), slice.len());
            }
            layouts::set_len_raw::<T, L>(raw, slice.len());
            Self {
                repr: this.assume_init(),
                phantom: PhantomData,
            }
        }
    }

    /// Whether [`from_bytes_wordwise`](Self::from_bytes_wordwise) applies:
    /// byte elements, a one-byte tagged length, the data at offset 0 or 1,
    /// and a whole number of words.
    const WORDWISE: bool = size_of::<T>() == 1
        && L::LEN_SIZE == 1
        && matches!(<L as layouts::LayoutExt<T>>::DATA_OFFSET, Some(0 | 1))
        && size_of::<L>() % size_of::<usize>() == 0
        && size_of::<L>() <= 4 * size_of::<usize>();

    /// Builds the value in registers, word by word, and stores whole words.
    ///
    /// Writing the tag and the bytes to memory and reading the value back as
    /// words stalls store-to-load forwarding (~25 cycles): this avoids it.
    /// The memory image, read as a little-endian integer, is
    /// `data << (8 * DATA_OFFSET) | tag << (8 * LEN_OFFSET)`; each word is
    /// stored in native order (`from_le`), so it works on big endian too.
    ///
    /// # Safety
    ///
    /// [`WORDWISE`](Self::WORDWISE), `src` valid for reads of
    /// `len <= CAPACITY` bytes.
    #[inline]
    const unsafe fn from_bytes_wordwise(src: *const u8, len: usize) -> Self {
        const MAX_WORDS: usize = 4;
        let w = size_of::<usize>();
        let words = size_of::<L>() / w;
        let data_offset = match <L as layouts::LayoutExt<T>>::DATA_OFFSET {
            Some(offset) => offset,
            None => unreachable!(),
        };
        let len_offset = <L as layouts::LayoutExt<T>>::LEN_OFFSET;

        // data limbs, little endian, zero extended
        let mut limbs = [0usize; MAX_WORDS];
        let mut k = 0;
        while k * w < len {
            let m = if len - k * w < w { len - k * w } else { w };
            // SAFETY: `k * w + m <= len` bytes readable (precondition)
            limbs[k] = unsafe { load_le(src.add(k * w), m) };
            k += 1;
        }
        // shift by the data offset (0 or 1 byte)
        if data_offset == 1 {
            let mut k = words;
            while k > 0 {
                k -= 1;
                let carry = if k > 0 {
                    limbs[k - 1] >> (8 * (w - 1))
                } else {
                    0
                };
                limbs[k] = (limbs[k] << 8) | carry;
            }
        }
        // tag
        let tag = layouts::encode_len::<T, L>(len);
        limbs[len_offset / w] |= tag << (8 * (len_offset % w));

        let mut this = core::mem::MaybeUninit::<L>::uninit();
        let raw = this.as_mut_ptr().cast::<usize>();
        let mut k = 0;
        while k < words {
            // SAFETY: `words` whole words in `L`, possibly unaligned
            unsafe { raw.add(k).write_unaligned(usize::from_le(limbs[k])) };
            k += 1;
        }
        // SAFETY: every byte written, tagged length set
        unsafe {
            Self {
                repr: this.assume_init(),
                phantom: PhantomData,
            }
        }
    }

    #[inline]
    pub const fn len(&self) -> usize {
        layouts::len(&self.repr)
    }

    /// # Safety
    ///
    /// `new_len <= CAPACITY`, and the first `new_len` elements must be
    /// initialized.
    #[inline]
    pub const unsafe fn set_len(&mut self, new_len: usize) {
        // SAFETY: precondition
        unsafe {
            layouts::set_len(&mut self.repr, new_len);
        }
    }

    #[inline]
    pub const fn as_slice(&self) -> &[T] {
        let len = self.len();
        let ptr = self.as_ptr();
        // SAFETY: `len` initialized elements
        unsafe { slice::from_raw_parts(ptr, len) }
    }

    #[inline]
    pub const fn as_mut_ptr(&mut self) -> *mut T {
        layouts::data_mut_ptr(&mut self.repr)
    }

    #[inline]
    pub const fn as_ptr(&self) -> *const T {
        layouts::data_ptr(&self.repr)
    }
}

impl<T, L: Layout<T>> Copy for Base<T, L> {}

impl<T, L: Layout<T>> Clone for Base<T, L> {
    fn clone(&self) -> Self {
        *self
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::inline_buf::layouts::{BasicLayout, SmallLayout, TinyLayout};

    #[test]
    fn copy_short_every_length() {
        let src: [u8; 40] = core::array::from_fn(|i| i as u8 + 1);
        for len in 0..=src.len() {
            let mut dst = [0u8; 48];
            // SAFETY: in bounds, distinct arrays
            unsafe { copy_short(src.as_ptr(), dst.as_mut_ptr(), len) };
            assert_eq!(&dst[..len], &src[..len], "len {len}");
            assert!(dst[len..].iter().all(|&b| b == 0), "wrote past {len}");
        }
    }

    fn inline_every_length<L: Layout<u8>>() {
        let src: [u8; 32] = core::array::from_fn(|i| i as u8 + 1);
        for len in 0..=L::CAPACITY {
            let b = Base::<u8, L>::from_slice_copy(&src[..len]);
            assert_eq!(b.as_slice(), &src[..len]);
        }
    }

    #[test]
    fn from_slice_copy_every_length() {
        inline_every_length::<BasicLayout>();
        inline_every_length::<SmallLayout>();
        inline_every_length::<TinyLayout>();
    }

    #[test]
    fn const_copy() {
        const B: Base<u8, BasicLayout> = Base::from_slice_copy(b"0123456789");
        assert_eq!(B.as_slice(), b"0123456789");
    }
}
