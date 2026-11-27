use core::mem::MaybeUninit;
use core::num::NonZeroUsize;
use core::ptr;

/// Memory layout of an inline vector.
///
/// The tagged length is a `LEN_SIZE`-byte integer placed either
///
/// - in the least significant byte(s) of the first word, tagged with bit 0 set
///   ("low" layouts), or
/// - in the most significant byte(s) of the last word, tagged with its two top
///   bits set ("high" layouts, see [`HighLayout`]).
pub trait Layout<T>: Copy {
    const LEN_SIZE: usize;
    const CAPACITY: usize;
    const EMPTY: Self;
    /// Whether the tagged length lives in the most significant bits of the last word.
    const HIGH: bool = false;
}

pub trait LayoutExt<T>: Layout<T> {
    const SIZE: usize;
    const DATA_OFFSET: Option<usize>;
    const DATA_SIZE: usize;
    const LEN_OFFSET: usize;
    /// Tag bits, in the coordinates of the `LEN_SIZE`-byte length field.
    const TAG: usize;
}

/// Whether the length field comes first in memory.
const fn len_first(high: bool) -> bool {
    high == cfg!(target_endian = "big")
}

impl<T, L: Layout<T>> LayoutExt<T> for L {
    const SIZE: usize = size_of::<Self>();

    const DATA_OFFSET: Option<usize> = {
        if align_of::<T>() > align_of::<Self>() {
            None
        } else if len_first(L::HIGH) {
            Some(Self::SIZE - Self::DATA_SIZE)
        } else {
            Some(0)
        }
    };
    const DATA_SIZE: usize = Self::CAPACITY * size_of::<T>();

    const LEN_OFFSET: usize = if len_first(L::HIGH) {
        0
    } else {
        Self::SIZE - Self::LEN_SIZE
    };

    const TAG: usize = if L::HIGH {
        if L::LEN_SIZE == 0 {
            0
        } else {
            0b11 << (L::LEN_SIZE * 8 - 2)
        }
    } else {
        1
    };
}

const fn encode<T, L: Layout<T>>(len: usize) -> usize {
    if L::HIGH {
        len | L::TAG
    } else {
        (len << 1) | 1
    }
}

const fn decode<T, L: Layout<T>>(tagged: usize) -> usize {
    if L::HIGH {
        tagged & !L::TAG
    } else {
        tagged >> 1
    }
}

/// Returns the length of the vector encoded in the layout.
pub(crate) const fn len<T, L: Layout<T>>(layout: &L) -> usize {
    let ptr = unsafe { (&raw const *layout).cast::<u8>().add(L::LEN_OFFSET) };
    let tagged_len = match L::LEN_SIZE {
        0 => return 0,
        1 => unsafe { *ptr as usize },
        2 => unsafe { *(ptr.cast::<u16>()) as usize },
        4 => unsafe { *(ptr.cast::<u32>()) as usize },
        8 => unsafe { *(ptr.cast::<u64>()) as usize },
        _ => unreachable!(),
    };
    decode::<T, L>(tagged_len)
}

/// Sets the length of the vector.
pub(crate) const unsafe fn set_len<T, L: Layout<T>>(layout: &mut L, len: usize) {
    debug_assert!(len <= L::CAPACITY);

    let ptr = unsafe { (&raw mut *layout).cast::<u8>().add(L::LEN_OFFSET) };
    let tagged_len = encode::<T, L>(len);
    match L::LEN_SIZE {
        0 => (),
        1 => unsafe {
            debug_assert!(tagged_len as u64 <= 0xFF, "length exceeds 1-byte field");
            ptr.write(tagged_len as u8);
        },
        2 => unsafe {
            debug_assert!(tagged_len as u64 <= 0xFFFF, "length exceeds 2-byte field");
            ptr.cast::<u16>().write(tagged_len as u16);
        },
        4 => unsafe {
            debug_assert!(
                tagged_len as u64 <= 0xFFFF_FFFF,
                "length exceeds 4-byte field"
            );
            ptr.cast::<u32>().write(tagged_len as u32);
        },
        8 => unsafe {
            ptr.cast::<u64>().write(tagged_len as u64);
        },
        _ => unreachable!(),
    }
}

/// Returns a raw const pointer to the vector's buffer.
pub(crate) const fn data_ptr<T, L: Layout<T>>(layout: &L) -> *const T {
    if let Some(offset) = L::DATA_OFFSET {
        unsafe { (&raw const *layout).byte_add(offset).cast() }
    } else {
        ptr::dangling()
    }
}

/// Returns a raw mutable pointer to the vector's buffer.
pub(crate) const fn data_mut_ptr<T, L: Layout<T>>(layout: &mut L) -> *mut T {
    if let Some(offset) = L::DATA_OFFSET {
        unsafe { (&raw mut *layout).byte_add(offset).cast() }
    } else {
        ptr::dangling_mut()
    }
}

/// Computes `(capacity, len_size)` for elements of type `T` in a layout of
/// `size` bytes aligned to `align`, where `tag_bits` bits of the length field
/// are reserved for the tag.
const fn numbers<T>(size: usize, align: usize, tag_bits: u32) -> (usize, usize) {
    if align_of::<T>() > align {
        return (0, 0);
    }

    let element_size = size_of::<T>();

    // find the maximum count of elements that can fit in the layout
    let Some(mut count) = size.checked_div(element_size) else {
        return (usize::MAX >> tag_bits, size_of::<usize>());
    };

    loop {
        if count == 0 {
            break (0, 0);
        }

        let remainder = size - (count * element_size);
        // largest power of two that fits in the remainder, capped to a word
        let len_size = if remainder == 0 {
            0
        } else {
            let p = 1 << remainder.ilog2();
            if p > size_of::<usize>() {
                size_of::<usize>()
            } else {
                p
            }
        };
        let len_max = if len_size == 0 {
            0
        } else {
            (1 << (len_size as u32 * 8 - tag_bits)) - 1
        };

        if count <= len_max {
            break (count, len_size);
        }

        // not encodable, but the len size is already a word
        if len_size == size_of::<usize>() {
            break (len_max, len_size);
        }
        count -= 1;
    }
}

/// A layout of `1 + REST` words with the tagged length in the low bits of the
/// first word (bit 0 set). Any properly aligned pointer has bit 0 clear, so it
/// can share the first word.
#[repr(C)]
pub struct LowLayout<const REST: usize> {
    #[cfg(target_endian = "little")]
    lsw: NonZeroUsize,

    rest: [MaybeUninit<usize>; REST],

    #[cfg(target_endian = "big")]
    lsw: NonZeroUsize,
}

impl<const REST: usize> Copy for LowLayout<REST> {}
impl<const REST: usize> Clone for LowLayout<REST> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T, const REST: usize> Layout<T> for LowLayout<REST> {
    const LEN_SIZE: usize = numbers::<T>(size_of::<Self>(), align_of::<Self>(), 1).1;
    const CAPACITY: usize = numbers::<T>(size_of::<Self>(), align_of::<Self>(), 1).0;
    const EMPTY: Self = Self {
        lsw: NonZeroUsize::new(1).unwrap(),
        rest: [MaybeUninit::uninit(); REST],
    };
}

/// A layout of `REST + 1` words with the tagged length in the high bits of the
/// last word (two top bits set). Lets the first word hold an unaligned pointer.
#[repr(C)]
pub struct HighLayout<const REST: usize> {
    #[cfg(target_endian = "big")]
    msw: NonZeroUsize,

    rest: [MaybeUninit<usize>; REST],

    #[cfg(target_endian = "little")]
    msw: NonZeroUsize,
}

impl<const REST: usize> Copy for HighLayout<REST> {}
impl<const REST: usize> Clone for HighLayout<REST> {
    fn clone(&self) -> Self {
        *self
    }
}

/// Tag of [`HighLayout`] in the coordinates of a full word.
pub const HIGH_TAG: usize = 0b11 << (usize::BITS - 2);

impl<T, const REST: usize> Layout<T> for HighLayout<REST> {
    const LEN_SIZE: usize = numbers::<T>(size_of::<Self>(), align_of::<Self>(), 2).1;
    const CAPACITY: usize = numbers::<T>(size_of::<Self>(), align_of::<Self>(), 2).0;
    const EMPTY: Self = Self {
        msw: NonZeroUsize::new(HIGH_TAG).unwrap(),
        rest: [MaybeUninit::uninit(); REST],
    };
    const HIGH: bool = true;
}

/// The 3-word layout.
pub type BasicLayout = LowLayout<2>;
/// The 1-word layout.
pub type TinyLayout = LowLayout<0>;
/// The 2-word layout.
pub type SmallLayout = HighLayout<1>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn layout_zst() {
        assert_eq!(size_of::<BasicLayout>(), 3 * size_of::<usize>());
        assert_eq!(<BasicLayout as Layout<()>>::CAPACITY, usize::MAX >> 1);
    }

    #[test]
    fn capacities_u8() {
        let w = size_of::<usize>();
        assert_eq!(<BasicLayout as Layout<u8>>::CAPACITY, 3 * w - 1);
        assert_eq!(<SmallLayout as Layout<u8>>::CAPACITY, 2 * w - 1);
        assert_eq!(<TinyLayout as Layout<u8>>::CAPACITY, w - 1);
        assert_eq!(<SmallLayout as Layout<()>>::CAPACITY, usize::MAX >> 2);
    }

    #[test]
    fn layout_i32() {
        assert_eq!(size_of::<BasicLayout>(), 3 * size_of::<usize>());
        assert_eq!(
            <BasicLayout as Layout<i32>>::CAPACITY,
            (3 * size_of::<usize>() - size_of::<i32>()) / size_of::<i32>()
        );
    }
}
