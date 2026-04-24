use core::mem::MaybeUninit;
#[cfg(target_endian = "little")]
use core::num::NonZeroUsize;
use core::ptr;
use core::ptr::NonNull;

pub trait Layout<T>: Copy {
    const LEN_SIZE: usize;
    const CAPACITY: usize;
    const EMPTY: Self;
}

pub trait LayoutExt<T>: Layout<T> {
    const SIZE: usize;
    const DATA_OFFSET: Option<usize>;
    const DATA_SIZE: usize;
    const LEN_OFFSET: usize;
}

impl<T, L: Layout<T>> LayoutExt<T> for L {
    const SIZE: usize = size_of::<Self>();

    const DATA_OFFSET: Option<usize> = {
        if align_of::<T>() > align_of::<Self>() {
            None
        } else if cfg!(target_endian = "little") {
            Some(Self::SIZE - Self::DATA_SIZE)
        } else {
            // in big endian, the length is stored at the end of the layout, so data starts at offset 0
            Some(0)
        }
    };
    const DATA_SIZE: usize = Self::CAPACITY * size_of::<T>();

    const LEN_OFFSET: usize = {
        #[cfg(target_endian = "little")]
        {
            0
        }
        #[cfg(target_endian = "big")]
        {
            Self::SIZE - Self::LEN_SIZE
        }
    };
}

/// Returns the length of the vector encoded in the layout.
pub(crate) const fn len<T, L: Layout<T>>(layout: &L) -> usize {
    let ptr = unsafe { (&raw const *layout).cast::<u8>().add(L::LEN_OFFSET) };
    let tagged_len = match L::LEN_SIZE {
        0 => 0,
        1 => unsafe { *ptr as usize },
        2 => unsafe { *(ptr.cast::<u16>()) as usize },
        4 => unsafe { *(ptr.cast::<u32>()) as usize },
        8 => unsafe { *(ptr.cast::<u64>()) as usize },
        _ => unreachable!(),
    };
    tagged_len >> 1
}

/// Sets the length of the vector.
pub(crate) const unsafe fn set_len<T, L: Layout<T>>(layout: &mut L, len: usize) {
    debug_assert!(len <= L::CAPACITY);

    let ptr = unsafe { (&raw mut *layout).cast::<u8>().add(L::LEN_OFFSET) };
    // add tag
    let tagged_len = (len << 1) | 1;
    match L::LEN_SIZE {
        0 => (),
        1 => unsafe {
            debug_assert!(
                tagged_len as u64 <= 0xFF,
                "length exceeds maximum for 1-byte length field"
            );
            ptr.write(tagged_len as u8);
        },
        2 => unsafe {
            debug_assert!(
                tagged_len as u64 <= 0xFFFF,
                "length exceeds maximum for 2-byte length field"
            );
            ptr.cast::<u16>().write(tagged_len as u16);
        },
        4 => unsafe {
            debug_assert!(
                tagged_len as u64 <= 0xFFFF_FFFF,
                "length exceeds maximum for 4-byte length field"
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

pub(crate) const fn data_non_null<T, L: Layout<T>>(layout: &mut L) -> NonNull<T> {
    if let Some(offset) = L::DATA_OFFSET {
        unsafe { NonNull::from_mut(layout).byte_add(offset).cast() }
    } else {
        NonNull::dangling()
    }
}

/// Returns the maximum length that can be encoded in a length field of the given size (in bytes).
const fn len_max(len_size: usize) -> usize {
    (1 << (len_size * 8).saturating_sub(1)) - 1
}

/// A basic layout that can store any type, including ZSTs on 3 pointer-sized words.
/// It uses a non-zero integer to store the length allowing for a niche that Rust may exploit.
/// This layout is simple and efficient for most cases.
#[repr(C)]
pub struct BasicLayout {
    #[cfg(target_endian = "little")]
    lsw: NonZeroUsize,

    remainder: [MaybeUninit<usize>; 2],

    #[cfg(target_endian = "big")]
    lsw: NonZeroUsize,
}

impl Copy for BasicLayout {}
impl Clone for BasicLayout {
    fn clone(&self) -> Self {
        *self
    }
}

impl BasicLayout {
    pub(crate) const fn numbers<T>() -> (usize, usize) {
        if align_of::<T>() > align_of::<Self>() {
            return (0, 0);
        }

        let size = size_of::<Self>();
        let element_size = size_of::<T>();
        if element_size == 0 {
            (usize::MAX >> 1, size_of::<usize>())
        } else {
            let mut count = size / element_size;
            loop {
                if count == 0 {
                    break (0, 0);
                }

                let remainder = size - (count * element_size);
                let len_size = remainder.next_power_of_two() >> 1;
                let (len_size, full) = if len_size >= size_of::<usize>() {
                    (size_of::<usize>(), true)
                } else {
                    (len_size, false)
                };
                // maximal length w.r.t the current len size (remove 1 bit for nonzero tagging)
                let len_max = len_max(len_size);

                // count is encodable
                if count <= len_max {
                    break (count, len_size);
                }

                // not encodable, but the len size is already usize
                if full {
                    break (len_max, len_size);
                }
                count -= 1;
            }
        }
    }
}

impl<T> Layout<T> for BasicLayout {
    const LEN_SIZE: usize = Self::numbers::<T>().1;
    const CAPACITY: usize = Self::numbers::<T>().0;
    const EMPTY: Self = {
        Self {
            lsw: NonZeroUsize::new(1).unwrap(),
            remainder: [MaybeUninit::uninit(); 2],
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn layout_zst() {
        assert_eq!(size_of::<BasicLayout>(), 3 * size_of::<usize>());
        assert_eq!(<BasicLayout as Layout<()>>::CAPACITY, usize::MAX >> 1);
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
