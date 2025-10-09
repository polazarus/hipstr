//! Internal representation of inline vectors.

use core::mem::{ManuallyDrop, MaybeUninit};
use core::num::NonZeroUsize;
use core::ptr;
use core::ptr::NonNull;

use generic_array::GenericArray;

use super::length::InlineLength;
use crate::common::force_copy;

/// Returns the number of bits needed to represent `n`.
pub const fn bits(n: usize) -> u32 {
    usize::BITS - n.leading_zeros()
}

/// Inline vector internal representation.
///
/// # Safety
///
/// `InlineRepr` is copyable (with [`Self::clone`]) but the copy is only valid
/// if the elements are copyable.
///
/// **This is not enforced by the type system**, so it is up to the user of this
/// type to either:
/// - ensure that the element type is actually copyable
/// - or that the source representation is no longer used after the copy.
///
/// Also, the representation does not drop its elements, so the user must ensure
/// that the elements are properly dropped when the representation is no longer
/// used.
///
/// For theses reasons, `InlineRepr` is not exposed outside this crate.
#[repr(C)]
pub struct InlineRepr<T, L>
where
    L: InlineLength,
{
    /// Tagged word that contains the length in its lower bits (so upper bytes)
    /// and possibly part of the data.
    #[cfg(target_endian = "little")]
    init_word: NonZeroUsize,

    /// The rest of the representation, containing the remainder of the data.
    rest: GenericArray<MaybeUninit<usize>, L::WordsM1>,

    /// Tagged word that contains the length in its lower bits (so lower bytes)
    /// and possibly part of the data.
    #[cfg(target_endian = "big")]
    init_word: NonZeroUsize,

    align: ManuallyDrop<[T; 0]>,
}

impl<T, N: InlineLength> Clone for InlineRepr<T, N> {
    /// Actually copies the representation.
    ///
    /// See the safety comment on `InlineRepr`.
    fn clone(&self) -> Self {
        // SAFETY: see the safety comment on `InlineRepr`.
        unsafe { force_copy(self) }
    }
}

impl<T, L> InlineRepr<T, L>
where
    L: InlineLength,
{
    /// Creates a new, uninitialized inline representation.
    pub const fn new() -> Self {
        let init_word = const { NonZeroUsize::new(1).unwrap() };
        Self {
            init_word,
            rest: GenericArray::uninit(),
            align: ManuallyDrop::new([]),
        }
    }

    /// Creates a new, zeroed inline representation.
    pub const unsafe fn zeroed() -> Self {
        let init_word = NonZeroUsize::new(1).unwrap();
        Self {
            init_word,
            rest: unsafe { MaybeUninit::zeroed().assume_init() },
            align: ManuallyDrop::new([]),
        }
    }

    /// Various constants about the inline representation.
    const LENGTH_AND_DATA: (usize, usize, usize, usize) = {
        let blob = L::USIZE;
        let t_align = align_of::<T>();
        let t_size = size_of::<T>();

        let (reserved, data_size) = if t_size == 0 {
            (size_of::<usize>(), usize::MAX >> 1)
        } else {
            let t_size_a = t_size / t_align;
            let blob_a = blob / t_align;
            let mut reserved_a = 1;

            let data_size = loop {
                if reserved_a >= blob_a {
                    break 0;
                }
                let max_data = (blob_a - reserved_a) / t_size_a;
                let needed_len_bits = (bits(max_data) + 1) as usize; // 1 bit for the tag
                let len_bits = 8 * reserved_a * t_align;
                if max_data == 0 || needed_len_bits <= len_bits {
                    break max_data;
                }
                reserved_a += 1;
            };

            let reserved = reserved_a * t_align;
            (reserved, data_size)
        };

        let len_size = if reserved > size_of::<usize>() {
            size_of::<usize>()
        } else {
            reserved
        };

        let len_off: usize;
        let data_off: usize;
        if cfg!(target_endian = "little") {
            // left aligned
            len_off = 0;

            assert!(reserved % t_align == 0);

            data_off = reserved;
        } else {
            // beware to be right aligned, so offset from the end with the tight
            // size (and not the reserved size)
            len_off = blob - len_size;

            data_off = 0;
        }

        (len_off, len_size, data_off, data_size)
    };

    /// Offset inside the representation where the length is stored.
    pub(super) const LEN_OFFSET: usize = Self::LENGTH_AND_DATA.0;

    /// Size in bytes of the length field.
    pub(super) const LEN_SIZE: usize = Self::LENGTH_AND_DATA.1;

    /// Offset inside the representation where the data starts.
    pub(super) const DATA_OFFSET: usize = Self::LENGTH_AND_DATA.2;

    /// Maximum number of elements that can be stored inline.
    pub const CAPACITY: usize = Self::LENGTH_AND_DATA.3;

    /// Offset inside a `usize` where the length is stored.
    const IN_LEN_OFFSET: usize = if cfg!(target_endian = "little") {
        0
    } else {
        size_of::<usize>() - Self::LEN_SIZE
    };

    /// Checks if the given length can be stored inline.
    #[cfg(test)]
    pub const fn is_len_valid(len: usize) -> bool {
        // strict comparison to take into account the tag bit
        (bits(len) as usize) < Self::LEN_SIZE * 8
    }

    /// Returns a pointer to the representation.
    const fn ptr(&self) -> *const u8 {
        ptr::from_ref(self).cast()
    }

    /// Returns a mutable non null pointer to the representation.
    const fn non_null(&mut self) -> NonNull<u8> {
        NonNull::from_mut(self).cast()
    }

    /// Returns the length of the inline vector.
    pub const fn len(&self) -> usize {
        let mut value: usize = 0;
        let src = unsafe { self.ptr().add(Self::LEN_OFFSET) };
        let dst: *mut u8 = ptr::from_mut(&mut value).cast();

        unsafe {
            dst.add(Self::IN_LEN_OFFSET)
                .copy_from_nonoverlapping(src, Self::LEN_SIZE);
        }
        value >> 1
    }

    /// Sets the length of the inline vector.
    ///
    /// # Safety
    ///
    /// The length must be valid (i.e. `Self::is_len_valid(len)` must be true), and
    /// must not exceed the current capacity. Setting the length to a value
    /// greater than the current length is only safe if the new elements are
    /// properly initialized.
    pub const unsafe fn set_len(&mut self, len: usize) {
        debug_assert!(len <= Self::CAPACITY, "length exceeds inline capacity");
        let value = (len << 1) | 1;

        // SAFETY: valid pointer by construction
        let dst = unsafe { self.non_null().add(Self::LEN_OFFSET) };

        let src: NonNull<u8> = NonNull::from_ref(&value).cast();

        // SAFETY: the destination is large enough by construction and there is
        // no overlap between function parameter and local variable
        unsafe {
            src.add(Self::IN_LEN_OFFSET)
                .copy_to_nonoverlapping(dst, Self::LEN_SIZE);
        }
    }

    /// Returns a pointer to the inline vector.
    ///
    /// If the capacity is zero, returns a dangling pointer. This is to ensure
    /// that the pointer is never null and property aligned.
    pub const fn as_ptr(&self) -> *const T {
        if Self::CAPACITY == 0 {
            return ptr::dangling();
        }

        unsafe { self.ptr().add(Self::DATA_OFFSET).cast() }
    }

    /// Returns a mutable pointer to the inline vector.
    ///
    /// If the capacity is zero, returns a dangling pointer. This is to ensure
    /// that the pointer is never null and property aligned.
    pub const fn as_mut_ptr(&mut self) -> *mut T {
        self.as_non_null().as_ptr()
    }

    /// Returns a non-null pointer to the inline vector.
    ///
    /// If the capacity is zero, returns a dangling pointer. This is to ensure
    /// that the pointer is never null and property aligned.
    pub const fn as_non_null(&mut self) -> NonNull<T> {
        if Self::CAPACITY == 0 {
            return NonNull::dangling();
        }

        unsafe { self.non_null().add(Self::DATA_OFFSET).cast() }
    }
}
