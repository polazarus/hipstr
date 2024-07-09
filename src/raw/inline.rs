//! Inline representation.

#![allow(clippy::inconsistent_struct_constructor)]
// REASON: the supports of little and big endianness results in two field orders
// as a result respecting the struct order is impossible for one of the two

use core::mem::{offset_of, size_of, MaybeUninit};
use core::num::NonZeroU8;
use core::ptr::copy_nonoverlapping;

use super::{MASK, TAG_BITS, TAG_INLINE};

#[cfg(test)]
mod tests;

const TAG: u8 = TAG_INLINE;
const SHIFT: u8 = TAG_BITS as u8;
const MAX_LEN: usize = 1 << (8 - SHIFT);

#[derive(Clone, Copy, Debug)]
pub(super) struct TaggedLen(NonZeroU8);

impl TaggedLen {
    #[allow(clippy::cast_possible_truncation)]
    #[inline]
    const fn encode(length: usize) -> Self {
        debug_assert!(length < MAX_LEN);
        let value = ((length << SHIFT) as u8) | TAG;

        // SAFETY: TAG != 0  ==>  value != 0
        Self(unsafe { NonZeroU8::new_unchecked(value) })
    }

    #[inline]
    const fn decode(self) -> usize {
        (self.0.get() >> SHIFT) as usize
    }

    #[inline]
    pub(super) const fn tag(self) -> u8 {
        self.0.get() & MASK
    }

    #[inline]
    const fn is_valid(self) -> bool {
        self.tag() == TAG
    }
}

/// Inline representation.
///
/// # Warning!
///
/// For big-endian platform, the shifted length is **after** the data.
/// For little-endian platform, the shifted length is **before** the data.
#[derive(Clone, Copy)]
#[repr(C)]
pub struct Inline<const INLINE_CAPACITY: usize> {
    #[cfg(target_endian = "little")]
    pub(super) len: TaggedLen,

    data: [MaybeUninit<u8>; INLINE_CAPACITY],

    #[cfg(target_endian = "big")]
    len: TaggedLen,
}

impl<const INLINE_CAPACITY: usize> Inline<INLINE_CAPACITY> {
    const ASSERTS: () = {
        if cfg!(target_endian = "little") {
            assert!(offset_of!(Self, len) == 0);
        } else {
            assert!(offset_of!(Self, len) == size_of::<Self>() - 1);
        }
    };

    /// Creates a new empty `Inline`.
    #[inline]
    pub const fn empty() -> Self {
        // HACK to actually check the asserts
        let () = Self::ASSERTS;

        let data = [MaybeUninit::uninit(); INLINE_CAPACITY];

        #[allow(clippy::inconsistent_struct_constructor)]
        Self {
            data,
            len: TaggedLen::encode(0),
        }
    }

    /// Creates a new empty `Inline`.
    #[inline]
    pub const fn zeroed(len: usize) -> Self {
        let data = [MaybeUninit::zeroed(); INLINE_CAPACITY];

        assert!(len <= INLINE_CAPACITY, "invalid length");

        let len = TaggedLen::encode(len);
        Self { data, len }
    }

    /// Creates a new `Inline` string by copying a byte slice.
    #[inline]
    #[allow(dead_code)]
    pub fn new(sl: &[u8]) -> Self {
        assert!(sl.len() <= INLINE_CAPACITY);

        // SAFETY: length check above
        unsafe { Self::new_unchecked(sl) }
    }

    /// Creates a new `Inline` string by copying a short byte slice.
    ///
    /// # Safety
    ///
    /// The input slice's length MUST be at most `INLINE_CAPACITY`.
    #[inline]
    pub unsafe fn new_unchecked(sl: &[u8]) -> Self {
        let len = sl.len();
        let mut data = [MaybeUninit::uninit(); INLINE_CAPACITY];

        // SAFETY: sl's length is a **function precondition**
        unsafe {
            copy_nonoverlapping(sl.as_ptr(), data.as_mut_ptr().cast(), len);
        }

        let len = TaggedLen::encode(len);
        let this = Self { data, len };
        debug_assert!(this.is_valid());

        this
    }

    /// Returns the length of this inline string.
    #[inline]
    pub const fn len(&self) -> usize {
        debug_assert!(self.is_valid());

        self.len.decode()
    }

    /// Returns an immutable view of this inline string.
    #[inline]
    pub const fn as_slice(&self) -> &[u8] {
        debug_assert!(self.is_valid());

        // HACK could be done with less unsafe one day:
        // waiting for const_slice_index and maybe_uninit_slice
        let data = self.data.as_ptr();
        let len = self.len();

        // SAFETY: type invariant (the first `len`-th bytes are initialized)
        unsafe { core::slice::from_raw_parts(data.cast(), len) }
    }

    /// Returns an immutable raw pointer of this inline string.
    #[inline]
    pub const fn as_ptr(&self) -> *const u8 {
        debug_assert!(self.is_valid());
        self.data.as_ptr().cast()
    }

    /// Returns a mutable view of this inline string.
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        // XXX should add const: waiting for const_mut_refs

        debug_assert!(self.is_valid());

        // HACK could be done without less unsafe: maybe_uninit_slice
        // and const-ly: const_mut_refs, const_slice_index
        let data = self.data.as_mut_ptr();
        let len = self.len();

        // SAFETY: type invariant (the first `len`-th bytes are initialized)
        unsafe { core::slice::from_raw_parts_mut(data.cast(), len) }
    }

    /// Returns `true` iff this representation is valid.
    #[inline]
    pub const fn is_valid(&self) -> bool {
        self.len.is_valid()
    }

    /// Returns the actual `const`-parameter for inline capacity of this type.
    #[inline]
    pub const fn capacity() -> usize {
        INLINE_CAPACITY
    }

    /// Pushes a short slice into this inline string.
    ///
    /// # Safety
    ///
    /// Does not check if the size with `addition` stays inside minimal capacity.
    #[inline]
    pub unsafe fn push_slice_unchecked(&mut self, addition: &[u8]) {
        let len = self.len();
        let add_len = addition.len();
        let new_len = len + add_len;

        debug_assert!(new_len <= INLINE_CAPACITY);

        unsafe {
            copy_nonoverlapping(
                addition.as_ptr().cast(),
                self.data.as_mut_ptr().add(len),
                add_len,
            );
        }

        self.len = TaggedLen::encode(new_len);
    }

    /// Returns the spare capacity of this inline vector as a slice of `MaybeUninit<u8>`.
    pub fn spare_capacity_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        let start = self.len();
        &mut self.data[start..]
    }

    /// Forces the length of the vector to `new_len`.
    ///
    /// # Safety
    ///
    /// * `new_len` should be must be less than or equal to `INLINE_CAPACITY`.
    /// * The elements at `old_len..new_len` must be initialized.
    pub unsafe fn set_len(&mut self, new_len: usize) {
        debug_assert!(new_len <= INLINE_CAPACITY);
        self.len = TaggedLen::encode(new_len);
    }
}
