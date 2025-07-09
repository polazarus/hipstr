use core::marker::PhantomData;

use crate::vecs::TAG_BORROWED;

#[repr(usize)]
#[derive(Clone, Copy)]
pub(crate) enum BorrowedTag {
    Value = TAG_BORROWED as usize, // reuse a tag of a fat vector
}

#[repr(C)]
pub(crate) struct Borrowed<'borrow, T> {
    #[cfg(target_endian = "little")]
    pub(crate) tag: BorrowedTag,

    pub(crate) ptr: *const T,

    pub(crate) len: usize,

    #[cfg(target_endian = "big")]
    pub tag: BorrowedTag,

    pub(crate) phantom: PhantomData<&'borrow [T]>,
}

impl<'borrow, T> Borrowed<'borrow, T> {
    #[inline]
    pub(crate) const fn new(slice: &'borrow [T]) -> Self {
        Self {
            tag: BorrowedTag::Value,
            ptr: slice.as_ptr(),
            len: slice.len(),
            phantom: PhantomData,
        }
    }

    #[inline]
    pub(crate) const fn as_slice(&self) -> &'borrow [T] {
        // SAFETY: validity ensured by construction.
        unsafe { core::slice::from_raw_parts(self.ptr as *const T, self.len) }
    }
}

impl<'borrow, T> Copy for Borrowed<'borrow, T> {}

impl<'borrow, T> Clone for Borrowed<'borrow, T> {
    fn clone(&self) -> Self {
        *self
    }
}
