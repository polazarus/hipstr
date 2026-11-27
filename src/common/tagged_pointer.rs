//! Tagged pointers.

use alloc::boxed::Box;
use core::num::NonZeroUsize;
use core::ptr::{self, NonNull};

union Pivot<T> {
    ptr: NonNull<T>,
    val: NonZeroUsize,
}

#[inline]
const fn is_value<T>(ptr: NonNull<T>, val: usize) -> bool {
    unsafe { Pivot { ptr }.val.get() == val }
}

/// A pointer tagged with a constant tag.
#[repr(transparent)]
pub struct TaggedPointer<T, const TAG: usize> {
    ptr: NonNull<T>,
}

impl<T, const TAG: usize> Copy for TaggedPointer<T, TAG> {}

impl<T, const TAG: usize> Clone for TaggedPointer<T, TAG> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T, const TAG: usize> TaggedPointer<T, TAG> {
    pub const fn debug_check() {
        #[cfg(debug_assertions)]
        {
            assert!(
                TAG != 0,
                "invalid tag (zero is reserved for niche optimization)"
            );
            let max_tag = align_of::<T>() - 1;
            assert!(
                TAG <= max_tag,
                "invalid tag (too large for the alignment niche)"
            );
        }
    }

    /// Retrieves the original pointer without the tag.
    #[inline]
    pub const fn as_non_null(self) -> Option<NonNull<T>> {
        NonNull::new(self.as_ptr())
    }

    /// Retrieves the original pointer without the tag, panicking if the pointer is null.
    #[inline]
    pub const fn as_ptr(self) -> *mut T {
        if is_value(self.ptr, TAG) {
            ptr::null_mut()
        } else {
            unsafe { self.ptr.as_ptr().byte_sub(TAG) }
        }
    }

    /// The null tagged pointer.
    pub const NULL: Self = {
        Self::debug_check();
        Self {
            ptr: NonNull::without_provenance(NonZeroUsize::new(TAG).unwrap()),
        }
    };
}

/// Converts a non-null pointer to a new tagged pointer.
///
/// # Safety
///
/// The pointer should be properly aligned for the type `T`. and the tag `TAG`.
/// The tag is stored in the least significant bits of the pointer,
/// so the pointer must be aligned to at least the power of two greather than `TAG` bytes.
impl<T, const TAG: usize> From<NonNull<T>> for TaggedPointer<T, TAG> {
    #[inline]
    fn from(ptr: NonNull<T>) -> Self {
        debug_assert!(
            ptr.is_aligned(),
            "pointer must be properly aligned for tagging"
        );

        Self::debug_check();
        let ptr = unsafe { ptr.byte_add(TAG) };
        Self { ptr }
    }
}

impl<T, const TAG: usize> From<Box<T>> for TaggedPointer<T, TAG> {
    #[inline]
    fn from(b: Box<T>) -> Self {
        let p = Box::into_raw(b);
        Self::from(unsafe { NonNull::new_unchecked(p) })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[allow(clippy::clone_on_copy, reason = "covers the impl")]
    fn clone_is_a_copy() {
        let p = TaggedPointer::<u64, 2>::NULL;
        assert!(p.clone().as_non_null().is_none());
    }
}
