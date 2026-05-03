//! Tagged pointers.

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

impl<T, const TAG: usize> core::fmt::Debug for TaggedPointer<T, TAG> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.as_ptr().fmt(f)
    }
}

impl<T, const TAG: usize> core::fmt::Pointer for TaggedPointer<T, TAG> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.as_ptr().fmt(f)
    }
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

    const NULL: Self = Self {
        ptr: NonNull::without_provenance(NonZeroUsize::new(TAG).unwrap()),
    };

    /// Creates a null tagged pointer.
    #[inline]
    pub const fn null() -> Self {
        Self::debug_check();

        Self::NULL
    }
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

impl<T, const TAG: usize> TryFrom<TaggedPointer<T, TAG>> for NonNull<T> {
    type Error = ();

    #[inline]
    fn try_from(tagged: TaggedPointer<T, TAG>) -> Result<Self, Self::Error> {
        tagged.as_non_null().ok_or(())
    }
}
