//! Unstable allocated backend trait and the built-in implementations.

use std::rc::Rc;
use std::sync::Arc;

#[cfg(feature = "unstable")]
pub use private::AllocatedBackend;

/// Sealed marker trait for allocated backend.
#[cfg(not(feature = "unstable"))]
pub trait AllocatedBackend: private::AllocatedBackend {}

#[cfg(not(feature = "unstable"))]
impl AllocatedBackend for Local {}

#[cfg(not(feature = "unstable"))]
impl AllocatedBackend for ThreadSafe {}

/// Local reference counted backend.
pub type Local = Rc<Vec<u8>>;

/// Shared (thread-safe) reference counted backend.
pub type ThreadSafe = Arc<Vec<u8>>;

pub mod private {
    use std::mem::{align_of, ManuallyDrop};
    use std::rc::Rc;
    use std::sync::Arc;

    /// _Unsafe_ trait for reference counted allocated backend.
    ///
    /// # Safety
    ///
    /// This trait is unsafe because it requires lots of difficult invariants.
    ///
    /// * must be pointer sized
    /// * the [`RawPointer`][AllocatedBackend::RawPointer] too
    /// * the type should have the `Sync` and `Send` needed
    pub unsafe trait AllocatedBackend {
        /// Should be pointer sized! (and not a fat pointer)
        type RawPointer: Copy + Sized;

        /// Creates the allocated from a byte vector and returns its raw representation.
        fn new_raw(v: Vec<u8>) -> Self::RawPointer;

        unsafe fn increment_count(raw: Self::RawPointer);

        unsafe fn decrement_count(raw: Self::RawPointer);

        unsafe fn is_unique(raw: Self::RawPointer) -> bool;

        unsafe fn vec_ref<'a>(raw: Self::RawPointer) -> &'a Vec<u8>;

        unsafe fn try_unwrap(raw: Self::RawPointer) -> Result<Vec<u8>, Self::RawPointer>;

        fn is_valid(raw: Self::RawPointer) -> bool;
    }

    unsafe impl AllocatedBackend for Arc<Vec<u8>> {
        type RawPointer = *const Vec<u8>;
        #[inline]
        fn new_raw(v: Vec<u8>) -> Self::RawPointer {
            Self::into_raw(Self::new(v))
        }
        #[inline]
        unsafe fn increment_count(raw: Self::RawPointer) {
            unsafe { Self::increment_strong_count(raw) };
        }
        #[inline]
        unsafe fn decrement_count(raw: Self::RawPointer) {
            unsafe { Self::decrement_strong_count(raw) };
        }
        #[inline]
        unsafe fn is_unique(raw: Self::RawPointer) -> bool {
            let arc = ManuallyDrop::new(unsafe { Self::from_raw(raw) });
            Self::weak_count(&arc) == 0 && Self::strong_count(&arc) == 1
        }
        #[inline]
        unsafe fn vec_ref<'a>(raw: Self::RawPointer) -> &'a Vec<u8> {
            unsafe { &*raw }
        }
        #[inline]
        unsafe fn try_unwrap(raw: Self::RawPointer) -> Result<Vec<u8>, Self::RawPointer> {
            Self::try_unwrap(unsafe { Self::from_raw(raw) }).map_err(Self::into_raw)
        }
        #[inline]
        fn is_valid(raw: Self::RawPointer) -> bool {
            !raw.is_null() && raw.align_offset(align_of::<Self::RawPointer>()) == 0
        }
    }

    unsafe impl AllocatedBackend for Rc<Vec<u8>> {
        type RawPointer = *const Vec<u8>;
        #[inline]
        fn new_raw(v: Vec<u8>) -> Self::RawPointer {
            Self::into_raw(Self::new(v))
        }
        #[inline]
        unsafe fn increment_count(raw: Self::RawPointer) {
            unsafe { Self::increment_strong_count(raw) };
        }
        #[inline]
        unsafe fn decrement_count(raw: Self::RawPointer) {
            unsafe { Self::decrement_strong_count(raw) };
        }
        #[inline]
        unsafe fn is_unique(raw: Self::RawPointer) -> bool {
            let arc = ManuallyDrop::new(unsafe { Self::from_raw(raw) });
            Self::weak_count(&arc) == 0 && Self::strong_count(&arc) == 1
        }
        #[inline]
        unsafe fn vec_ref<'a>(raw: Self::RawPointer) -> &'a Vec<u8> {
            unsafe { &*raw }
        }
        #[inline]
        unsafe fn try_unwrap(raw: Self::RawPointer) -> Result<Vec<u8>, Self::RawPointer> {
            Self::try_unwrap(unsafe { Self::from_raw(raw) }).map_err(Self::into_raw)
        }
        #[inline]
        fn is_valid(raw: Self::RawPointer) -> bool {
            !raw.is_null() && raw.align_offset(align_of::<Self::RawPointer>()) == 0
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_basic_rc() {
        test_backend::<Local>();
    }

    #[test]
    fn test_basic_arc() {
        test_backend::<ThreadSafe>();
    }

    fn test_backend<B: AllocatedBackend>() {
        let v = vec![42; 42];
        unsafe {
            let r = B::new_raw(v);
            assert!(B::is_valid(r));
            assert!(B::is_unique(r));
            {
                let v = B::vec_ref(r);
                assert_eq!(v.len(), 42);
            }
            B::increment_count(r);
            assert!(!B::is_unique(r));
            B::decrement_count(r);

            let v = B::try_unwrap(r).unwrap_or_else(|_| panic!());
            assert_eq!(v.len(), 42);
        }
    }
}
