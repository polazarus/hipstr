//! Unstable allocated backend trait and the built-in implementations.

use std::rc::Rc;
use std::sync::Arc;

#[cfg(feature = "unstable")]
pub use private::Backend;

/// Sealed marker trait for allocated backend.
#[cfg(not(feature = "unstable"))]
pub trait Backend: private::Backend {}

#[cfg(not(feature = "unstable"))]
impl Backend for Local {}

#[cfg(not(feature = "unstable"))]
impl Backend for ThreadSafe {}

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
    pub unsafe trait Backend: Sized {
        /// Should be pointer sized! (and not a fat pointer)
        type RawPointer: Copy + Sized;

        /// Creates the allocated backend from a byte vector and returns its raw representation.
        fn new(v: Vec<u8>) -> Self;

        /// Tries to unwrap the vector from the backend.
        ///
        /// # Errors
        ///
        /// Returns the backend itself if the unwrap is impossible, typically
        /// the reference is not unique.
        fn try_unwrap(self) -> Result<Vec<u8>, Self>;

        /// Gets a raw representation of the backend.
        fn into_raw(self) -> Self::RawPointer;

        /// Gets the backend back from a raw representation.
        ///
        /// # Safety
        ///
        /// The raw pointer should be one corresponding to a valid backend.
        unsafe fn from_raw(raw: Self::RawPointer) -> Self;

        /// Increments the (strong) count.
        ///
        /// # Safety
        ///
        /// The raw pointer should be one corresponding to a valid backend.
        unsafe fn raw_increment_count(raw: Self::RawPointer);

        /// Decrements the (strong) count, invalidating the raw pointer if the
        /// reference count reaches 0.
        ///
        /// # Safety
        ///
        /// The raw pointer should be one corresponding to a valid backend.
        unsafe fn raw_decrement_count(raw: Self::RawPointer);

        /// Checks if their is only one reference.
        ///
        /// # Safety
        ///
        /// The raw pointer should be one corresponding to a valid backend.
        unsafe fn raw_is_unique(raw: Self::RawPointer) -> bool;

        /// Returns a reference to underlying vector.
        ///
        /// # Safety
        ///
        /// The raw pointer should be one corresponding to a valid backend and
        /// stay valid for lifetime `'a`.
        unsafe fn raw_as_vec<'a>(raw: Self::RawPointer) -> &'a Vec<u8>;

        /// Try to unwrap the vector from the backend.
        ///
        /// # Errors
        ///
        /// Returns the original raw pointer if the reference is not unique.
        ///
        /// # Safety
        ///
        /// The raw pointer should be one corresponding to a valid backend.
        unsafe fn raw_try_unwrap(raw: Self::RawPointer) -> Result<Vec<u8>, Self::RawPointer> {
            let backend = unsafe { Self::from_raw(raw) };
            backend.try_unwrap().map_err(Self::into_raw)
        }

        /// Superficially checks if the raw pointer is valid.
        /// For debugging purposes only.
        fn raw_is_valid(raw: Self::RawPointer) -> bool;
    }

    unsafe impl Backend for Arc<Vec<u8>> {
        type RawPointer = *const Vec<u8>;

        #[inline]
        fn new(v: Vec<u8>) -> Self {
            Self::new(v)
        }

        #[inline]
        fn into_raw(self) -> Self::RawPointer {
            Self::into_raw(self)
        }

        #[inline]
        unsafe fn from_raw(raw: Self::RawPointer) -> Self {
            unsafe { Self::from_raw(raw) }
        }

        #[inline]
        unsafe fn raw_increment_count(raw: Self::RawPointer) {
            unsafe { Self::increment_strong_count(raw) };
        }

        #[inline]
        unsafe fn raw_decrement_count(raw: Self::RawPointer) {
            unsafe { Self::decrement_strong_count(raw) };
        }

        #[inline]
        unsafe fn raw_is_unique(raw: Self::RawPointer) -> bool {
            let arc = ManuallyDrop::new(unsafe { Self::from_raw(raw) });
            Self::weak_count(&arc) == 0 && Self::strong_count(&arc) == 1
        }
        #[inline]
        unsafe fn raw_as_vec<'a>(raw: Self::RawPointer) -> &'a Vec<u8> {
            unsafe { &*raw }
        }
        #[inline]
        fn try_unwrap(self) -> Result<Vec<u8>, Self> {
            Self::try_unwrap(self)
        }
        #[inline]
        fn raw_is_valid(raw: Self::RawPointer) -> bool {
            !raw.is_null() && raw.align_offset(align_of::<Self::RawPointer>()) == 0
        }
    }

    unsafe impl Backend for Rc<Vec<u8>> {
        type RawPointer = *const Vec<u8>;

        #[inline]
        fn new(v: Vec<u8>) -> Self {
            Self::new(v)
        }

        #[inline]
        fn try_unwrap(self) -> Result<Vec<u8>, Self> {
            Self::try_unwrap(self)
        }

        #[inline]
        fn into_raw(self) -> Self::RawPointer {
            Self::into_raw(self)
        }

        #[inline]
        unsafe fn from_raw(raw: Self::RawPointer) -> Self {
            unsafe { Self::from_raw(raw) }
        }

        #[inline]
        unsafe fn raw_increment_count(raw: Self::RawPointer) {
            // SAFETY: the raw pointer should be to a Rc<Vec<u8>>
            unsafe { Self::increment_strong_count(raw) };
        }
        #[inline]
        unsafe fn raw_decrement_count(raw: Self::RawPointer) {
            // SAFETY: the raw pointer should be to a Rc<Vec<u8>>
            unsafe { Self::decrement_strong_count(raw) };
        }
        #[inline]
        unsafe fn raw_is_unique(raw: Self::RawPointer) -> bool {
            let arc = ManuallyDrop::new(unsafe { Self::from_raw(raw) });
            Self::weak_count(&arc) == 0 && Self::strong_count(&arc) == 1
        }
        #[inline]
        unsafe fn raw_as_vec<'a>(raw: Self::RawPointer) -> &'a Vec<u8> {
            unsafe { &*raw }
        }
        #[inline]
        fn raw_is_valid(raw: Self::RawPointer) -> bool {
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

    fn test_backend<B: Backend>() {
        let v = vec![42; 42];
        unsafe {
            let r = B::into_raw(B::new(v));
            assert!(B::raw_is_valid(r));
            assert!(B::raw_is_unique(r));
            {
                let v = B::raw_as_vec(r);
                assert_eq!(v.len(), 42);
            }
            B::raw_increment_count(r);
            assert!(!B::raw_is_unique(r));
            B::raw_decrement_count(r);

            let v = B::raw_try_unwrap(r).unwrap_or_else(|_| panic!());
            assert_eq!(v.len(), 42);
        }
    }
}
