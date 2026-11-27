//! Test allocator: the system allocator, with a switch that makes the next
//! allocation fail.
//!
//! [`fail_next`] arms a global atomic; the next `alloc`, `alloc_zeroed` or
//! `realloc` returns null and disarms it. To keep tests running in parallel
//! from stealing the failure, the atomic holds a token of the arming thread
//! and only that thread's allocations fail; and arming is serialized by
//! [`LOCK`] (one slot), which [`failing`] holds.

extern crate std;

use core::alloc::{GlobalAlloc, Layout};
use core::sync::atomic::{AtomicUsize, Ordering};
use std::alloc::System;

/// Held while armed: there is a single slot.
pub static LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

/// The arming thread's token, `0` when disarmed.
static FAIL_NEXT: AtomicUsize = AtomicUsize::new(0);

std::thread_local! {
    // const-initialized, no destructor: no allocation on access
    static TOKEN: u8 = const { 0 };
}

/// A nonzero token for the current thread (the address of a thread-local).
fn token() -> usize {
    TOKEN.with(|t| core::ptr::from_ref(t).addr())
}

/// Makes the next allocation of the current thread fail (hold [`LOCK`]).
pub fn fail_next() {
    FAIL_NEXT.store(token(), Ordering::SeqCst);
}

/// Whether a failure is still armed for the current thread (it is not once
/// an allocation has consumed it).
pub fn armed() -> bool {
    FAIL_NEXT.load(Ordering::SeqCst) == token()
}

/// Disarms, if the failure was not consumed.
pub fn disarm() {
    let _ = FAIL_NEXT.compare_exchange(token(), 0, Ordering::SeqCst, Ordering::SeqCst);
}

/// Runs `f` with the next allocation failing, and returns its result and
/// whether the failure was consumed.
pub fn failing<T>(f: impl FnOnce() -> T) -> (T, bool) {
    // a panicking test poisons it, harmlessly
    let _lock = LOCK
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    fail_next();
    let result = f();
    let consumed = !armed();
    disarm();
    (result, consumed)
}

/// Consumes the armed failure, if it is the current thread's.
fn should_fail() -> bool {
    // cheap check first: allocations of other threads and disarmed ones
    FAIL_NEXT.load(Ordering::Relaxed) != 0
        && FAIL_NEXT
            .compare_exchange(token(), 0, Ordering::SeqCst, Ordering::SeqCst)
            .is_ok()
}

pub struct FailingAlloc;

// SAFETY: delegates to `System`, or returns null (an allowed failure)
unsafe impl GlobalAlloc for FailingAlloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if should_fail() {
            return core::ptr::null_mut();
        }
        // SAFETY: caller's contract
        unsafe { System.alloc(layout) }
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        if should_fail() {
            return core::ptr::null_mut();
        }
        // SAFETY: caller's contract
        unsafe { System.alloc_zeroed(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        // SAFETY: caller's contract
        unsafe { System.dealloc(ptr, layout) }
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        if should_fail() {
            // the old block stays valid, as required
            return core::ptr::null_mut();
        }
        // SAFETY: caller's contract
        unsafe { System.realloc(ptr, layout, new_size) }
    }
}

#[global_allocator]
static GLOBAL: FailingAlloc = FailingAlloc;

#[cfg(test)]
mod tests {
    use alloc::vec::Vec;

    use super::*;

    #[test]
    fn next_alloc_fails_once() {
        let (r, consumed) = failing(|| Vec::<u8>::new().try_reserve(10));
        assert!(r.is_err());
        assert!(consumed);
        // disarmed afterwards
        assert!(Vec::<u8>::new().try_reserve(10).is_ok());
    }

    #[test]
    fn realloc_fails() {
        let mut v = Vec::<u8>::with_capacity(1);
        v.push(1);
        let (r, consumed) = failing(|| v.try_reserve(100));
        assert!(r.is_err() && consumed);
        assert_eq!(v, [1], "the old block is kept");
    }

    #[test]
    fn unconsumed_is_disarmed() {
        let ((), consumed) = failing(|| ());
        assert!(!consumed);
        assert!(!armed());
    }

    #[test]
    fn other_threads_unaffected() {
        use core::sync::atomic::AtomicU8;
        // 1: armed by the other thread, 2: allocated here
        let step = AtomicU8::new(0);
        std::thread::scope(|scope| {
            scope.spawn(|| {
                let _lock = LOCK
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner);
                fail_next();
                step.store(1, Ordering::SeqCst);
                while step.load(Ordering::SeqCst) != 2 {
                    core::hint::spin_loop();
                }
                assert!(armed(), "not consumed by the other thread");
                disarm();
            });
            while step.load(Ordering::SeqCst) != 1 {
                core::hint::spin_loop();
            }
            let ok = Vec::<u8>::new().try_reserve(10).is_ok();
            step.store(2, Ordering::SeqCst);
            assert!(ok);
        });
    }

    /// The crate's allocation-failure paths.
    mod oom {
        use alloc::string::ToString;
        use alloc::vec;

        use super::*;
        use crate::backend::Unique;
        use crate::thin::{Base, TryReserveErrorKind};
        use crate::{HipByt, HipStr, SmallByt, TinyByt};

        type B = Base<<Unique as crate::backend::Backend>::Counter>;

        fn is_alloc_error(e: &crate::thin::TryReserveError) -> bool {
            matches!(e.0, TryReserveErrorKind::AllocError { .. })
        }

        #[test]
        fn thin_with_capacity() {
            let (r, consumed) = failing(|| B::try_with_capacity(100));
            let e = r.err().unwrap();
            assert!(consumed && is_alloc_error(&e));
            assert!(e.to_string().starts_with("allocation error: layout"));
            // the conversion retries through `Vec`, which now succeeds: the
            // fallback is a capacity overflow (still an error)
            let _ = e.into_std();
        }

        #[test]
        fn thin_grow() {
            let mut b = B::try_with_capacity(1).unwrap();
            let cap = b.capacity();
            let (r, consumed) = failing(|| b.try_reserve(1000));
            assert!(consumed && is_alloc_error(&r.unwrap_err()));
            assert_eq!(b.capacity(), cap, "unchanged");
            // SAFETY: not used afterwards (`Base` has no destructor)
            unsafe { b.drop_container() };
            // from no allocation at all
            let mut b = B::new();
            let (r, _) = failing(|| unsafe { b.try_realloc(10) });
            assert!(is_alloc_error(&r.unwrap_err()));
            assert_eq!(b.capacity(), 0);
        }

        #[test]
        fn alloc_error_into_std() {
            // fail both the thin allocation and the `Vec` retry: the std
            // error is then an allocation error too
            let (r, _) = failing(|| B::try_with_capacity(100));
            let e = r.err().unwrap();
            let (std_e, consumed) = failing(|| e.into_std());
            assert!(consumed);
            assert!(!std_e.to_string().contains("capacity overflow"), "{std_e}");
        }

        #[test]
        fn hip_reserve() {
            let long = "x".repeat(100);
            // thin heap value
            let mut s = HipStr::from(long.as_str());
            let (r, consumed) = failing(|| s.try_reserve(1000));
            assert!(r.is_err() && consumed);
            assert_eq!(s, long.as_str(), "unchanged");
            // adopted vector: `Vec`'s own error
            let mut b = HipByt::from(vec![1u8; 100]);
            let (r, consumed) = failing(|| b.try_reserve(1000));
            assert!(r.is_err() && consumed);
            assert_eq!(b.len(), 100);
        }

        #[test]
        fn inline_to_heap() {
            let mut b = SmallByt::from(&b"ab"[..]);
            let (r, consumed) = failing(|| b.try_reserve(100));
            assert!(r.is_err() && consumed);
            assert_eq!(b, &b"ab"[..]);
            let mut b = TinyByt::from(&b"ab"[..]);
            let (r, consumed) = failing(|| b.try_reserve(100));
            assert!(r.is_err() && consumed);
            assert_eq!(b, &b"ab"[..]);
            let mut b = HipByt::from(&b"ab"[..]);
            let (r, consumed) = failing(|| b.try_reserve(100));
            assert!(r.is_err() && consumed);
            assert_eq!(b, &b"ab"[..]);
        }
    }
}
