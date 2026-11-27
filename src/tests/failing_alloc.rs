//! Test allocator: the system allocator, with a switch that makes the next
//! allocation fail.
//!
//! [`arm`] sets a global atomic; the next `alloc`, `alloc_zeroed` or
//! `realloc` returns null and clears it. Only one test at a time can have the
//! failing allocator on: arming takes a global mutex, held by the returned
//! [`Armed`] guard until it is dropped. The atomic also holds a token of the
//! arming thread, so that allocations of tests running in parallel (which do
//! not arm) do not consume the failure.

#![cfg_attr(coverage_nightly, coverage(off))]

extern crate std;

use core::alloc::{GlobalAlloc, Layout};
use core::sync::atomic::{AtomicUsize, Ordering};
use std::alloc::System;
use std::sync::{Mutex, MutexGuard, PoisonError};

/// Held while the failing allocator is on: one test at a time.
static LOCK: Mutex<()> = Mutex::new(());

/// The arming thread's token, `0` when off.
static FAIL_NEXT: AtomicUsize = AtomicUsize::new(0);

std::thread_local! {
    // const-initialized, no destructor: no allocation on access
    static TOKEN: u8 = const { 0 };
}

/// A nonzero token for the current thread (the address of a thread-local).
fn token() -> usize {
    TOKEN.with(|t| core::ptr::from_ref(t).addr())
}

/// The failing allocator, on for the current thread until the failure is
/// consumed or the guard dropped; other tests wait in [`arm`] meanwhile.
#[must_use]
pub struct Armed {
    token: usize,
    _lock: MutexGuard<'static, ()>,
}

impl Armed {
    /// Whether an allocation has consumed the failure.
    pub fn consumed(&self) -> bool {
        FAIL_NEXT.load(Ordering::SeqCst) != self.token
    }
}

impl Drop for Armed {
    fn drop(&mut self) {
        // off before the lock is released (fields drop after this)
        let _ = FAIL_NEXT.compare_exchange(self.token, 0, Ordering::SeqCst, Ordering::SeqCst);
    }
}

/// Makes the next allocation of the current thread fail, waiting for any
/// other test using the failing allocator to finish.
pub fn arm() -> Armed {
    // a test panicking while armed poisons it, harmlessly: its guard turned
    // the allocator off while unwinding
    let lock = LOCK.lock().unwrap_or_else(PoisonError::into_inner);
    let token = token();
    FAIL_NEXT.store(token, Ordering::SeqCst);
    Armed { token, _lock: lock }
}

/// Runs `f` with the next allocation failing, and returns its result and
/// whether the failure was consumed.
pub fn failing<T>(f: impl FnOnce() -> T) -> (T, bool) {
    let armed = arm();
    let result = f();
    (result, armed.consumed())
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
        assert_eq!(FAIL_NEXT.load(Ordering::SeqCst), 0);
    }

    #[test]
    #[allow(
        clippy::significant_drop_tightening,
        reason = "armed while the main thread allocates"
    )]
    fn other_threads_unaffected() {
        use core::sync::atomic::AtomicU8;
        // 1: armed by the other thread, 2: allocated here
        let step = AtomicU8::new(0);
        std::thread::scope(|scope| {
            scope.spawn(|| {
                #[allow(
                    clippy::significant_drop_tightening,
                    reason = "armed while the main thread allocates"
                )]
                let armed = arm();
                step.store(1, Ordering::SeqCst);
                while step.load(Ordering::SeqCst) != 2 {
                    core::hint::spin_loop();
                }
                assert!(!armed.consumed(), "not consumed by the other thread");
            });
            while step.load(Ordering::SeqCst) != 1 {
                core::hint::spin_loop();
            }
            let ok = Vec::<u8>::new().try_reserve(10).is_ok();
            step.store(2, Ordering::SeqCst);
            assert!(ok);
        });
    }

    #[test]
    fn one_test_at_a_time() {
        use core::sync::atomic::AtomicU8;
        // 1: armed here, 2: armed by the other thread
        let step = AtomicU8::new(0);
        std::thread::scope(|scope| {
            // spawned before arming: spawning allocates
            let waiter = scope.spawn(|| {
                while step.load(Ordering::SeqCst) != 1 {
                    core::hint::spin_loop();
                }
                let _guard = arm();
                step.store(2, Ordering::SeqCst);
            });
            let armed = arm();
            step.store(1, Ordering::SeqCst);
            // the other thread blocks in `arm` while this one is armed
            for _ in 0..1000 {
                std::thread::yield_now();
            }
            let blocked = step.load(Ordering::SeqCst) == 1;
            drop(armed);
            waiter.join().unwrap();
            assert!(blocked);
            assert_eq!(step.load(Ordering::SeqCst), 2);
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
