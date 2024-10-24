#[cfg(all(not(loom), feature = "std"))]
use std::sync;
#[cfg(all(not(loom), feature = "std"))]
use std::thread;

#[cfg(loom)]
use loom::{sync, thread};

use super::*;

type U<E> = Smart<E, Unique>;
type L<E> = Smart<E, Rc>;
type T<E> = Smart<E, Arc>;

mod local_witness {
    use alloc::rc::Rc;
    use core::cell::Cell;

    /// A `Clone`-able witness that counts drop calls.
    #[derive(Default)]
    pub struct Witness {
        clones: Rc<Cell<usize>>,
        drops: Rc<Cell<usize>>,
    }

    impl Witness {
        pub fn clones(&self) -> usize {
            self.clones.get()
        }

        pub fn drops(&self) -> usize {
            self.drops.get()
        }
    }

    impl Clone for Witness {
        fn clone(&self) -> Self {
            self.clones.set(self.clones.get().saturating_add(1));
            Self {
                clones: self.clones.clone(),
                drops: self.drops.clone(),
            }
        }
    }

    impl Drop for Witness {
        fn drop(&mut self) {
            self.drops.set(self.drops.get().saturating_add(1))
        }
    }
}

mod atomic_witness {
    use alloc::sync::Arc;
    use core::sync::atomic::{AtomicUsize, Ordering};

    #[derive(Default)]
    pub struct Witness {
        clones: Arc<AtomicUsize>,
        drops: Arc<AtomicUsize>,
    }

    impl Witness {
        pub fn clones(&self) -> usize {
            self.clones.load(Ordering::Acquire)
        }

        pub fn drops(&self) -> usize {
            self.drops.load(Ordering::Acquire)
        }
    }

    impl Clone for Witness {
        fn clone(&self) -> Self {
            let _ = self.clones.fetch_add(1, Ordering::AcqRel);
            Self {
                clones: self.clones.clone(),
                drops: self.drops.clone(),
            }
        }
    }

    impl Drop for Witness {
        fn drop(&mut self) {
            let _ = self.drops.fetch_add(1, Ordering::AcqRel);
        }
    }
}

#[test]
fn test_unique_misc() {
    let mut a = U::new(1);
    assert_eq!(a.as_ref(), &1);

    let mut b = a.clone();

    assert_eq!(a.ref_count(), 1);
    assert!(a.is_unique());
    assert!(a.as_mut().is_some());
    assert_eq!(b.as_ref(), &1);

    assert_eq!(b.ref_count(), 1);
    assert!(b.is_unique());
    assert!(b.as_mut().is_some());
    assert_eq!(b.as_ref(), &1);

    assert_eq!(a.try_unwrap().unwrap_or(0), 1);
    assert_eq!(b.try_unwrap().unwrap_or(0), 1);
}

#[test]
fn test_unique_drop() {
    let witness = local_witness::Witness::default();
    let _ = U::new(witness.clone());
    assert_eq!(witness.clones(), 1);
    assert_eq!(witness.drops(), 1);
}

#[test]
fn test_unique_clone_drop() {
    let witness = local_witness::Witness::default();
    {
        let a = U::new(witness.clone());
        let _ = a.clone();
    }
    assert_eq!(witness.clones(), 2);
    assert_eq!(witness.drops(), 2);
}

#[test]
fn test_local_misc() {
    let mut a = L::new(1);
    assert_eq!(a.as_ref(), &1);

    let mut b = a.clone();
    assert_eq!(a.ref_count(), 2);
    assert_eq!(b.ref_count(), 2);

    assert!(a.as_mut().is_none());
    assert!(b.as_mut().is_none());

    assert_eq!(b.as_ref(), &1);

    // will drop b
    assert!(b.try_unwrap().is_err());

    assert!(a.as_mut().is_some());
    assert_eq!(a.try_unwrap().unwrap_or(0), 1);
}

#[test]
fn test_local_drop() {
    let witness = local_witness::Witness::default();
    let _ = L::new(witness.clone());
    assert_eq!(witness.clones(), 1);
    assert_eq!(witness.drops(), 1);
}

#[test]
fn test_local_clone_drop() {
    let witness = local_witness::Witness::default();
    {
        let a = L::new(witness.clone());
        let _ = a.clone();
        let _ = a.clone();
    }
    assert_eq!(witness.clones(), 1);
    assert_eq!(witness.drops(), 1);
}

#[test]
fn test_atomic_misc() {
    let a = T::new(1);
    assert_eq!(a.as_ref(), &1);

    let a_raw = a.0; // could be just `a.0`
    assert_eq!(unsafe { a_raw.as_ref().value }, 1);
    assert_eq!(unsafe { a_raw.as_ref().count.get() }, 1);

    let mut b = a.clone();
    assert_eq!(a.ref_count(), 2);
    assert_eq!(b.ref_count(), 2);
    assert_eq!(b.as_ref(), &1);
    assert!(b.as_mut().is_none());

    // will drop a
    assert!(a.try_unwrap().is_err());

    assert_eq!(b.ref_count(), 1);
    assert!(b.as_mut().is_some());
    assert_eq!(b.try_unwrap().unwrap_or(0), 1);
}

#[test]
fn test_atomic_st_drop() {
    let witness = local_witness::Witness::default();
    let _ = T::new(witness.clone());
    assert_eq!(witness.clones(), 1);
    assert_eq!(witness.drops(), 1);
}

#[test]
fn test_atomic_st_clone_drop() {
    let witness = local_witness::Witness::default();
    {
        let a = T::new(witness.clone());
        {
            let _b = a.clone();
            assert_eq!(a.inner().count.get(), 2);
        }
        {
            let _c = a.clone();
            assert_eq!(a.inner().count.get(), 2);
        }
    }
    assert_eq!(witness.clones(), 1);
    assert_eq!(witness.drops(), 1);
}

#[test]
fn test_local_clone_overflow() {
    let witness = local_witness::Witness::default();
    {
        let a = L::new(witness.clone());
        assert_eq!(a.inner().count.get(), 1);
        a.inner().count.0.set(usize::MAX - 1);

        {
            let b = a.clone();
            assert_eq!(a.inner().count.get(), usize::MAX);
            assert_eq!(b.inner().count.get(), 1);
            // drop b
        }
        assert_eq!(witness.clones(), 2);
        assert_eq!(witness.drops(), 1);

        a.inner().count.0.set(0);
        // drop a
    }
    assert_eq!(witness.clones(), 2);
    assert_eq!(witness.drops(), 2);
}

#[test]
fn test_atomic_st_clone_overflow() {
    let witness = local_witness::Witness::default();
    {
        let a = T::new(witness.clone());
        assert_eq!(a.inner().count.get(), 1);
        a.inner().count.0.store(usize::MAX - 1, Ordering::Release);

        {
            let b = a.clone();
            assert_eq!(a.inner().count.get(), usize::MAX);
            assert_eq!(b.inner().count.get(), 1);
            // drop b
        }
        assert_eq!(witness.clones(), 2);
        assert_eq!(witness.drops(), 1);

        a.inner().count.0.store(0, Ordering::Release);
        // drop a
    }
    assert_eq!(witness.clones(), 2);
    assert_eq!(witness.drops(), 2);
}

#[test]
#[cfg(any(loom, feature = "std"))]
fn test_atomic_mt_clone_move_and_drop() {
    let witness = atomic_witness::Witness::default();
    let num = T::new(witness.clone());

    let ths = [(); 2].map(|_| {
        let num = num.clone();
        thread::spawn(move || {
            let _ = num;
        })
    });

    for th in ths {
        th.join().unwrap();
    }
    assert_eq!(witness.clones(), 1);
    assert_eq!(witness.drops(), 0);
}

#[test]
#[cfg(loom)]
fn loom_atomic_mt_clone_move_and_drop() {
    loom::model(test_atomic_mt_clone_move_and_drop);
}

#[test]
#[cfg(any(loom, feature = "std"))]
fn test_atomic_mt_orderly_drop() {
    let (tx, rx) = sync::mpsc::channel();
    let num = T::new(0);

    let t1 = thread::spawn(move || {
        let num = rx.recv().unwrap();
        let _ = num;
    });
    let t2 = thread::spawn(move || {
        tx.send(num.clone()).unwrap();
        let _ = num;
    });
    t1.join().unwrap();
    t2.join().unwrap();
}

#[test]
#[cfg(loom)]
fn loom_atomic_mt_orderly_drop() {
    loom::model(test_atomic_mt_orderly_drop);
}

#[test]
#[cfg(any(loom, feature = "std"))]
fn test_atomic_mt_orderly_drop2() {
    let witness = atomic_witness::Witness::default();
    let n0 = T::new(witness.clone());

    let n1 = n0.clone();
    let t1 = thread::spawn(move || {
        drop(n1);
    });
    let n2 = n0.clone();
    let t2 = thread::spawn(move || {
        drop(n2);
    });
    drop(n0);

    t1.join().unwrap();
    t2.join().unwrap();
    assert_eq!(witness.clones(), witness.drops());
}

#[test]
#[cfg(loom)]
fn loom_atomic_mt_orderly_drop2() {
    loom::model(test_atomic_mt_orderly_drop2);
}

#[test]
#[cfg(any(loom, feature = "std"))]
fn test_atomic_mt_clone_overflow() {
    let witness = atomic_witness::Witness::default();
    let a = T::new(witness.clone());

    const N: usize = usize::MAX - 3;

    a.inner().count.0.store(N, Ordering::Release);

    let ths = [(); 2].map(|_| {
        let b = a.clone();
        thread::spawn(move || {
            let c = b.clone();
            drop(c);
        })
    });

    for th in ths {
        th.join().unwrap();
    }

    assert_eq!(
        a.inner()
            .count
            .0
            .compare_exchange(N, 0, Ordering::AcqRel, Ordering::Acquire),
        Ok(N)
    );

    drop(a);
    assert_eq!(witness.clones(), witness.drops());
}

#[test]
#[cfg(loom)]
fn loom_atomic_mt_clone_overflow() {
    loom::model(test_atomic_mt_clone_overflow);
}
