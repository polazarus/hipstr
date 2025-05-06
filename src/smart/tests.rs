use alloc::vec;
use alloc::vec::Vec;
use core::cmp::Ordering;
#[cfg(all(not(loom), feature = "std"))]
use std::sync;
#[cfg(all(not(loom), feature = "std"))]
use std::thread;

#[cfg(loom)]
use loom::{sync, thread};

use super::*;
use crate::backend::PanickyUnique;
use crate::{Arc, Rc, Unique};

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

    assert_eq!(Smart::try_unwrap(a).unwrap_or(0), 1);
    assert_eq!(Smart::try_unwrap(b).unwrap_or(0), 1);
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
    assert!(Smart::try_unwrap(b).is_err());

    assert!(a.as_mut().is_some());
    assert_eq!(Smart::try_unwrap(a).unwrap_or(0), 1);
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
    assert!(Smart::try_unwrap(a).is_err());

    assert_eq!(b.ref_count(), 1);
    assert!(b.as_mut().is_some());
    assert_eq!(Smart::try_unwrap(b).unwrap_or(0), 1);
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
#[cfg(feature = "std")]
fn test_local_clone_overflow() {
    let a = L::new(42);

    assert_eq!(a.inner().count.get(), 1);
    // artificially set the count to MAX
    a.inner().count.0.set(usize::MAX);

    let result = std::panic::catch_unwind(|| {
        let _ = a.clone();
    });
    assert!(result.is_err());

    assert_eq!(a.inner().count.get(), usize::MAX);
    // reset the count to 1
    a.inner().count.set(1);
}

#[test]
#[cfg(feature = "std")]
fn test_atomic_st_clone_overflow() {
    let a = T::new(42);

    assert_eq!(a.inner().count.get(), 1);
    // artificially set the count to MAX
    a.inner().count.set(usize::MAX);

    let result = std::panic::catch_unwind(|| {
        let _ = a.clone();
    });
    assert!(result.is_err());

    assert_eq!(a.inner().count.get(), usize::MAX);
    // reset the count to 1
    a.inner().count.set(1);
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

    const THREADS: usize = 3;
    const N: usize = usize::MAX - THREADS;

    // artificially set the count to N
    a.inner().count.set(N);

    let ths = [(); THREADS].map(|_| a.clone()).map(|b| {
        thread::spawn(move || {
            let c = b.clone();
            drop(c);
        })
    });

    let errors: Vec<bool> = ths
        .into_iter()
        .map(thread::JoinHandle::join)
        .map(|result| result.is_err())
        .collect();
    assert!(errors.into_iter().any(|b| b)); // at least one of the thread should panic

    // check that the count is still N
    // that is, the drop of the moved clones did occur
    assert_eq!(a.inner().count.get(), N);

    // reset the count to 1
    a.inner().count.set(1);

    drop(a);
    assert_eq!(witness.clones(), witness.drops());
}

#[test]
#[cfg(loom)]
#[should_panic(expected = "overflow")]
fn loom_atomic_mt_clone_overflow() {
    loom::model(test_atomic_mt_clone_overflow);
}

#[test]
fn force_clone() {
    let v = Smart::<_, PanickyUnique>::new(vec![1, 2, 3]);
    let w = Smart::force_clone(&v);
    assert_eq!(w.as_slice(), [1, 2, 3]);
    assert_ne!(v.as_ptr(), w.as_ptr());

    let v = Smart::<_, Arc>::new(vec![1, 2, 3]);
    let w = Smart::force_clone(&v);
    assert_eq!(w.as_slice(), [1, 2, 3]);
    assert_eq!(v.as_ptr(), w.as_ptr());
}

#[test]
fn mutate() {
    let mut v = Smart::<_, Arc>::new(vec![1, 2, 3]);
    assert_eq!(v.as_slice(), [1, 2, 3]);

    Smart::mutate(&mut v).push(4);
    assert_eq!(v.as_slice(), [1, 2, 3, 4]);

    let w = v.clone();

    Smart::mutate(&mut v).pop();
    assert_eq!(v.as_slice(), [1, 2, 3]);
    assert_eq!(w.as_slice(), [1, 2, 3, 4]);
}

#[test]
fn mutate_copy() {
    let mut v = Smart::<_, Arc>::new(1);
    assert_eq!(*v, 1);

    *Smart::mutate_copy(&mut v) += 1;
    assert_eq!(*v, 2);

    let w = v.clone();

    *Smart::mutate_copy(&mut v) += 1;
    assert_eq!(*v, 3);
    assert_eq!(*w, 2);
}

#[test]
#[cfg(feature = "std")]
fn hash() {
    use std::hash::{BuildHasher, BuildHasherDefault, DefaultHasher};
    let hasher = BuildHasherDefault::<DefaultHasher>::new();

    let mut v = Smart::<_, Arc>::new(vec![1, 2, 3]);

    assert_eq!(v.as_slice(), [1, 2, 3]);
    let slice_hash = hasher.hash_one(v.as_slice());

    let hash = hasher.hash_one(&v);
    assert_eq!(hash, slice_hash);

    let w = v.clone();
    let clone_hash = hasher.hash_one(&w);
    assert_eq!(hash, clone_hash);

    Smart::mutate(&mut v).push(4);
    let new_hash = hasher.hash_one(&v);
    assert_ne!(hash, new_hash);
}

#[test]
fn borrow() {
    let v = Smart::<_, Arc>::new(1);
    assert_eq!(v.as_ref(), &1);
    assert_eq!(<_ as Borrow<i32>>::borrow(&v), &1_i32);
    assert!(ptr::eq(v.as_ref(), v.borrow()));
}

#[test]
fn default() {
    let v = Smart::<i32, Arc>::default();
    assert_eq!(*v, 0);

    let v = Smart::<Vec<i32>, Arc>::default();
    let empty: &[i32] = &[];
    assert_eq!(v.as_slice(), empty);
}

#[test]
#[cfg(feature = "std")]
fn fmt() {
    use std::format;
    let v = Smart::<_, Arc>::new(1);
    assert_eq!(format!("{:?}", v), "1");
    assert_eq!(format!("{}", v), "1");
    assert_eq!(format!("{:p}", v), format!("{:p}", ptr::from_ref(&*v)));
}

#[test]
fn eq() {
    let v = Smart::<_, Arc>::new(1);
    let w = Smart::<_, Arc>::new(1);
    let x = Smart::<_, Arc>::new(2);
    assert_eq!(v, w);
    assert_ne!(v, x);
    assert_eq!(v.as_ref(), w.as_ref());
    assert_ne!(v.as_ref(), x.as_ref());

    let v = Smart::<_, Arc>::new(vec![1, 2, 3]);
    let w = Smart::<_, Arc>::new(vec![1, 2, 3]);
    assert_eq!(v, w);
    assert_eq!(v.as_slice(), w.as_slice());
}

#[test]
fn cmp() {
    let v = Smart::<_, Arc>::new(1);
    let w = Smart::<_, Arc>::new(1);
    let x = Smart::<_, Arc>::new(2);
    assert_eq!(v.cmp(&w), Ordering::Equal);
    assert_eq!(v.cmp(&x), Ordering::Less);
    assert_eq!(v.as_ref().cmp(w.as_ref()), Ordering::Equal);
    assert_eq!(v.as_ref().cmp(x.as_ref()), Ordering::Less);
}
