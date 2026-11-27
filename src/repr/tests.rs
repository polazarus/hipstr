use alloc::vec;
use alloc::vec::Vec;

use super::*;
use crate::backend::{Arc, Rc, Unique};

/// Representative lengths around the inline capacity of `R`.
fn lengths<R: Repr<'static>>() -> Vec<usize> {
    let c = R::INLINE_CAPACITY;
    vec![0, 1, c - 1, c, c + 1, 2 * c + 3, 1000]
}

/// Static data, so that borrowing representations can borrow it for `'static`.
static POOL: [u8; 2000] = {
    let mut a = [0; 2000];
    let mut i = 0;
    while i < a.len() {
        a[i] = (i * 7 + 3) as u8;
        i += 1;
    }
    a
};

fn data(len: usize) -> Vec<u8> {
    POOL[..len].to_vec()
}

fn expected_owned_kind<R: Repr<'static>>(len: usize, heap: HeapKind) -> Kind {
    if len <= R::INLINE_CAPACITY {
        Kind::Inline
    } else {
        Kind::Heap(heap)
    }
}

/// The heap kind of a value made from a vector.
fn vec_kind<R: Repr<'static>>() -> HeapKind {
    if R::ADOPTS_VEC {
        HeapKind::Vec
    } else {
        HeapKind::Thin
    }
}

fn from_slice_and_vec<R: Repr<'static>>() {
    for len in lengths::<R>() {
        let d = data(len);
        let r = R::from_slice(&d);
        assert_eq!(r.as_slice(), d.as_slice());
        assert_eq!(r.len(), len);
        assert_eq!(r.kind(), expected_owned_kind::<R>(len, HeapKind::Thin));

        let r = R::from_vec(d.clone());
        assert_eq!(r.as_slice(), d.as_slice());
        assert_eq!(r.kind(), expected_owned_kind::<R>(len, vec_kind::<R>()));
    }
}

fn borrowed<R: Repr<'static>>() {
    for len in lengths::<R>() {
        let d = &POOL[..len];
        let r = R::from_borrowed(d);
        assert_eq!(r.as_slice(), d);
        let kind = r.kind();
        if len == 0 {
            // `Wide` keeps empty borrowed slices borrowed, the others inline them
            assert!(matches!(kind, Kind::Inline | Kind::Borrowed));
        } else if R::BORROWS {
            assert_eq!(kind, Kind::Borrowed);
            assert_eq!(r.as_slice().as_ptr(), d.as_ptr(), "must not copy");
            assert!(!r.is_unique());
        } else {
            assert_eq!(kind, expected_owned_kind::<R>(len, HeapKind::Thin));
        }
    }
}

fn vec_round_trip_is_zero_copy<R: Repr<'static>>() {
    let d = data(R::INLINE_CAPACITY + 100);
    let ptr = d.as_ptr();
    let r = R::from_vec(d);
    // adopted, or copied into a thin buffer
    assert_eq!(r.as_slice().as_ptr() == ptr, R::ADOPTS_VEC);
    let v = r.into_vec();
    // (a copy may land at the freed address: only checked when adopted)
    if R::ADOPTS_VEC {
        assert_eq!(v.as_ptr(), ptr);
    }
    assert_eq!(v, data(R::INLINE_CAPACITY + 100));
}

/// Writes into fresh unique values (Miri checks the pointers' provenance).
fn mutate_fresh_unique<R: Repr<'static>>() {
    let d = data(R::INLINE_CAPACITY + 10);
    for mut r in [R::from_slice(&d), R::from_vec(d.clone())] {
        r.to_mut_slice()[0] = 1;
        assert_eq!(r.as_slice()[0], 1);
    }
}

fn vec_with_spare_capacity<R: Repr<'static>>() {
    let mut v = Vec::with_capacity(R::INLINE_CAPACITY + 50);
    v.extend_from_slice(&data(R::INLINE_CAPACITY + 1));
    let (ptr, cap) = (v.as_ptr(), v.capacity());
    let mut r = R::from_vec(v);
    assert_eq!(r.len(), R::INLINE_CAPACITY + 1);
    if !R::ADOPTS_VEC {
        // copied: the spare capacity is not kept
        assert_eq!(r.as_slice(), data(R::INLINE_CAPACITY + 1));
        return;
    }
    assert_eq!(r.capacity(), cap);
    r.extend_from_slice(&[1; 20]);
    assert_eq!(
        r.as_slice().as_ptr(),
        ptr,
        "grows in place within the spare capacity"
    );
    let v = r.into_vec();
    assert_eq!(
        (v.as_ptr(), v.capacity(), v.len()),
        (ptr, cap, R::INLINE_CAPACITY + 21)
    );
}

fn clone_shares_or_copies<R: Repr<'static>>(shares: bool) {
    for (len, adopt) in [(R::INLINE_CAPACITY + 1, false), (500, true)] {
        let d = data(len);
        let a = if adopt {
            R::from_vec(d.clone())
        } else {
            R::from_slice(&d)
        };
        assert!(a.is_unique());
        let b = a.clone();
        assert_eq!(b.as_slice(), d.as_slice());
        let same = a.as_slice().as_ptr() == b.as_slice().as_ptr();
        assert_eq!(same, shares);
        assert_eq!(a.is_unique(), !shares);
        drop(b);
        assert!(a.is_unique());
    }
}

fn copy_on_write<R: Repr<'static>>() {
    for len in lengths::<R>() {
        let d = data(len);
        for source in 0..3 {
            let a = match source {
                0 => R::from_slice(&d),
                1 => R::from_vec(d.clone()),
                _ => R::from_borrowed(&POOL[..len]),
            };
            let mut b = a.clone();
            b.push(42);
            b.to_mut_slice()
                .iter_mut()
                .for_each(|x| *x = x.wrapping_add(1));
            assert!(b.is_unique());

            assert_eq!(a.as_slice(), d.as_slice(), "original untouched");
            let mut expected = d.clone();
            expected.push(42);
            expected.iter_mut().for_each(|x| *x = x.wrapping_add(1));
            assert_eq!(b.as_slice(), expected.as_slice());
        }
    }
}

fn growth_transitions<R: Repr<'static>>() {
    let mut r = R::new();
    let mut v = Vec::new();
    for i in 0..300u32 {
        r.push(i as u8);
        v.push(i as u8);
        assert_eq!(r.as_slice(), v.as_slice());
    }
    assert!(matches!(r.kind(), Kind::Heap(_)));

    // adopted vectors grow in place, keeping their buffer adopted
    let mut r = R::from_vec(data(R::INLINE_CAPACITY + 1));
    r.extend_from_slice(&data(1000));
    assert_eq!(r.kind(), Kind::Heap(vec_kind::<R>()));
    assert_eq!(r.len(), R::INLINE_CAPACITY + 1001);
}

fn truncate_and_pop<R: Repr<'static>>() {
    for len in lengths::<R>() {
        let d = data(len);
        let mut r = R::from_borrowed(&POOL[..len]);
        let mut v = d.clone();
        assert_eq!(r.pop(), v.pop());
        r.truncate(len / 2);
        v.truncate(len / 2);
        assert_eq!(r.as_slice(), v.as_slice());
        r.clear();
        assert!(r.is_empty());
        // clearing an empty borrowed `Wide` keeps it as is
        assert!(matches!(r.kind(), Kind::Inline | Kind::Borrowed));
    }
}

/// Differential test: random operations against `Vec<u8>`.
fn differential<R: Repr<'static>>(seed: u64) {
    let mut rng = fastrand::Rng::with_seed(seed);
    let pool = &POOL;
    let mut r = R::new();
    let mut v: Vec<u8> = Vec::new();
    let mut clones: Vec<(R, Vec<u8>)> = Vec::new();

    for _ in 0..400 {
        match rng.u8(0..9) {
            0 => {
                let x = rng.u8(..);
                r.push(x);
                v.push(x);
            }
            1 => {
                let n = rng.usize(0..60);
                let s = &pool[..n];
                r.extend_from_slice(s);
                v.extend_from_slice(s);
            }
            2 => assert_eq!(r.pop(), v.pop()),
            3 => {
                let n = rng.usize(0..=v.len());
                r.truncate(n);
                v.truncate(n);
            }
            4 => clones.push((r.clone(), v.clone())),
            5 => {
                let n = rng.usize(0..pool.len());
                r = R::from_borrowed(&pool[..n]);
                v = pool[..n].to_vec();
            }
            6 => {
                r = R::from_vec(v.clone());
            }
            7 => {
                if let Some(x) = r.to_mut_slice().first_mut() {
                    *x = x.wrapping_add(1);
                    v[0] = v[0].wrapping_add(1);
                }
            }
            _ => {
                if !clones.is_empty() {
                    let (c, cv) = clones.swap_remove(rng.usize(0..clones.len()));
                    assert_eq!(c.as_slice(), cv.as_slice());
                    if rng.bool() {
                        assert_eq!(c.into_vec(), cv);
                    }
                }
            }
        }
        assert_eq!(r.as_slice(), v.as_slice());
        assert_eq!(r.len(), v.len());
    }
    for (c, cv) in clones {
        assert_eq!(c.as_slice(), cv.as_slice());
    }
}

/// One value of each kind the representation supports, with its content.
fn kinds<R: Repr<'static>>() -> Vec<(R, &'static [u8])> {
    let c = R::INLINE_CAPACITY;
    let mut v = vec![
        (R::from_slice(&POOL[..c]), &POOL[..c]),
        (R::from_slice(&POOL[..c + 10]), &POOL[..c + 10]),
        (R::from_vec(data(c + 10)), &POOL[..c + 10]),
    ];
    if R::BORROWS {
        v.push((R::from_borrowed(&POOL[..c + 10]), &POOL[..c + 10]));
    }
    v
}

fn capacity_and_reserve<R: Repr<'static>>() {
    for (mut r, d) in kinds::<R>() {
        match r.kind() {
            Kind::Inline => assert_eq!(r.capacity(), R::INLINE_CAPACITY),
            Kind::Borrowed => assert_eq!(r.capacity(), 0),
            Kind::Heap(_) => assert!(r.capacity() >= r.len()),
        }
        assert!(r.try_reserve(usize::MAX).is_err(), "{:?}", r.kind());
        assert!(r.try_reserve(usize::MAX - r.len()).is_err());
        assert_eq!(r.as_slice(), d, "unchanged after a failed reserve");
        r.try_reserve(5).unwrap();
        assert!(r.is_unique() && r.capacity() >= d.len() + 5);
        assert_eq!(r.as_slice(), d);
    }
}

fn into_owned_keeps_content<R: Repr<'static>>() {
    for (r, d) in kinds::<R>() {
        let kind = r.kind();
        let ptr = r.as_slice().as_ptr();
        let o = r.into_owned();
        assert_eq!(o.as_slice(), d);
        if matches!(kind, Kind::Heap(_)) {
            assert_eq!(o.as_slice().as_ptr(), ptr, "heap values are not copied");
        }
        assert_ne!(o.kind(), Kind::Borrowed);
    }
}

macro_rules! suite {
    ($name:ident, $r:ty, shares = $shares:expr) => {
        mod $name {
            use super::*;

            #[test]
            fn from_slice_and_vec() {
                super::from_slice_and_vec::<$r>();
            }

            #[test]
            fn borrowed() {
                super::borrowed::<$r>();
            }

            #[test]
            fn vec_round_trip_is_zero_copy() {
                super::vec_round_trip_is_zero_copy::<$r>();
            }

            #[test]
            fn mutate_fresh_unique() {
                super::mutate_fresh_unique::<$r>();
            }

            #[test]
            fn vec_with_spare_capacity() {
                super::vec_with_spare_capacity::<$r>();
            }

            #[test]
            fn clone_shares_or_copies() {
                super::clone_shares_or_copies::<$r>($shares);
            }

            #[test]
            fn copy_on_write() {
                super::copy_on_write::<$r>();
            }

            #[test]
            fn growth_transitions() {
                super::growth_transitions::<$r>();
            }

            #[test]
            fn truncate_and_pop() {
                super::truncate_and_pop::<$r>();
            }

            #[test]
            fn capacity_and_reserve() {
                super::capacity_and_reserve::<$r>();
            }

            #[test]
            fn into_owned_keeps_content() {
                super::into_owned_keeps_content::<$r>();
            }

            #[test]
            fn differential() {
                let seeds = if cfg!(miri) { 2 } else { 64 };
                for seed in 0..seeds {
                    super::differential::<$r>(seed);
                }
            }
        }
    };
}

type WideRc<'a> = Wide<'a, Rc>;
type WideArc<'a> = Wide<'a, Arc>;
type WideUnique<'a> = Wide<'a, Unique>;
type SmallRc<'a> = Small<'a, Rc>;
type SmallArc<'a> = Small<'a, Arc>;
type SmallUnique<'a> = Small<'a, Unique>;

suite!(wide_rc, WideRc<'static>, shares = true);
suite!(wide_arc, WideArc<'static>, shares = true);
suite!(wide_unique, WideUnique<'static>, shares = false);
suite!(small_rc, SmallRc<'static>, shares = true);
suite!(small_arc, SmallArc<'static>, shares = true);
suite!(small_unique, SmallUnique<'static>, shares = false);
suite!(tiny_rc, Tiny<Rc>, shares = true);
suite!(tiny_arc, Tiny<Arc>, shares = true);
suite!(tiny_unique, Tiny<Unique>, shares = false);

#[test]
fn sizes() {
    let w = size_of::<usize>();
    assert_eq!(size_of::<WideRc<'static>>(), 3 * w);
    assert_eq!(size_of::<SmallRc<'static>>(), 2 * w);
    assert_eq!(size_of::<Tiny<Rc>>(), w);
    assert_eq!(size_of::<Option<WideRc<'static>>>(), 3 * w);
    assert_eq!(size_of::<Option<SmallRc<'static>>>(), 2 * w);
    assert_eq!(size_of::<Option<Tiny<Rc>>>(), w);
    assert_eq!(
        <WideRc<'static> as Repr<'static>>::INLINE_CAPACITY,
        3 * w - 1
    );
    assert_eq!(
        <SmallRc<'static> as Repr<'static>>::INLINE_CAPACITY,
        2 * w - 1
    );
    assert_eq!(<Tiny<Rc> as Repr<'static>>::INLINE_CAPACITY, w - 1);
}

#[test]
fn send_sync() {
    fn is_send_sync<X: Send + Sync>() {}
    is_send_sync::<WideArc<'static>>();
    is_send_sync::<SmallArc<'static>>();
    is_send_sync::<Tiny<Arc>>();
    is_send_sync::<WideUnique<'static>>();
    is_send_sync::<SmallUnique<'static>>();
}

#[test]
fn const_construction() {
    const F: WideRc<'static> = Wide::borrowed(b"hello world, this is longer than inline");
    const P: SmallRc<'static> = Small::borrowed(b"hello world, longer");
    const E: Tiny<Rc> = Tiny::new();
    assert_eq!(F.len(), 39);
    assert_eq!(P.as_slice(), b"hello world, longer");
    assert!(E.is_empty());
}

#[test]
fn wide_slicing() {
    let d = data(200);
    for source in 0..3 {
        let a: WideRc<'_> = match source {
            0 => Repr::from_slice(&d),
            1 => Repr::from_vec(d.clone()),
            _ => Wide::borrowed(&d),
        };
        let s = a.slice(50..150);
        assert_eq!(s.as_slice(), &d[50..150]);
        assert_eq!(s.as_slice().as_ptr(), a.as_slice()[50..].as_ptr(), "O(1)");
        let small = a.slice(10..12);
        // short slices of heap values move inline; borrowed ones stay borrowed
        let expected = if source == 2 {
            Kind::Borrowed
        } else {
            Kind::Inline
        };
        assert_eq!(small.kind(), expected);

        // mutating a slice of a unique owner reuses the buffer (normalized)
        drop(a);
        let mut s = s;
        s.push(1);
        let mut expected = d[50..150].to_vec();
        expected.push(1);
        assert_eq!(s.as_slice(), expected.as_slice());
    }

    // unique backend: slicing copies
    let a: WideUnique<'_> = Repr::from_slice(&d);
    let s = a.slice(50..150);
    assert_ne!(s.as_slice().as_ptr(), a.as_slice()[50..].as_ptr());
    assert_eq!(s.as_slice(), &d[50..150]);
}

#[test]
fn wide_unique_view_moves_to_the_front_on_growth() {
    // a unique view past the start of its buffer, without room to grow in place
    let d = data(200);
    let a: WideRc<'_> = Repr::from_slice(&d);
    let mut s = a.slice(50..200);
    drop(a);
    assert!(s.is_unique());
    let cap = s.capacity();
    s.try_reserve(cap + 1).unwrap();
    assert_eq!(s.as_slice(), &d[50..]);
    s.extend_from_slice(&d[..10]);
    assert_eq!(&s.as_slice()[150..], &d[..10]);
}
