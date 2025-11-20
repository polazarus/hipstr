use alloc::boxed::Box;
use alloc::vec;

use super::*;
use crate::Arc;

#[test]
fn is_empty() {
    let mut h = HipVec::<i32, Arc>::new();
    assert!(h.mutate().is_empty());

    let mut h = HipVec::<i32, Arc>::with_capacity(1);
    assert!(h.mutate().is_empty());

    let mut h = HipVec::<i32, Arc>::with_capacity(42);
    assert!(h.mutate().is_empty());
}

#[test]
fn as_ptr() {
    let mut h = HipVec::<i32, Arc>::new();
    assert_eq!(h.mutate().as_ptr(), ptr::dangling());

    let mut h = HipVec::<i32, Arc>::with_capacity(1);
    let p = h.as_ptr();
    assert_eq!(h.mutate().as_ptr(), p);

    let mut h = HipVec::<i32, Arc>::with_capacity(42);
    let p = h.as_ptr();
    assert_eq!(h.mutate().as_ptr(), p);
}

#[test]
fn as_mut_ptr() {
    let mut h = HipVec::<i32, Arc>::new();
    assert_eq!(h.mutate().as_mut_ptr(), ptr::dangling_mut());

    let mut h = HipVec::<i32, Arc>::with_capacity(1);
    let p = h.as_ptr();
    assert_eq!(h.mutate().as_mut_ptr().cast_const(), p);

    let mut h = HipVec::<i32, Arc>::with_capacity(42);
    let p = h.as_ptr();
    assert_eq!(h.mutate().as_mut_ptr().cast_const(), p);
}

#[test]
fn as_non_null() {
    let mut h = HipVec::<i32, Arc>::new();
    assert_eq!(h.mutate().as_non_null(), NonNull::dangling());

    let mut h = HipVec::<i32, Arc>::with_capacity(1);
    let p = h.as_ptr();
    assert_eq!(h.mutate().as_non_null().as_ptr().cast_const(), p);

    let mut h = HipVec::<i32, Arc>::with_capacity(42);
    let p = h.as_ptr();
    assert_eq!(h.mutate().as_non_null().as_ptr().cast_const(), p);
}

#[test]
fn as_slice() {
    let mut h = HipVec::<i32, Arc>::new();
    assert!(h.mutate().as_slice().is_empty());

    let mut h = HipVec::<i32, Arc>::from([1]);
    let p = h.as_ptr();
    let l = h.len();
    assert_eq!(h.mutate().as_slice().as_ptr(), p);
    assert_eq!(h.mutate().as_slice().len(), l);

    let mut h = HipVec::<i32, Arc>::from([42; 42]);
    let p = h.as_ptr();
    let l = h.len();
    assert_eq!(h.mutate().as_slice().as_ptr(), p);
    assert_eq!(h.mutate().as_slice().len(), l);
}

#[test]
fn as_mut_slice() {
    let mut h = HipVec::<i32, Arc>::new();
    assert!(h.mutate().as_mut_slice().is_empty());

    let mut h = HipVec::<i32, Arc>::from([1]);
    let p = h.as_ptr();
    let l = h.len();
    {
        let mut m = h.mutate();
        assert_eq!(m.as_mut_slice().as_ptr(), p);
        assert_eq!(m.as_mut_slice().len(), l);
        m.as_mut_slice()[0] = 2;
    }
    assert_eq!(h.as_slice(), &[2]);

    let mut h = HipVec::<i32, Arc>::from([42; 42]);
    let p = h.as_ptr();
    let l = h.len();
    {
        let mut m = h.mutate();
        assert_eq!(m.as_mut_slice().as_ptr(), p);
        assert_eq!(m.as_mut_slice().len(), l);
        m.as_mut_slice().fill(0);
    }
    assert_eq!(h.as_slice(), &[0; 42]);
}

#[test]
fn reserve() {
    let mut h = HipVec::<u8, Arc>::from([1, 2, 3, 4, 5]);
    {
        let mut h_mut = h.mutate();
        assert!(h_mut.0.is_inline());
        h_mut.reserve(100);
        assert!(h_mut.0.is_thin());
    }
    assert!(h.is_thin());

    let mut h = HipVec::<u8, Arc>::from(vec![42; 42]);
    {
        let mut h_mut = h.mutate();
        assert!(h_mut.0.is_wide());
        h_mut.reserve(100);
        assert!(h_mut.0.is_thin());
    }
    assert!(h.is_thin());

    let mut h = HipVec::<u8, Arc>::new();
    assert!(h.is_borrowed());
    {
        let mut h_mut = h.mutate();
        assert!(h_mut.0.is_borrowed());
        h_mut.reserve(10);
        assert!(h_mut.0.is_inline());
    }

    let mut h = HipVec::<u8, Arc>::new();
    assert!(h.is_borrowed());
    {
        let mut h_mut = h.mutate();
        assert!(h_mut.0.is_borrowed());
        h_mut.reserve(100);
        assert!(h_mut.0.is_thin());
    }
}

#[test]
fn reserve_exact() {
    let mut h = HipVec::<u8, Arc>::from([1, 2, 3, 4, 5]);
    {
        let mut h_mut = h.mutate();
        assert!(h_mut.0.is_inline());
        h_mut.reserve_exact(100);
        assert!(h_mut.0.is_thin());
    }
    assert!(h.is_thin());

    let mut h = HipVec::<u8, Arc>::from(vec![42; 42]);
    {
        let mut h_mut = h.mutate();
        assert!(h_mut.0.is_wide());
        h_mut.reserve_exact(100);
        assert!(h_mut.0.is_thin());
    }
    assert!(h.is_thin());

    let mut h = HipVec::<u8, Arc>::new();
    assert!(h.is_borrowed());
    {
        let mut h_mut = h.mutate();
        assert!(h_mut.0.is_borrowed());
        h_mut.reserve_exact(10);
        assert!(h_mut.0.is_inline());
    }

    let mut h = HipVec::<u8, Arc>::new();
    assert!(h.is_borrowed());
    {
        let mut h_mut = h.mutate();
        assert!(h_mut.0.is_borrowed());
        h_mut.reserve_exact(100);
        assert!(h_mut.0.is_thin());
    }
}

#[test]
fn pop() {
    let mut h = HipVec::<u8, Arc>::new();
    assert!(h.mutate_copy().pop().is_none());

    let mut h = HipVec::<u8, Arc>::from([1, 2, 3]);
    assert_eq!(h.mutate_copy().pop(), Some(3));
    assert_eq!(h.len(), 2);

    let mut h = HipVec::<u8, Arc>::from([42; 42]);
    assert_eq!(h.mutate_copy().pop(), Some(42));
    assert_eq!(h.len(), 41);
}

#[test]
fn truncate() {
    let mut h = HipVec::<u8, Arc>::new();
    h.mutate_copy().truncate(20); // do nothing
    assert!(h.is_empty());
    assert_eq!(h.capacity(), 0);

    let mut h = HipVec::<Box<u8>, Arc>::from([1].map(Box::new));
    h.mutate().clear();
    assert_eq!(h.len(), 0);
    assert!(h.capacity() >= 1);

    let mut h = HipVec::<Box<u8>, Arc>::from([42; 42].map(Box::new));
    h.mutate().truncate(3);
    assert_eq!(h.len(), 3);
    assert!(h.capacity() >= 42);
}

#[test]
fn extend_from_slice() {
    let mut h = HipVec::<Box<u8>, Arc>::new();
    {
        let mut m = h.mutate();

        m.extend_from_slice(&[1].map(Box::new));
        assert_eq!(m.as_slice(), &[1].map(Box::new));

        m.extend_from_slice(&[2, 3, 4, 5].map(Box::new));
        assert_eq!(m.as_slice(), &[1, 2, 3, 4, 5].map(Box::new));
    }
    assert_eq!(h.as_slice(), &[1, 2, 3, 4, 5].map(Box::new));
}

#[test]
fn set_len() {
    let mut h = HipVec::<i32, Arc>::new();
    unsafe {
        h.mutate().set_len(0);
    }
    assert!(h.is_empty());

    let mut h = HipVec::<_, Arc>::from([1, 2, 3]);
    unsafe {
        h.mutate().set_len(0);
    }
    assert!(h.is_empty());

    let mut h = HipVec::<_, Arc>::from([42; 42]);
    unsafe {
        h.mutate().set_len(0);
    }
    assert!(h.is_empty());
}

#[test]
fn set_capacity() {
    let l = HipVec::<i32, Arc>::INLINE_CAP;

    let mut h = HipVec::<i32, Arc>::new();
    unsafe {
        h.mutate().set_capacity(5);
    }
    assert!(h.capacity() >= 5);

    let mut h = HipVec::<i32, Arc>::with_capacity(5);
    unsafe {
        h.mutate().set_capacity(0);
    }
    assert_eq!(h.capacity(), 0);

    let mut h = HipVec::<i32, Arc>::with_capacity(l);
    unsafe {
        h.mutate().set_capacity(l);
    }
    assert_eq!(h.capacity(), l);
}

#[test]
fn swap_remove() {
    let mut h = HipVec::<u8, Arc>::from(b"abc");
    h.mutate().swap_remove(0);
    assert_eq!(h.as_slice(), b"cb");
}

#[test]
fn swap_remove_boxed() {
    let mut h = HipVec::<_, Arc>::from(b"abc".map(Box::new));
    h.mutate().swap_remove(0);
    assert_eq!(h.as_slice(), b"cb".map(Box::new));
}

#[test]
#[should_panic(expected = "index out of bounds")]
fn swap_remove_panic() {
    let mut h = HipVec::<u8, Arc>::from(b"abc");
    h.mutate().swap_remove(5);
}

#[test]
fn remove() {
    let mut h = HipVec::<u8, Arc>::from(b"abc");
    h.mutate().remove(0);
    assert_eq!(h.as_slice(), b"bc");
}

#[test]
fn remove_boxed() {
    let mut h = HipVec::<_, Arc>::from(b"abc".map(Box::new));
    h.mutate().remove(0);
    assert_eq!(h.as_slice(), b"bc".map(Box::new));
}

#[test]
#[should_panic(expected = "index out of bounds")]
fn remove_panic() {
    let mut h = HipVec::<u8, Arc>::from(b"abc");
    h.mutate().remove(5);
}

#[test]
fn insert() {
    let mut h = HipVec::<_, Arc>::new();
    h.mutate().insert(0, Box::new(1));
    assert_eq!(h.as_slice(), [1].map(Box::new));

    let mut h = HipVec::<_, Arc>::from([1].map(Box::new));
    h.mutate().insert(1, Box::new(2));
    assert_eq!(h.as_slice(), [1, 2].map(Box::new));

    let mut h = HipVec::<_, Arc>::from([1].map(Box::new));
    h.mutate().insert(0, Box::new(2));
    assert_eq!(h.as_slice(), [2, 1].map(Box::new));

    let mut h = HipVec::<_, Arc>::from([42; 42].map(Box::new));
    h.mutate().insert(10, Box::new(42));
    assert_eq!(h.as_slice(), [42; 43].map(Box::new));
}

#[test]
fn append() {
    let mut h = HipVec::<_, Arc>::new();
    let mut v = vec![1, 2, 3];
    h.mutate().append(&mut v);
    assert!(v.is_empty());
    assert_eq!(h.as_slice(), [1, 2, 3]);

    let mut h = HipVec::<_, Arc>::from([1, 2, 3]);
    let mut v = vec![1, 2, 3];
    h.mutate().append(&mut v);
    assert!(v.is_empty());
    assert_eq!(h.as_slice(), [1, 2, 3, 1, 2, 3]);

    let mut h = HipVec::<_, Arc>::from([42; 21]);
    let mut v = vec![42; 21];
    h.mutate().append(&mut v);
    assert!(v.is_empty());
    assert_eq!(h.as_slice(), [42; 42]);
}

#[test]
fn drain() {
    let mut h = HipVec::<_, Arc>::from([1, 2, 3, 4, 5]);
    {
        let mut m = h.mutate();
        let mut drain = m.drain(1..3);
        assert_eq!(drain.next(), Some(2));
        let _ = drain;
    }
    assert_eq!(h.as_slice(), [1, 4, 5]);
}

#[test]
fn spare_capacity_mut() {
    let mut h = HipVec::<u8, Arc>::new();
    {
        let mut m = h.mutate();
        assert!(m.spare_capacity_mut().is_empty())
    }

    let mut h = HipVec::<u8, Arc>::with_capacity(5);
    {
        let mut m = h.mutate();
        assert!(m.spare_capacity_mut().len() >= 5);
        m.spare_capacity_mut()[0].write(1);
        unsafe {
            m.set_len(1);
        }
    }
    assert_eq!(h.as_slice(), [1]);

    let mut h = HipVec::<u8, Arc>::with_capacity(100);
    {
        let mut m = h.mutate();
        assert!(m.spare_capacity_mut().len() >= 100);
        m.spare_capacity_mut()[0].write(1);
        unsafe {
            m.set_len(1);
        }
    }
    assert_eq!(h.as_slice(), [1]);
}

#[test]
fn resize() {
    let mut h = HipVec::<u8, Arc>::new();
    h.mutate().resize(10, 0);
    assert_eq!(h.as_slice(), [0; 10]);

    let mut h = HipVec::<Box<i32>, Arc>::new();
    h.mutate().resize(100, Box::new(0));
    assert_eq!(h.as_slice(), [0; 100].map(Box::new));
}

#[test]
fn resize_with() {
    let mut h = HipVec::<u8, Arc>::new();
    h.mutate().resize_with(10, || 0);
    assert_eq!(h.as_slice(), [0; 10]);

    let mut h = HipVec::<Box<i32>, Arc>::new();
    h.mutate().resize_with(100, || Box::new(0));
    assert_eq!(h.as_slice(), [0; 100].map(Box::new));
}
