use core::cell::Cell;

use super::*;
use crate::backend::Arc;

#[test]
fn from_array_small() {
    let v = HipVec::<u8, Arc>::from_array([1, 2, 3]);
    assert!(v.is_inline());
    assert_eq!(v.tag(), Tag::Inline);
    assert_eq!(v.len(), 3);
    assert_eq!(v.as_slice(), [1, 2, 3]);
}

#[test]
fn from_array_large() {
    let v = HipVec::<u8, Arc>::from_array([1; 40]);
    assert!(!v.is_inline());
    assert_eq!(v.tag(), Tag::Thin);
    assert_eq!(v.len(), 40);
    assert_eq!(v.as_slice(), [1; 40]);
}

#[test]
fn drop_count() {
    let counts = CloneAndDropCounts::new();

    let v = HipVec::<_, Arc>::from_array([0; 50].map(|_| counts.witness()));
    assert_eq!(v.tag(), Tag::Thin);

    let v2 = v.clone();
    drop(v);
    assert_eq!(counts.clones(), 0);
    assert_eq!(counts.drops(), 0);

    drop(v2);
    assert_eq!(counts.clones(), 0);
    assert_eq!(counts.drops(), 50);
}

#[test]
fn drop_count_inline() {
    let counts = CloneAndDropCounts::new();

    {
        let v = HipVec::<_, Arc>::from_array([0; 2].map(|_| counts.witness()));
        assert_eq!(v.tag(), Tag::Inline);
    }
    assert_eq!(counts.clones(), 0);
    assert_eq!(counts.drops(), 2);
}

struct CloneAndDropCounts {
    clones: Cell<u16>,
    drops: Cell<u16>,
}

impl CloneAndDropCounts {
    fn new() -> Self {
        Self {
            clones: Cell::new(0),
            drops: Cell::new(0),
        }
    }

    fn clones(&self) -> usize {
        self.clones.get().into()
    }

    fn drops(&self) -> usize {
        self.drops.get().into()
    }

    fn witness(&self) -> CloneAndDropWitness {
        CloneAndDropWitness { witness: self }
    }
}

struct CloneAndDropWitness<'a> {
    witness: &'a CloneAndDropCounts,
}

impl Clone for CloneAndDropWitness<'_> {
    fn clone(&self) -> Self {
        self.witness.clones.set(self.witness.clones.get() + 1);
        CloneAndDropWitness {
            witness: self.witness,
        }
    }
}

impl Drop for CloneAndDropWitness<'_> {
    fn drop(&mut self) {
        self.witness.drops.set(self.witness.drops.get() + 1);
    }
}
