//! Allocated representation.

use alloc::vec::Vec;
use core::marker::PhantomData;
use core::mem::{offset_of, transmute, ManuallyDrop, MaybeUninit};
use core::ops::Range;
use core::panic::{RefUnwindSafe, UnwindSafe};
use core::ptr::{self, NonNull};

use super::TAG_OWNED;
use crate::backend::{Backend, UpdateResult};
use crate::smart::{Inner, Smart};
use crate::vecs::thin::{Header, ThinVec};
use crate::vecs::SmartThinVec;

const TAG_MASK: usize = super::MASK as usize;
const TAG: usize = super::TAG_OWNED as usize;
const THIN_BIT: usize = 0b1;
const TAG_THIN: usize = super::TAG_OWNED as usize | THIN_BIT;
const TAG_FAT: usize = super::TAG_OWNED as usize;

enum Variant<F, T> {
    Fat(F),
    Thin(T),
}

/// Tagged smart pointer (with forced exposed provenance).
///
/// The exposed provenance is required to cast [`Allocated`] from and to the
/// [`Pivot`](super::Pivot) representation.
struct TaggedSmart<B: Backend>(usize, PhantomData<Smart<Vec<u8>, B>>);

// Manual implementation of Clone and Copy traits to avoid requiring additional
// trait bounds on the generic parameter B

impl<B: Backend> Clone for TaggedSmart<B> {
    #[cfg_attr(coverage_nightly, coverage(off))]
    fn clone(&self) -> Self {
        *self
    }
}

impl<B: Backend> Copy for TaggedSmart<B> {}

impl<B: Backend> TaggedSmart<B> {
    /// Gets the owner.
    fn get(&self) -> Variant<Smart<Vec<u8>, B>, SmartThinVec<u8, B>> {
        let ptr = self.ptr();

        if self.is_fat() {
            Variant::Fat(unsafe { Smart::from_raw(ptr.cast()) })
        } else {
            Variant::Thin(unsafe { SmartThinVec::from_raw(ptr.cast()) })
        }
    }

    const fn is_fat(&self) -> bool {
        self.0 & THIN_BIT == 0
    }

    const fn ptr(&self) -> NonNull<()> {
        // expose provenance semantics
        let ptr = (self.0 & !TAG_MASK) as *mut ();
        debug_assert!(!ptr.is_null());
        // debug only

        // SAFETY: type invariant
        let ptr: NonNull<()> = unsafe { NonNull::new_unchecked(ptr) };

        #[cfg(miri)]
        let _ = &*ptr; // check provenance early
        ptr
    }

    /// Constructed a tagged smart pointer from a [`Smart`].
    #[inline]
    fn from_smart_vec(raw: Smart<Vec<u8>, B>) -> Self {
        let ptr = Smart::into_raw(raw).as_ptr();
        debug_assert!(ptr.is_aligned());
        debug_assert!((ptr as usize) & TAG_MASK == 0);

        // SAFETY: add a 2-bit tag to a non-null pointer with the same alignment
        // requirement as usize (typically 4 bytes on 32-bit architectures, and
        // more on 64-bit architectures)
        let addr = ptr.map_addr(|addr| addr | TAG_FAT).expose_provenance();

        Self(addr, PhantomData)
    }

    #[inline]
    fn from_smart_thin_vec(raw: SmartThinVec<u8, B>) -> Self {
        let ptr = SmartThinVec::into_raw(raw).as_ptr();
        debug_assert!(ptr.is_aligned());
        debug_assert!((ptr as usize) & TAG_MASK == 0);

        // SAFETY: add a 2-bit tag to a non-null pointer with the same alignment
        // requirement as usize (typically 4 bytes on 32-bit architectures, and
        // more on 64-bit architectures)
        let addr = ptr.map_addr(|addr| addr | TAG_THIN).expose_provenance();

        Self(addr, PhantomData)
    }

    #[inline]
    fn is_unique(self) -> bool {
        const {
            assert!(offset_of!(Inner<u8, B>, count) == 0);
            assert!(offset_of!(Header<u8, B>, prefix) == 0);
        }
        self.count().is_unique()
    }

    #[inline]
    fn count(&self) -> &B {
        let counter = unsafe { self.ptr().cast().as_ref() };

        #[cfg(debug_assertions)]
        {
            let m = ManuallyDrop::new(self.get());
            unsafe {
                match &*m {
                    Variant::Fat(fat) => {
                        debug_assert_eq!(&raw const fat.0.as_ref().count, counter as *const _);
                    }
                    Variant::Thin(thin) => {
                        debug_assert_eq!(&raw const thin.0.as_ref().prefix, counter as *const _);
                    }
                }
            }
        }

        counter
    }

    #[inline]
    fn as_slice(&self) -> &[u8] {
        let v = ManuallyDrop::new(self.get());
        let short_lived = match &*v {
            Variant::Fat(fat) => fat.as_slice(),
            Variant::Thin(thin) => thin.as_slice(),
        };
        // SAFETY: the owner is valid.
        unsafe { transmute(short_lived) }
    }

    /// Checks if the tag is valid.
    #[inline]
    const fn check_tag(self) -> bool {
        (self.0 & !TAG_MASK) != 0 && (self.0 & TAG_OWNED as usize) != 0
    }

    /// Explicitly clones this tagged smart pointer.
    fn try_clone(self) -> Option<Self> {
        let variant = ManuallyDrop::new(self.get());
        match &*variant {
            Variant::Fat(fat) => fat.try_clone().map(Self::from_smart_vec),
            Variant::Thin(thin) => thin.try_clone().map(Self::from_smart_thin_vec),
        }
    }

    unsafe fn as_fat_unchecked(&self) -> Smart<Vec<u8>, B> {
        debug_assert!(self.is_fat());
        debug_assert!(self.check_tag());

        // SAFETY: type invariant
        unsafe { Smart::from_raw(self.ptr().cast()) }
    }
}

/// Allocated representation.
///
/// # Warning!
///
/// For big-endian platform, the owner pointer is **after** the slice.
/// For little-endian platform, the owner pointer is **before** the slice.
#[repr(C)]
pub struct Allocated<B: Backend> {
    #[cfg(target_endian = "little")]
    /// Tagged smart pointer of the owning vector
    owner: TaggedSmart<B>,

    /// Pointer to the slice's start
    ptr: *const u8,

    /// Length of the slice
    len: usize,

    #[cfg(target_endian = "big")]
    /// Tagged smart pointer of the owning vector
    owner: TaggedSmart<B>,
}

impl<B: Backend> Copy for Allocated<B> {}

impl<B: Backend> Clone for Allocated<B> {
    #[cfg_attr(coverage_nightly, coverage(off))]
    fn clone(&self) -> Self {
        *self
    }
}

unsafe impl<B: Backend + Sync> Sync for Allocated<B> {}

unsafe impl<B: Backend + Send> Send for Allocated<B> {}

impl<B: Backend + Unpin> Unpin for Allocated<B> {}

impl<B: Backend + UnwindSafe> UnwindSafe for Allocated<B> {}

impl<B: Backend + RefUnwindSafe> RefUnwindSafe for Allocated<B> {}

impl<B: Backend> Allocated<B> {
    /// Converts the allocated representation into its owner.
    fn into_owner(self) -> Variant<Smart<Vec<u8>, B>, SmartThinVec<u8, B>> {
        self.owner.get()
    }

    /// Creates an allocated from a vector.
    ///
    /// Takes ownership of the vector without copying the data.
    #[inline]
    pub fn from_vec(v: Vec<u8>) -> Self {
        let ptr = v.as_ptr();
        let len = v.len();
        let owner = Smart::new(v);
        assert!(owner.is_unique());

        let this = Self {
            ptr,
            len,
            owner: TaggedSmart::from_smart_vec(owner),
        };

        debug_assert!(this.is_unique());

        this
    }

    #[inline]
    pub fn from_thin_vec<P>(v: ThinVec<u8, P>) -> Self {
        let ptr = v.as_ptr();
        let len = v.len();
        let stv = SmartThinVec::from(v);

        let this = Self {
            ptr,
            len,
            owner: TaggedSmart::from_smart_thin_vec(stv),
        };

        debug_assert!(this.is_unique());
        debug_assert!(this.is_valid());

        this
    }

    /// Creates an allocated vector from a slice.
    pub fn from_slice(slice: &[u8]) -> Self {
        Self::from_vec(slice.to_vec())
    }

    /// Returns the length of this allocated string.
    #[inline]
    pub const fn len(&self) -> usize {
        // NOTE: must be const to be used in `HipByt::len` even if there is no
        // way the allocated representation will be used in the const case

        // debug_assert!(self.is_valid()); // not const

        self.len
    }

    /// Returns as a byte slice.
    #[inline]
    pub const fn as_slice(&self) -> &[u8] {
        // NOTE: must be const to be used in `HipByt::as_slice` even if there is no
        // way the allocated representation will be used in the const case

        // debug_assert!(self.is_valid()); // not const

        // SAFETY: Type invariant
        unsafe { core::slice::from_raw_parts(self.ptr, self.len) }
    }

    /// Returns a raw pointer to the first element.
    #[inline]
    pub const fn as_ptr(&self) -> *const u8 {
        // NOTE: must be const to be used in `HipByt::as_ptr` even if there is no way
        // the allocated representation will be used in the const case

        // debug_assert!(self.is_valid()); // is_valid is not const!
        self.ptr
    }

    /// Returns a mutable raw pointer to the first element if this sequence is
    /// not shared, `None` otherwise.
    #[inline]
    #[allow(clippy::needless_pass_by_ref_mut)]
    pub fn as_mut_ptr(&mut self) -> Option<*mut u8> {
        if self.is_unique() {
            Some(self.ptr.cast_mut())
        } else {
            None
        }
    }

    /// Returns a mutable raw pointer to the first element.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the `Allocated` is actually uniquely shared.
    #[inline]
    #[allow(clippy::needless_pass_by_ref_mut)]
    pub unsafe fn as_mut_ptr_unchecked(&mut self) -> *mut u8 {
        debug_assert!(self.is_unique());
        self.ptr.cast_mut()
    }

    /// Returns a mutable slice if possible (unique owned reference).
    #[inline]
    pub fn as_mut_slice(&mut self) -> Option<&mut [u8]> {
        if self.is_unique() {
            // SAFETY:
            // * unique -> no one else can "see" the string
            // * type invariant -> valid slice
            Some(unsafe { self.as_mut_slice_unchecked() })
        } else {
            None
        }
    }

    /// Returns a mutable slice.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the `Allocated` is actually uniquely shared.
    #[inline]
    pub unsafe fn as_mut_slice_unchecked(&mut self) -> &mut [u8] {
        debug_assert!(self.is_valid());
        debug_assert!(self.is_unique());

        unsafe { core::slice::from_raw_parts_mut(self.ptr.cast_mut(), self.len) }
    }

    /// Creates a new `Allocated` for some range with the same owner.
    ///
    /// # Safety
    ///
    /// Range must be a range `a..b` such that `a <= b <= len`.
    #[inline]
    pub unsafe fn slice_unchecked(&self, range: Range<usize>) -> Option<Self> {
        debug_assert!(self.is_valid());
        debug_assert!(range.start <= range.end);
        debug_assert!(range.start <= self.len);
        debug_assert!(range.end <= self.len);

        let owner = self.owner;
        if owner.count().incr() == UpdateResult::Overflow {
            return None;
        }

        // SAFETY: type invariant -> self.ptr..self.ptr+self.len is valid
        // also Rust like C specify you can move to the last + 1
        let ptr = unsafe { self.ptr.add(range.start) };

        Some(Self {
            ptr,
            len: range.len(),
            owner,
        })
    }

    /// Clones this vector.
    #[inline]
    pub fn try_clone(&self) -> Option<Self> {
        debug_assert!(self.is_valid());

        if self.owner.count().incr() == UpdateResult::Done {
            Some(*self)
        } else {
            None
        }
    }

    /// Drops this vector explicitly.
    #[inline]
    pub fn explicit_drop(self) {
        debug_assert!(self.is_valid());
        let _ = self.into_owner();
    }

    /// Return `true` iff this representation is valid.
    #[inline]
    #[cfg_attr(coverage_nightly, coverage(off))]
    pub fn is_valid(&self) -> bool {
        if !self.owner.check_tag() {
            return false;
        }

        let owner_slice: &[u8] = self.owner.as_slice();
        let owner_ptr = owner_slice.as_ptr();
        let owner_len = owner_slice.len();
        let shift = unsafe { self.ptr.offset_from(owner_ptr) };
        shift >= 0 && {
            #[allow(clippy::cast_sign_loss)]
            let shift = shift as usize;
            shift <= owner_len && shift + self.len <= owner_len
        }
    }

    /// Returns the backend capacity.
    #[inline]
    pub fn capacity(&self) -> usize {
        debug_assert!(self.is_valid());

        let owner = ManuallyDrop::new(self.owner.get());
        match &*owner {
            Variant::Fat(fat) => fat.capacity(),
            Variant::Thin(thin) => thin.capacity(),
        }
    }

    /// Unwraps the inner vector if it makes any sense.
    #[inline]
    pub fn try_into_vec(self) -> Result<Vec<u8>, Self> {
        debug_assert!(self.is_valid());

        if !self.owner.is_fat() {
            return Err(self);
        }
        let owner = ManuallyDrop::new(unsafe { self.owner.as_fat_unchecked() });

        if !owner.is_unique() || self.ptr != owner.as_ptr() {
            // the owner is shared or the slice is not at the start of the vector
            return Err(self);
        }

        let owner = ManuallyDrop::into_inner(owner);
        let mut vec = unsafe { Smart::into_inner_unchecked(owner) };
        vec.truncate(self.len);

        // forget(self);

        Ok(vec)
    }

    /// Returns `true` if there is only one reference to the underlying vector.
    pub fn is_unique(&self) -> bool {
        debug_assert!(self.is_valid());
        self.owner.is_unique()
    }

    /// Pushes a slice at the end of the underlying vector.
    ///
    /// # Safety
    ///
    /// The reference must be unique, cf. [`Self::is_unique`].
    pub unsafe fn push_slice_unchecked(&mut self, addition: &[u8]) {
        debug_assert!(self.is_valid());
        debug_assert!(self.is_unique());

        // SAFETY: uniqueness is a precondition, owner can be mutable
        let mut owner = ManuallyDrop::new(self.owner.get());

        let shift; // start of the slice in the vector
        let ptr; // pointer to the start of the vector, may change when growing

        #[allow(clippy::cast_sign_loss)]
        match &mut *owner {
            Variant::Fat(fat) => {
                let fat = unsafe { fat.as_mut_unchecked() };

                // SAFETY: compute the shift from within the vector range (type invariant)
                shift = unsafe { self.ptr.offset_from(fat.as_ptr()) as usize };
                fat.truncate(self.len);
                fat.extend_from_slice(addition);
                ptr = fat.as_ptr();
            }
            Variant::Thin(thin) => {
                let thin = unsafe { thin.as_mut_unchecked() };

                // SAFETY: compute the shift from within the vector range (type invariant)
                shift = unsafe { self.ptr.offset_from(thin.as_ptr()) as usize };
                thin.truncate(self.len);
                thin.extend_from_slice_copy(addition);
                ptr = thin.as_ptr();
            }
        }

        self.len += addition.len();

        // SAFETY: shift to within the vector range (the shift was already
        // in the old range).
        self.ptr = unsafe { ptr.add(shift) };
    }

    /// Returns the remaining spare capacity of the unique vector as a slice of
    /// `MaybeUnit<u8>`. If the vector is actually shared, returns an empty
    /// slice.
    ///
    /// The returned slice can be used to fill the vector with data (e.g. by
    /// reading from a file) before marking the data as initialized using the
    /// `set_len` method.
    pub fn spare_capacity_mut(&mut self) -> &mut [MaybeUninit<u8>] {
        debug_assert!(self.is_valid());

        if !self.is_unique() {
            return &mut [];
        }

        let mut owner = ManuallyDrop::new(self.owner.get());

        match &mut *owner {
            Variant::Fat(fat) => {
                let vec = unsafe { fat.as_mut_unchecked_extended() };
                let start = unsafe { self.ptr.offset_from(vec.as_ptr()) as usize };
                let end = start + self.len;
                vec.truncate(end);
                vec.spare_capacity_mut()
            }
            Variant::Thin(thin) => {
                let vec = unsafe { thin.as_mut_unchecked() };
                let start = unsafe { self.ptr.offset_from(vec.as_ptr()) as usize };
                let end = start + self.len;
                vec.truncate(end);
                let spare = vec.spare_capacity_mut();

                // extend lifetime of the slicce
                // SAFETY: the slice is valid while self is owned
                unsafe { transmute(spare) }
            }
        }
    }

    /// Forces the length of the vector to `new_len`.
    ///
    /// # Safety
    ///
    /// Either:
    /// 1. `new_len` is less than or equal to the current length, in which case
    ///    this truncates the vector, or
    /// 2. All of these conditions must be met:
    ///    - `new_len` is greater than `capacity()`
    ///    - The elements at `old_len..new_len` must be properly initialized
    ///    - The vector must be uniquely owned (not shared)
    ///
    /// Failing to meet these safety requirements can lead to undefined
    /// behavior.
    pub unsafe fn set_len(&mut self, new_len: usize) {
        if new_len <= self.len {
            self.len = new_len;
            return;
        }

        debug_assert!(self.is_unique());
        debug_assert!(new_len <= self.capacity());

        let mut owner = ManuallyDrop::new(self.owner.get());
        match &mut *owner {
            Variant::Fat(fat) => {
                // SAFETY: uniqueness is a precondition
                let vec = unsafe { fat.as_mut_unchecked() };

                // SAFETY: compute the shift from within the vector range (type invariant)
                #[allow(clippy::cast_sign_loss)]
                let start = unsafe { self.ptr.offset_from(vec.as_ptr()).abs_diff(0) };

                unsafe {
                    vec.set_len(start + new_len);
                }
            }

            Variant::Thin(thin) => {
                // SAFETY: uniqueness is a precondition
                let vec = unsafe { thin.as_mut_unchecked() };
                // SAFETY: compute the shift from within the vector range (type invariant)
                #[allow(clippy::cast_sign_loss)]
                let start = unsafe { self.ptr.offset_from(vec.as_ptr()).abs_diff(0) };
                unsafe {
                    vec.set_len(start + new_len);
                }
            }
        }

        self.len = new_len;
    }

    /// Shrinks the capacity of the underlying vector as close as possible to
    /// `min_capacity`.
    ///
    /// The capacity will not shrink below the length of the vector or the
    /// supplied minimum capacity. That is, if the current capacity is less than
    /// or equal to the minimum capacity, no shrinking is done.
    pub fn shrink_to(&mut self, min_capacity: usize) {
        let min_capacity = min_capacity.max(self.len);

        if self.capacity() <= min_capacity {
            return;
        }

        let mut new_vec: ThinVec<u8, B> = ThinVec::with_capacity(min_capacity);
        new_vec.extend_from_slice_copy(self.as_slice());
        let old = core::mem::replace(self, Self::from_thin_vec(new_vec));
        old.explicit_drop();
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec;

    use super::Allocated;
    use crate::backend::Counter;
    use crate::{thin_vec, Rc};

    #[test]
    fn test_alloc() {
        let allocated = Allocated::<Rc>::from_vec(vec![]);
        let _ = allocated.explicit_drop();

        let allocated = Allocated::<Rc>::from_thin_vec(thin_vec![0_u8]);
        let allocated2 = allocated.try_clone().unwrap();
        let _ = allocated.explicit_drop();
        let _ = allocated2.explicit_drop();
    }

    #[test]
    #[cfg_attr(coverage_nightly, coverage(off))]
    fn test_try_into_vec() {
        let allocated = Allocated::<Rc>::from_vec(vec![0, 1, 2]);
        assert_eq!(allocated.owner.count().get(), 1);

        {
            let slice = unsafe { allocated.slice_unchecked(1..2) }.unwrap();

            assert_eq!(allocated.owner.count().get(), 2);
            let Err(allocated) = slice.try_into_vec() else {
                panic!("shared reference cannot be converted to vec")
            };
            allocated.explicit_drop();
        }

        assert_eq!(allocated.owner.count().get(), 1);

        assert!(allocated.try_into_vec().is_ok());
    }
}
