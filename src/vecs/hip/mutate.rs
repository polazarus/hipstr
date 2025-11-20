use core::borrow::BorrowMut;
use core::mem::MaybeUninit;
use core::ops::RangeBounds;
use core::ptr::NonNull;
use core::{iter, mem, ptr};

use const_default::ConstDefault;
use rules_derive::rules_derive;

use super::{HipVec, Inline};
use crate::common::derives::{AsRef, DelegateDebug, Deref, MutVector};
use crate::common::drain::Drain;
use crate::common::methods::{
    append_impl, extend_from_slice_copy_impl, extend_from_slice_impl, insert_impl, pop_impl,
    push_within_capacity, remove_unchecked_impl, resize_impl, spare_capacity_mut_impl,
    swap_remove_impl, truncate_impl,
};
use crate::common::traits::{MutVector, Mutate, Vector};
use crate::common::unwrap_display;
use crate::vecs::thin::{SmartThinVec, ThinVec};
use crate::Backend;

#[cfg(test)]
mod tests;

/// A mutable reference to a `HipVec`.

#[rules_derive(
    AsRef([T], Self::as_slice, Self::as_mut_slice),
    Deref([T], Self::as_slice, Self::as_mut_slice),
    DelegateDebug(Self::as_slice where T: core::fmt::Debug),
    MutVector(T)
)]
pub struct RefMut<'a, 'b, T, B: Backend>(&'a mut HipVec<'b, T, B>);

impl<'a, 'b, T, B: Backend> RefMut<'a, 'b, T, B> {
    #[must_use]
    pub(super) unsafe fn new(origin: &'a mut HipVec<'b, T, B>) -> Self {
        debug_assert!(origin.is_trimmed());
        debug_assert!(origin.is_unique());

        Self(origin)
    }

    /// Returns the current capacity of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::HipVec;
    /// let mut hip = HipVec::from([42; 42]);
    /// assert!(hip.mutate().capacity() >= 42);
    /// ```
    #[must_use]
    pub const fn capacity(&self) -> usize {
        if self.0.is_inline() {
            unsafe { self.0.as_inline_unchecked() }.capacity()
        } else if self.0.is_allocated() {
            unsafe { self.0.as_allocated_unchecked() }.owner.capacity()
        } else {
            debug_assert!(self.0.is_nil());
            0
        }
    }

    /// Returns the number of elements in the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::HipVec;
    /// let mut hip = HipVec::from([1, 2, 3, 4, 5]);
    /// assert_eq!(hip.mutate().len(), 5);
    ///
    #[must_use]
    pub const fn len(&self) -> usize {
        if self.0.is_inline() {
            // SAFETY: repr is checked above
            unsafe { self.0.as_inline_unchecked() }.len()
        } else if self.0.is_allocated() {
            // SAFETY: repr is checked above
            unsafe { self.0.as_allocated_unchecked() }.owner.len()
        } else {
            debug_assert!(self.0.is_nil());
            0
        }
    }

    /// Sets the length of the vector.
    ///
    /// # Safety
    ///
    /// The new length must be less than or equal to the capacity.
    /// The elements between the old length and the new length must be
    /// properly initialized.
    pub const unsafe fn set_len(&mut self, new_len: usize) {
        if self.0.is_inline() {
            // SAFETY: repr is checked above
            let inline = unsafe { self.0.as_mut_inline_unchecked() };
            // SAFETY: precondition
            unsafe {
                inline.set_len(new_len);
            }
        } else if self.0.is_allocated() {
            // SAFETY: repr is checked above
            let allocated = unsafe { self.0.as_mut_allocated_unchecked() };
            // SAFETY: precondition
            unsafe {
                allocated.owner.set_len(new_len);
            }
        } else {
            debug_assert!(new_len == 0);
            debug_assert!(self.0.is_nil());
        }
    }

    /// Returns `true` if the vector has a length of 0.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::HipVec;
    /// let mut hip = HipVec::new();
    /// assert!(hip.mutate().is_empty());
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns a pointer to the first element of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::HipVec;
    /// let hip = HipVec::from([1, 2, 3]);
    /// assert_eq!(unsafe { *hip.mutate().as_ptr() }, 1);
    /// ```
    #[must_use]
    pub const fn as_ptr(&self) -> *const T {
        if self.0.is_inline() {
            // SAFETY: repr is checked above
            unsafe { self.0.as_inline_unchecked() }.as_ptr()
        } else if self.0.is_allocated() {
            // SAFETY: repr is checked above
            unsafe { self.0.as_allocated_unchecked() }
                .owner
                .data()
                .as_ptr()
        } else {
            debug_assert!(self.0.is_nil());
            ptr::dangling()
        }
    }

    /// Returns a mutable pointer to the first element of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::HipVec;
    /// let mut hip = HipVec::from([1, 2, 3]);
    /// unsafe { *hip.mutate().as_mut_ptr() = 0; }
    /// assert_eq!(hip.as_slice(), &[0, 2, 3]);
    /// ```
    #[must_use]
    pub const fn as_mut_ptr(&mut self) -> *mut T {
        if self.0.is_inline() {
            unsafe { self.0.as_mut_inline_unchecked() }.as_mut_ptr()
        } else if self.0.is_allocated() {
            unsafe { self.0.as_mut_allocated_unchecked() }
                .owner
                .data_mut()
                .as_ptr()
        } else {
            debug_assert!(self.0.is_nil());
            ptr::dangling_mut()
        }
    }

    pub const fn as_non_null(&mut self) -> NonNull<T> {
        // SAFETY: as_mut_ptr's result is non null
        unsafe { NonNull::new_unchecked(self.as_mut_ptr()) }
    }

    /// Returns a slice of the vector's contents.
    #[must_use]
    #[inline]
    pub const fn as_slice(&self) -> &[T] {
        unsafe { core::slice::from_raw_parts(self.as_ptr(), self.len()) }
    }

    /// Returns a mutable slice of the vector's contents.
    #[must_use]
    #[inline]
    pub const fn as_mut_slice(&mut self) -> &mut [T] {
        unsafe { core::slice::from_raw_parts_mut(self.as_mut_ptr(), self.len()) }
    }

    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the given vector.
    ///
    /// The collection may reserve more space to avoid frequent reallocations.
    ///
    /// # Panics
    ///
    /// This function panics if the new capacity overflows.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::HipVec;
    /// let mut hip = HipVec::new();
    /// hip.mutate().reserve(10);
    /// assert!(hip.mutate().capacity() >= 10);
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        let len = self.len();
        let cap = self.capacity();
        if additional > cap - len {
            let required = len.checked_add(additional).expect("capacity overflow");
            let new_cap = required.max(cap * 2);
            unsafe {
                self.set_capacity(new_cap);
            }
        }
    }

    pub fn reserve_exact(&mut self, additional: usize) {
        let len = self.len();
        let cap = self.capacity();
        if additional > cap - len {
            let required = len.checked_add(additional).expect("capacity overflow");
            unsafe {
                self.set_capacity(required);
            }
        }
    }

    /// Sets the capacity of the vector.
    ///
    /// # Safety
    ///
    /// The new capacity must be greater than or equal to the current length.
    pub unsafe fn set_capacity(&mut self, new_cap: usize) {
        debug_assert!(self.0.is_unique(), "unique by type invariant");
        let len = self.len();
        debug_assert!(new_cap >= len);

        let cap = self.capacity();
        if new_cap == cap {
            return;
        }

        let new_cap = if new_cap == 0 {
            0
        } else if new_cap < HipVec::<T, B>::INLINE_CAP {
            HipVec::<T, B>::INLINE_CAP
        } else {
            new_cap
        };

        if new_cap == 0 {
            *self.0 = HipVec::DEFAULT;
        } else if new_cap <= HipVec::<T, B>::INLINE_CAP {
            unsafe {
                self.make_inline();
            }
        } else if self.0.is_thin() {
            // SAFETY: repr is checked above
            let allocated = unsafe { self.0.as_mut_allocated_unchecked() };

            // SAFETY: repr is checked above (thin) and unique
            let ref_mut = unsafe { allocated.owner.as_mut_thin_vec() };

            // SAFETY: new capacity >= len by precondition
            unsafe {
                ref_mut.set_capacity(new_cap);
            }
        } else {
            unsafe {
                self.make_thin(new_cap);
            }
        }
    }

    /// Converts the allocated vector from wide to thin.
    ///
    /// # Safety
    ///
    /// The vector must be allocated and wide.
    /// Its length must be less than or equal to `new_cap`.
    unsafe fn make_thin(&mut self, new_cap: usize) {
        debug_assert!(!self.0.is_thin());
        if self.0.is_inline() {
            let old = mem::replace(self.0, HipVec::DEFAULT);
            // SAFETY: repr is checked above
            let mut inline = unsafe { old.into_inline_unchecked() };
            let len = inline.len();
            debug_assert!(len <= new_cap);

            let mut thin: ThinVec<T, B> = ThinVec::with_capacity(new_cap);
            // SAFETY: capacity ≥ new length by `reserve`
            unsafe {
                inline.set_len(0);
                thin.as_mut_ptr()
                    .copy_from_nonoverlapping(inline.as_ptr(), len.min(new_cap));
                thin.set_len(len);
            }

            // SAFETY: thin vec with the default prefix
            let shared = unsafe { SmartThinVec::from_thin_vec_unchecked(thin) };
            let new = HipVec::from_smart_thin(shared);
            let old = mem::replace(self.0, new);
            mem::forget(old);
        } else if self.0.is_wide() {
            let old = mem::replace(self.0, HipVec::DEFAULT);
            // SAFETY: precondition
            let allocated = unsafe { old.into_allocated_unchecked() };
            let len = allocated.owner.len();
            debug_assert!(len <= new_cap);
            debug_assert!(allocated.owner.is_wide());
            debug_assert!(allocated.owner.is_unique());

            let mut thin: ThinVec<T, B> = ThinVec::with_capacity(new_cap);
            {
                // SAFETY: repr is checked above (wide)
                let smart_wide = unsafe { allocated.owner.into_smart_wide_unchecked() };
                debug_assert!(smart_wide.is_unique());

                // SAFETY: unique by type invariant
                let mut vec = unsafe { smart_wide.into_vec_unchecked() };
                debug_assert!(vec.len() <= new_cap);

                // SAFETY: capacity ≥ new length by `reserve`
                unsafe {
                    vec.set_len(0);
                    thin.as_mut_ptr()
                        .copy_from_nonoverlapping(vec.as_ptr(), len.min(new_cap));
                    thin.set_len(len);
                }
            }
            // SAFETY: thin vec with the default prefix
            let shared = unsafe { SmartThinVec::from_thin_vec_unchecked(thin) };

            let new = HipVec::from_smart_thin(shared);
            let old = mem::replace(self.0, new);
            mem::forget(old);
            // old is empty, it can be forgotten
        } else {
            debug_assert!(self.0.capacity() == 0 && self.0.is_borrowed());
            let new = HipVec::with_capacity(new_cap);
            let old = mem::replace(self.0, new);
            mem::forget(old);
        }
    }

    /// Converts the allocated vector into an inline vector.
    ///
    /// # Safety
    ///
    /// The vector's length must be less than or equal to the inline capacity.
    unsafe fn make_inline(&mut self) {
        if self.0.is_inline() {
            // do nothing
        } else if self.0.is_nil() {
            let old = mem::replace(self.0, HipVec::inline_empty());
            mem::forget(old);
        } else {
            debug_assert!(self.0.is_allocated());
            let old = mem::replace(self.0, HipVec::DEFAULT);
            let mut inline = Inline::new();
            // SAFETY: repr cannot be inline
            unsafe {
                let mut allocated = old.into_allocated_unchecked();
                let len = allocated.owner.len();
                debug_assert!(len <= HipVec::<T, B>::INLINE_CAP);
                allocated.owner.set_len(0);
                allocated
                    .owner
                    .data()
                    .as_ptr()
                    .copy_to_nonoverlapping(inline.as_mut_ptr(), len);
                allocated.owner.drop();
                inline.set_len(len);
            }
            let new = HipVec::from_inline(inline);
            let old = mem::replace(self.0, new);
            mem::forget(old);
            // old is empty, it can be forgotten
        }
    }

    /// Appends an element to this vector.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::vecs::HipVec;
    /// let mut vec = HipVec::from(b"abc");
    /// vec.mutate().push(b'd');
    /// assert_eq!(vec.as_slice(), b"abcd")
    /// ```
    pub fn push(&mut self, value: T) {
        self.reserve(1);
        let Ok(()) = self.push_within_capacity(value) else {
            unreachable!();
        };
    }

    /// Pushes a value to the end of the vector, assuming there is enough
    /// capacity.
    ///
    /// # Errors
    ///
    /// If there is not enough capacity, returns `Err(value)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::HipVec;
    /// let mut hip = HipVec::with_capacity(2);
    /// {
    ///     let mut m = hip.mutate();
    ///     let n = (0..).find(|i| r.push_with_capacity(i).is_err()).unwrap();
    ///     assert!(n >= 2);
    /// }
    /// assert!(hip.len() >= 2);
    /// ```
    pub const fn push_within_capacity(&mut self, value: T) -> Result<(), T> {
        push_within_capacity!(self, value)
    }

    /// Appends all element of the slice to this vector.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::vecs::HipVec;
    /// let mut h = HipVec::from(b"abc");
    /// h.mutate().push_slice(b"123");
    /// assert_eq!(h.as_slice(), b"abc123");
    /// ```
    #[doc(alias = "push_slice")]
    pub fn extend_from_slice(&mut self, slice: &[T])
    where
        T: Clone,
    {
        extend_from_slice_impl!(self, slice);
    }

    /// Appends all element of the slice to this vector.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::vecs::HipVec;
    /// let mut h = HipVec::from(b"abc");
    /// h.mutate_copy().push_slice_copy(b"123");
    /// assert_eq!(h.as_slice(), b"abc123");
    /// ```
    pub fn extend_from_slice_copy(&mut self, slice: &[T])
    where
        T: Copy,
    {
        extend_from_slice_copy_impl!(self, slice);
    }

    /// Shortens this vector to the specified length.
    ///
    /// If the new length is greater than the current length, this has no
    /// effect.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::vecs::HipVec;
    /// let mut a = HipVec::from(b"abc");
    /// a.mutate().truncate(1);
    /// assert_eq!(a.as_slice(), b"a");
    /// ```
    pub fn truncate(&mut self, new_len: usize) {
        truncate_impl!(self, new_len);
    }

    /// Truncates this vector, removing all contents.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::HipByt;
    /// let mut s = HipByt::from(b"foo");
    ///
    /// s.mutate().clear();
    ///
    /// assert!(s.is_empty());
    /// assert_eq!(0, s.len());
    /// ```
    pub fn clear(&mut self) {
        self.truncate(0);
    }

    /// Removes the last element from this vector and returns it, or [`None`]
    /// if it is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::vecs::HipVec;
    /// let mut h = HipVec::from([1, 2, 3]);
    /// assert_eq!(h.mutate_copy().pop(), Some(3));
    /// assert_eq!(h.as_slice(), [1, 2]);
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        pop_impl!(self)
    }

    /// Shrinks the capacity of the vector with a lower bound.
    ///
    /// The capacity will remain at least as large as the given bound and the
    /// actual length of the vec-tor.
    ///
    /// # Representation stability
    ///
    /// The representation may change:
    /// - to the normal empty if the required capacity is zero,
    /// - to inline if the required capacity is smaller than the inline
    ///   capacity.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hipstr::vecs::HipVec;
    /// let mut s = HipVec::<u9>::with_capacity(100);
    /// {
    ///     let mut m = s.mutate_copy();
    ///     m.shrink_to(4);
    ///     assert_eq!(m.capacity(), HipVec::<u8>::INLINE_CAP);
    /// }
    /// assert!(s.is_inline());
    /// ```
    pub fn shrink_to(&mut self, cap: usize) {
        if cap >= self.len() && cap < self.capacity() {
            unsafe {
                self.set_capacity(cap);
            }
        }
    }

    /// Shrinks the capacity of the vector as much as possible.
    ///
    /// The capacity will remain at least as large as the actual length of the
    /// vector.
    ///
    /// # Representation stability
    ///
    /// The representation may change:
    /// - to the normal empty if the required capacity is zero,
    /// - to inline if the required capacity is smaller than the inline
    ///   capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::vecs::HipVec;
    /// let mut s = HipVec::<u9>::with_capacity(100);
    /// {
    ///     let mut m = s.mutate_copy();
    ///     m.shrink_to_fit();
    ///     assert_eq!(m.capacity(), HipVec::<u8>::INLINE_CAP);
    /// }
    /// assert!(s.is_empty() && !s.is_allocated());
    /// ```
    pub fn shrink_to_fit(&mut self) {
        self.shrink_to(self.len());
    }

    pub fn swap_remove(&mut self, index: usize) -> T {
        swap_remove_impl!(self, index)
    }

    pub fn remove(&mut self, index: usize) -> T {
        assert!(index < self.len(), "index out of bounds");
        remove_unchecked_impl!(self, index)
    }

    pub fn insert(&mut self, index: usize, value: T) {
        insert_impl!(self, index, value);
    }

    pub fn append(&mut self, other: &mut impl Mutate<Item = T>) {
        let mut other = other.mutate();
        let other = other.borrow_mut();
        append_impl!(self, other);
    }

    pub fn drain(&mut self, range: impl RangeBounds<usize>) -> Drain<'_, Self> {
        unwrap_display(Drain::new(self, range))
    }

    pub fn spare_capacity_mut(&mut self) -> &mut [MaybeUninit<T>] {
        spare_capacity_mut_impl!(self)
    }

    pub fn resize(&mut self, new_len: usize, value: T)
    where
        T: Clone,
    {
        resize_impl!(self, new_len, value.clone())
    }

    pub fn resize_copy(&mut self, new_len: usize, value: T)
    where
        T: Copy,
    {
        if let Some(additional) = new_len.checked_sub(self.len()) {
            self.reserve(additional);
            self.spare_capacity_mut()[..additional].fill(MaybeUninit::new(value));
            unsafe {
                self.set_len(new_len);
            }
        } else {
            self.truncate(new_len);
        }
    }

    pub fn resize_with(&mut self, new_len: usize, f: impl FnMut() -> T) {
        let mut f = f;
        resize_impl!(self, new_len, f())
    }
}

impl<T, B: Backend> Drop for RefMut<'_, '_, T, B> {
    fn drop(&mut self) {
        if self.0.is_inline() {
            // nothing to do
        } else if self.0.is_allocated() {
            // SAFETY: repr is checked above
            let allocated = unsafe { self.0.as_mut_allocated_unchecked() };
            allocated.ptr = allocated.owner.data().as_ptr();
            allocated.len = allocated.owner.len();
        } else {
            let sliced = unsafe { self.0.as_mut_sliced_unchecked() };
            sliced.ptr = ptr::dangling();
            sliced.len = 0;
        }
        debug_assert!(self.0.is_valid());
    }
}
