use alloc::vec::Vec;
use core::marker::PhantomData;
use core::mem::{needs_drop, transmute, ManuallyDrop};
use core::ops::{Range, RangeBounds};
use core::ptr;

use const_default::ConstDefault;
use rules_derive::rules_derive;
use typenum::Unsigned;

use self::repr::{Allocated, Borrowed, Owner, Pivot, Sliced, UnknownSliced};
use crate::backend::UpdateResult;
use crate::common::derives::{AsRef, ConstDefault, Copy, DelegateDebug, DelegateHash, Deref, From};
use crate::common::traits::Mutate;
use crate::common::{self, drop_raw_slice, force_transmute};
use crate::vecs::inline::{InlineLength, InlineVec};
use crate::vecs::smart_fat::SmartFatVec;
use crate::vecs::smart_thin::SmartThinVec;
use crate::vecs::thin::{can_reuse, ThinVec};
use crate::Backend;

pub(crate) mod repr;

#[cfg(test)]
mod tests;

#[rules_derive(
    ConstDefault(Self::EMPTY),
    AsRef([T], Self::as_slice),
    Deref([T], Self::as_slice),
    From([T; N], Self::from_array, (const N: usize)),
    From(Vec<T>, Self::from_vec),
    From(ThinVec<T, P>, Self::from_thin_vec, (P: ConstDefault)),
    From(&[T], Self::from_slice_clone, () where (T: Clone)),
    From(InlineVec<T, L>, Self::from_inline, (L: InlineLength)),
    DelegateDebug(Self::as_slice where T: core::fmt::Debug),
    DelegateHash(Self::as_slice where T: core::hash::Hash),
)]
pub struct HipVec<'a, T, B: Backend>(Pivot, PhantomData<(B, &'a [T])>);
pub const INLINE_BYTES: usize = size_of::<Borrowed<()>>();
pub type InlineBytes = crate::typenum::U<INLINE_BYTES>;
type HipInline<T> = InlineVec<T, InlineBytes>;

impl<'a, T, B: Backend> HipVec<'a, T, B> {
    const EMPTY: Self = Self::borrowed(&[]);
    pub const INLINE_CAP: usize = InlineVec::<T, InlineBytes>::CAPACITY;
    const MAY_INLINE: bool = align_of::<T>() <= align_of::<Self>() && Self::INLINE_CAP > 0;

    const fn fit_inline(len: usize) -> bool {
        Self::MAY_INLINE && len <= Self::INLINE_CAP
    }

    /// Creates a new empty `HipVec`.
    ///
    /// This vector is not *allocated*.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::HipVec;
    /// let a: HipVec<u8> = HipVec::new();
    /// assert!(a.is_empty());
    /// assert!(!a.is_allocated());
    /// ```
    #[must_use]
    pub const fn new() -> Self {
        Self::EMPTY
    }

    /// Creates a `HipVec` from an array.
    #[must_use]
    #[inline]
    pub(crate) fn from_array<const N: usize>(array: [T; N]) -> Self {
        if N == 0 {
            Self::new()
        } else if const { Self::fit_inline(N) } {
            let inline = HipInline::from_array(array);
            Self::from_inline(inline)
        } else {
            let smart = SmartThinVec::from_array(array);
            Self::from_smart_thin(smart)
        }
    }

    #[must_use]
    #[inline]
    pub fn from_vector_normalized(v: impl Mutate<Item = T>) -> Self {
        if v.len() == 0 {
            Self::new()
        } else if Self::fit_inline(v.len()) {
            let inline = HipInline::from_vector(v);
            Self::from_inline(inline)
        } else {
            let smart = SmartThinVec::from_vector(v);
            Self::from_smart_thin(smart)
        }
    }

    #[must_use]
    #[inline]
    pub fn from_vec(vec: Vec<T>) -> Self {
        if vec.capacity() == 0 {
            Self::new()
        } else {
            let smart = SmartFatVec::from_vec(vec);
            let sliced = Sliced {
                ptr: smart.as_ptr(),
                len: smart.len(),
                owner: smart, // the cast is not necessary SmartFatVec is transparent
            };
            // SAFETY: repr is correct by construction
            unsafe { transmute::<Sliced<T, SmartFatVec<T, B>>, Self>(sliced) }
        }
    }

    #[must_use]
    #[inline]
    pub(crate) fn from_thin_vec<P: ConstDefault>(v: ThinVec<T, P>) -> Self {
        if v.capacity() > 0 && can_reuse::<T, P, B>() {
            let v: ThinVec<T, B> = v.fresh_move();
            let s = unsafe { SmartThinVec::from_thin_vec_unchecked(v) };
            Self::from_smart_thin(s)
        } else {
            Self::from_vector_normalized(v)
        }
    }

    /// Returns `true` if the vector is stored inline.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::HipVec;
    /// let a: HipVec<u8> = HipVec::from([1,2,3]);
    /// assert!(a.is_inline());
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_inline(&self) -> bool {
        self.0.is_inline()
    }

    /// Returns `true` if the vector is allocated on the heap.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::HipVec;
    /// let a: HipVec<u8> = HipVec::from([0; 1024]);
    /// assert!(!a.is_inline());
    /// //assert!(!a.is_borrowed());
    /// //assert!(a.is_allocated());
    /// //assert_eq!(a.len(), 1024);
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_allocated(&self) -> bool {
        self.0.is_allocated()
    }

    /// Returns `true` if the vector is borrowed.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::HipVec;
    /// let slice: &[u8] = &[1,2,3];
    /// let a: HipVec<u8> = HipVec::borrowed(slice);
    /// assert!(a.is_borrowed());
    /// assert!(!a.is_inline());
    /// assert!(!a.is_allocated());
    /// assert_eq!(a.len(), 3);
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_borrowed(&self) -> bool {
        self.0.is_borrowed()
    }

    /// Returns `true` if the vector is uniquely owned.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::HipVec;
    /// let a: HipVec<u8> = HipVec::from([b'*'; 42]);
    /// assert!(a.is_unique());
    /// let b = a.clone();
    /// assert!(!a.is_unique());
    /// ```
    #[must_use]
    #[inline]
    pub fn is_unique(&self) -> bool {
        self.is_inline()
            || (self.is_allocated() && unsafe { self.as_allocated_unchecked() }.owner.is_unique())
    }

    #[must_use]
    #[inline]
    pub const fn is_fat(&self) -> bool {
        self.is_allocated() && unsafe { self.as_allocated_unchecked() }.owner.is_fat()
    }

    #[must_use]
    pub const fn is_thin(&self) -> bool {
        self.is_allocated() && unsafe { self.as_allocated_unchecked() }.owner.is_thin()
    }

    #[must_use]
    pub const fn as_ptr(&self) -> *const T {
        if self.is_inline() {
            unsafe { self.as_inline_unchecked() }.as_ptr()
        } else {
            unsafe { self.as_sliced_unchecked() }.as_ptr()
        }
    }

    #[must_use]
    pub const fn len(&self) -> usize {
        if self.is_inline() {
            unsafe { self.as_inline_unchecked() }.len()
        } else {
            unsafe { self.as_sliced_unchecked() }.len()
        }
    }

    /// Returns `true` if the vector has a length of 0.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::HipVec;
    /// let a: HipVec<u8> = HipVec::new();
    /// assert!(a.is_empty());
    ///
    /// let b: HipVec<u8> = HipVec::from([1,2,3]);
    /// assert!(!b.is_empty());
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[must_use]
    pub const fn as_slice(&self) -> &[T] {
        if self.is_inline() {
            unsafe { self.as_inline_unchecked() }.as_slice()
        } else {
            unsafe { self.as_sliced_unchecked() }.as_slice()
        }
    }

    /// Gets the inline representation.
    ///
    /// # Safety
    ///
    /// The vector must be inline.
    const unsafe fn as_inline_unchecked(&self) -> &InlineVec<T, InlineBytes> {
        debug_assert!(self.is_inline());
        // SAFETY: precondition
        unsafe { &*ptr::from_ref(self).cast() }
    }

    /// Gets a mutable reference to the underlying inline representation.
    ///
    /// # Safety
    ///
    /// The vector must be inline.
    const unsafe fn as_inline_mut_unchecked(&mut self) -> &mut InlineVec<T, InlineBytes> {
        debug_assert!(self.is_inline());
        // SAFETY: precondition
        unsafe { &mut *ptr::from_mut(self).cast() }
    }

    /// Gets a reference to the underlying sliced representation.
    ///
    /// # Safety
    ///
    /// The vector must not be inline.
    const unsafe fn as_sliced_unchecked(&self) -> &UnknownSliced<T> {
        debug_assert!(!self.is_inline());
        // SAFETY: precondition
        unsafe { &*ptr::from_ref(self).cast() }
    }

    /// Gets a mutable reference to the underlying sliced representation.
    ///
    /// # Safety
    ///
    /// The vector must not be inline.
    const unsafe fn as_sliced_mut_unchecked(&mut self) -> &mut UnknownSliced<T> {
        debug_assert!(!self.is_inline());
        // SAFETY: precondition
        unsafe { &mut *ptr::from_mut(self).cast() }
    }

    /// Gets a reference to the underlying allocated representation.
    ///
    /// # Safety
    ///
    /// The vector must be allocated.
    const unsafe fn as_allocated_unchecked(&self) -> &Allocated<T, B> {
        debug_assert!(self.is_allocated());
        // SAFETY: precondition
        unsafe { &*ptr::from_ref(self).cast() }
    }

    /// Gets a mutable reference to the underlying allocated representation.
    ///
    /// # Safety
    ///
    /// The vector must be allocated and unique.
    const unsafe fn as_allocated_mut_unchecked(&mut self) -> &mut Allocated<T, B> {
        debug_assert!(self.is_allocated());
        // SAFETY: precondition
        unsafe { &mut *ptr::from_mut(self).cast() }
    }

    /// Creates a borrowed `HipVec` from a slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::HipVec;
    /// let slice: &[u8] = &[1, 2, 3];
    /// let a: HipVec<u8> = HipVec::borrowed(slice);
    /// assert!(a.is_borrowed());
    /// ```
    #[must_use]
    pub const fn borrowed(slice: &'a [T]) -> Self {
        let borrowed = Borrowed::<'a, T>::new(slice);
        unsafe { transmute(borrowed) }
    }

    /// Creates an inline `HipVec` from an `InlineVec`.
    ///
    /// In the case where the inline byte size is equal to the inline byte size
    /// of the `HipVec`, the actual representation is reused. Otherwise, the
    /// elements are moved to a compatible inline vector.
    ///
    /// # Panics
    ///
    /// This function panics if:
    /// - either the length of the input inline vector exceeds the inline
    ///   capacity of the `HipVec`,
    /// - or if the `HipVec` cannot be inlined (that is, the alignment of `T` is
    ///   greater than the alignment of the `HipVec`).
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::HipVec;
    /// use hipstr::inline_vec;
    /// let inline = inline_vec![24 => 1, 2, 3];
    /// let hip: HipVec<u8> = HipVec::from_inline(inline);
    /// assert!(hip.is_inline());
    #[must_use]
    pub const fn from_inline<L: InlineLength>(inline: InlineVec<T, L>) -> Self {
        // compile time check transformed to runtime panic
        assert!(Self::MAY_INLINE, "this vector cannot be inlined");

        if const { InlineBytes::USIZE == L::USIZE } {
            // reuse the inline representation if sizes match
            debug_assert!(Self::MAY_INLINE);

            // SAFETY: sizes are equal, inline repr
            unsafe { force_transmute::<InlineVec<T, L>, Self>(inline) }
        } else {
            // move the elements to a new compatible inline vector
            let mut old = inline;
            let mut new = InlineVec::new();
            new.const_append(&mut old);

            // forget the old inline vector, the drop is not necessary since the
            // elements were moved out beforehand
            let _ = ManuallyDrop::new(old);

            // SAFETY: inline repr
            unsafe { force_transmute::<InlineVec<T, InlineBytes>, Self>(new) }
        }
    }

    /// Creates a `HipVec` from a slice by cloning the elements.
    #[must_use]
    pub(crate) fn from_slice_clone(slice: &[T]) -> Self
    where
        T: Clone,
    {
        if slice.len() <= Self::INLINE_CAP {
            let inline = HipInline::from_slice_clone(slice);
            Self::from_inline(inline)
        } else {
            let smart = SmartThinVec::from_slice_clone(slice);
            Self::from_smart_thin(smart)
        }
    }

    #[must_use]
    pub(crate) fn from_slice_copy(slice: &[T]) -> Self
    where
        T: Copy,
    {
        if slice.len() <= Self::INLINE_CAP {
            let inline = HipInline::from_slice_copy(slice);
            Self::from_inline(inline)
        } else {
            let smart = SmartThinVec::from_slice_copy(slice);
            Self::from_smart_thin(smart)
        }
    }

    #[must_use]
    pub const fn from_smart_thin(v: SmartThinVec<T, B>) -> Self {
        let len = v.len();
        let ptr = v.as_ptr();

        #[cfg(debug_assertions)]
        let is_null = v.capacity() == 0;

        let owner = v;
        let this =
            unsafe { transmute::<Sliced<T, SmartThinVec<T, B>>, Self>(Sliced { owner, ptr, len }) };

        #[cfg(debug_assertions)]
        if is_null {
            debug_assert!(this.is_borrowed());
        } else {
            debug_assert!(this.is_allocated());
        }

        this
    }

    const unsafe fn owner_mut_unchecked(&mut self) -> &mut Owner<T, B> {
        debug_assert!(self.is_allocated());
        unsafe { &mut self.as_allocated_mut_unchecked().owner }
    }

    const unsafe fn copy(&self) -> Self {
        Self(self.0, PhantomData)
    }

    pub fn detach(&mut self)
    where
        T: Clone,
    {
        if self.is_unique() {
            // do nothing
        } else {
            let new = Self::from_slice_clone(self.as_slice());
            *self = new;
        }
    }

    pub fn detach_copy(&mut self)
    where
        T: Copy,
    {
        if self.is_unique() {
            // do nothing
        } else {
            let new = Self::from_slice_copy(self.as_slice());
            *self = new;
        }
    }

    /// Returns a slice of the vector.
    ///
    /// # Panics
    ///
    /// Panics if the range is out of bounds or if the reference count
    /// overflows.
    #[must_use]
    pub fn slice(&self, range: impl RangeBounds<usize>) -> Self
    where
        T: Clone,
    {
        let range = common::range(range, self.len()).unwrap();
        self.slice_range(range)
    }

    fn slice_range(&self, range: Range<usize>) -> Self
    where
        T: Clone,
    {
        if Self::MAY_INLINE && range.len() < Self::INLINE_CAP {
            let inline = HipInline::from_slice_clone(&self.as_slice()[range]);
            Self::from_inline(inline)
        } else {
            debug_assert!(!self.is_inline());

            if self.is_allocated() {
                // SAFETY: repr is checked above
                let owner = unsafe { &self.as_allocated_unchecked().owner };
                if owner.counter().incr() == UpdateResult::Overflow {
                    return Self::from_slice_clone(&self.as_slice()[range]);
                }
            }

            // SAFETY: counter is incremented if allocated
            // otherwise, the borrowed slice is copyable
            let mut copy = unsafe { self.copy() };
            unsafe {
                let copy = copy.as_sliced_mut_unchecked();
                copy.ptr = copy.ptr.add(range.start);
                copy.len = range.len();
            }
            copy
        }
    }

    /// Removes the last element from the vector and returns it, or `None` if
    /// it is empty.
    ///
    /// Note that if the vector is not unique, the last element is cloned.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::HipVec;
    /// let mut hip = HipVec::from([1, 2, 3]);
    /// assert_eq!(hip.pop(), Some(3));
    /// assert_eq!(hip.pop(), Some(2));
    /// assert_eq!(hip.pop(), Some(1));
    /// assert_eq!(hip.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<T>
    where
        T: Clone,
    {
        if self.is_inline() {
            // SAFETY: repr is checked above
            let inline = unsafe { self.as_inline_mut_unchecked() };
            inline.pop()
        } else if self.is_empty() {
            None
        } else {
            if self.is_allocated() {
                // SAFETY: repr is checked above
                let allocated = unsafe { self.as_allocated_mut_unchecked() };
                let owner = &mut allocated.owner;
                if owner.is_unique() {
                    let ptr = owner.data().as_ptr();

                    // SAFETY: the slice is inside the owner's buffer by type
                    // invariant
                    unsafe {
                        let slice_end = allocated.ptr.add(allocated.len);
                        // compute the actual length
                        let actual_len = ptr.offset_from_unsigned(slice_end);

                        // compute the remaining part
                        let rem_ptr = ptr.add(actual_len);
                        let rem_len = owner.len() - actual_len;

                        // drop the remaining elements
                        drop_raw_slice(rem_ptr, rem_len);
                        // move the last element out
                        let value = ptr.add(actual_len - 1).read();
                        // update the length
                        owner.set_len(actual_len - 1);
                        return Some(value);
                    }
                }
            }

            // not unique => we clone the last value and update the length

            // SAFETY: not inlined
            let sliced = unsafe { self.as_sliced_mut_unchecked() };

            // SAFETY: not empty
            let last = unsafe { &*sliced.ptr.add(sliced.len - 1) };

            // clone the value to return
            let value = last.clone();

            // update the length
            sliced.len -= 1;
            Some(value)
        }
    }

    /// Clears the vector, removing all values.
    ///
    /// Note that if the vector is not inline, clearing will not drop any
    /// elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::HipVec;
    /// let mut hip = HipVec::from([1, 2, 3]);
    /// assert_eq!(hip.len(), 3);
    /// hip.clear();
    /// assert_eq!(hip.len(), 0);
    /// ```
    pub fn clear(&mut self) {
        self.truncate(0);
    }

    /// Tightens the allocated vector (without shifting), dropping excess
    /// elements if the vector is uniquely owned.
    pub fn tighten(&mut self) {
        if self.is_allocated() {
            // SAFETY: repr is checked above
            let allocated = unsafe { self.as_allocated_mut_unchecked() };
            let owner = &mut allocated.owner;
            if owner.is_unique() {
                let ptr = owner.data().as_ptr();

                // SAFETY: the slice is inside the owner's buffer by type
                // invariant
                unsafe {
                    let slice_end = allocated.ptr.add(allocated.len);
                    // compute the actual length
                    let actual_len = slice_end.offset_from_unsigned(ptr);

                    // compute the remaining part
                    let rem_ptr = ptr.add(actual_len);
                    let rem_len = owner.len() - actual_len;

                    // drop the remaining elements
                    drop_raw_slice(rem_ptr, rem_len);

                    // update the length
                    owner.set_len(actual_len);
                }
            }
        }
    }

    pub fn tighten_and_shift(&mut self) {
        if self.is_allocated() {
            // SAFETY: repr is checked above
            let allocated = unsafe { self.as_allocated_mut_unchecked() };
            let owner = &mut allocated.owner;
            if owner.is_unique() {
                let ptr = owner.data().as_ptr();
                let shift = unsafe { allocated.ptr.offset_from_unsigned(ptr) };

                // drop the first `shift` elements
                // SAFETY: the slice is inside the owner's buffer by type invariant
                unsafe {
                    drop_raw_slice(ptr, shift);
                }

                // move the visible elements to the start of the buffer
                // SAFETY: the slice is inside the owner's buffer by type invariant
                unsafe {
                    ptr.copy_from(ptr.add(shift), allocated.len);
                }

                // drop the excess elements
                let excess_start = shift + allocated.len;
                let excess_len = owner.len() - excess_start;

                // SAFETY: the whole slice is inside the owner's buffer by type invariant
                unsafe {
                    drop_raw_slice(ptr.add(excess_start), excess_len);
                }

                // SAFETY: the slice is inside the owner's buffer by type
                // invariant
                unsafe {
                    // update the length
                    owner.set_len(allocated.len);
                }
            }
        }
    }

    /// Splits the vector into two at the given index.
    ///
    /// The original vector contains elements `[0, at)`, and the returned vector
    /// contains elements `[at, len)`.
    ///
    /// # Errors
    ///
    /// - If `at > len`, returns `SplitOffError::OutOfBounds`.
    /// - If the reference count overflows, returns `SplitOffError::RefCountOverflow`.
    pub fn try_split_off(&mut self, at: usize) -> Result<Self, SplitOffError> {
        let len = self.len();
        if at > self.len() {
            Err(SplitOffError::OutOfBounds)
        } else if at == len {
            Ok(Self::new())
        } else if self.is_inline() {
            // inline representation, just split the inline vector
            // SAFETY: repr is inline
            let inline = unsafe { self.as_inline_mut_unchecked() };
            let new_inline = inline.split_off(at);
            Ok(Self::from_inline(new_inline))
        } else {
            // checks if allocated or borrowed
            if self.is_allocated() {
                // increment the owner reference count
                let owner = unsafe { self.owner_mut_unchecked() };
                if owner.counter().incr() == UpdateResult::Overflow {
                    return Err(SplitOffError::RefCountOverflow);
                }
            }

            // SAFETY: the reference count was incremented if needed
            let mut other = unsafe { self.copy() };

            // SAFETY: repr is not inline
            unsafe {
                // update the current vector
                self.as_sliced_mut_unchecked().len = at;
            }

            // SAFETY: same repr for other
            unsafe {
                // set the slice for the other vector
                let other = other.as_sliced_mut_unchecked();
                other.ptr = other.ptr.add(at);
                other.len -= at;
            };
            Ok(other)
        }
    }

    /// Splits the vector into two at the given index.
    ///
    /// The original vector contains elements `[0, at)`, and the returned vector
    /// contains elements `[at, len)`.
    ///
    /// This function clones the elements to the returned vector if the
    /// reference count overflows.
    ///
    /// # Panics
    ///
    /// This function panics if `at > len`.
    #[must_use]
    pub fn split_off(&mut self, at: usize) -> Self
    where
        T: Clone,
    {
        match self.try_split_off(at) {
            Ok(v) => v,
            Err(SplitOffError::OutOfBounds) => panic!("split index out of bounds"),
            Err(SplitOffError::RefCountOverflow) => {
                let new = Self::from_slice_clone(&self.as_slice()[at..]);
                self.truncate(at);
                new
            }
        }
    }

    /// Splits the vector into two at the given index.
    ///
    /// The original vector contains elements `[0, at)`, and the returned vector
    /// contains elements `[at, len)`.
    ///
    /// This function copies the elements to the returned vector
    /// if the reference count overflows.
    ///
    /// # Panics
    ///
    /// This function panics if `at > len`.
    #[must_use]
    pub fn split_off_copy(&mut self, at: usize) -> Self
    where
        T: Copy,
    {
        match self.try_split_off(at) {
            Ok(v) => v,
            Err(SplitOffError::OutOfBounds) => panic!("split index out of bounds"),
            Err(SplitOffError::RefCountOverflow) => {
                let new = Self::from_slice_copy(&self.as_slice()[at..]);
                self.truncate(at);
                new
            }
        }
    }

    // Shortens the vector, keeping the first `new_len` elements and dropping
    /// the rest.
    ///
    /// If `new_len` is greater than the vector's current length, this has no
    /// effect.
    ///
    /// Note that if the vector is not inline, truncating will not drop the
    /// elements beyond the new length.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::HipVec;
    /// let mut hip = HipVec::from([1, 2, 3, 4, 5]);
    /// assert_eq!(hip.len(), 5);
    /// hip.truncate(3);
    /// assert_eq!(hip.len(), 3);
    /// assert_eq!(hip.as_slice(), &[1, 2, 3]);
    /// hip.truncate(10); // has no effect
    /// assert_eq!(hip.len(), 3);
    /// ```
    pub fn truncate(&mut self, len: usize) {
        if self.is_inline() {
            // SAFETY: repr checked above
            let inline = unsafe { self.as_inline_mut_unchecked() };
            inline.truncate(len);
        } else {
            let sliced = unsafe { self.as_sliced_mut_unchecked() };
            sliced.len = len;
        }
    }
}

impl<T, B: Backend> Drop for HipVec<'_, T, B> {
    fn drop(&mut self) {
        if self.is_inline() {
            if needs_drop::<T>() {
                // SAFETY: repr checked above
                let inline = unsafe { self.as_inline_mut_unchecked() };
                // SAFETY: will no be used after drop
                unsafe {
                    inline.drop_contents();
                }
            }
        } else if self.is_allocated() {
            // SAFETY: repr checked above
            let owner = unsafe { self.owner_mut_unchecked() };
            // SAFETY: will no be used after drop
            unsafe {
                owner.drop();
            }
        }
    }
}

impl<T: Clone, B: Backend> Clone for HipVec<'_, T, B> {
    fn clone(&self) -> Self {
        if self.is_inline() {
            // SAFETY: repr is checked above
            let inline = unsafe { self.as_inline_unchecked() };
            // TODO optimize if T is Copy
            Self::from_inline(inline.clone())
        } else {
            if self.is_allocated() {
                // SAFETY: repr is checked above
                let allocated = unsafe { self.as_allocated_unchecked() };
                if allocated.owner.counter().incr() == UpdateResult::Overflow {
                    return Self::from_slice_clone(allocated.as_slice());
                }
            }
            // SAFETY: either ref count increased or borrowed repr => copyable
            unsafe { self.copy() }
        }
    }
}

/// Error type for `HipVec::try_split_off`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum SplitOffError {
    /// The split index is greater than the length of the vector.
    OutOfBounds,
    /// The reference count overflowed.
    RefCountOverflow,
}
