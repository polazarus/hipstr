use alloc::vec::Vec;
use core::marker::PhantomData;
use core::mem::{self, needs_drop, transmute, ManuallyDrop};
use core::ops::{Range, RangeBounds};
use core::ptr;

use const_default::ConstDefault;
use rules_derive::rules_derive;
use typenum::Unsigned;

use self::repr::{
    check_wide_and_thin_compatibility, Allocated, Borrowed, Owner, Pivot, Sliced, UnknownSliced,
};
use crate::backend::UpdateResult;
use crate::common::derives::{AsRef, ConstDefault, Copy, DelegateDebug, DelegateHash, Deref, From};
use crate::common::methods::push_within_capacity;
use crate::common::traits::Mutate;
use crate::common::{self, drop_raw_slice, force_transmute};
use crate::vecs::inline::{InlineLength, InlineVec};
use crate::vecs::thin::{can_reuse, SmartThinVec, ThinVec};
use crate::vecs::wide::SmartWideVec;
use crate::Backend;

pub(crate) mod repr;

#[cfg(test)]
mod tests;

/// Hip vector, i.e. inline, copy on write shared, or borrowed.
///
/// # Examples
///
/// ```
/// use hipstr::vecs::HipVec;
/// let h: HipVec<Box<i32>> = HipVec::from([1, 2, 3].map(Box::new));
/// let h2 = h.clone();
/// assert!(std::ptr::eq(h.as_slice(), h2.as_slice()));
/// ```
#[rules_derive(
    ConstDefault(Self::borrowed(&[])),
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

/// Byte size for `HipVec`.
pub const BYTES: usize = size_of::<Borrowed<()>>();

/// Byte size for `HipVec` as a type.
pub type Bytes = crate::typenum::U<BYTES>;

/// Inline vector type for `HipVec`.
pub type Inline<T> = InlineVec<T, Bytes>;

impl<'a, T, B: Backend> HipVec<'a, T, B> {
    /// Inline capacity in number of elements.
    pub const INLINE_CAP: usize = if align_of::<T>() <= align_of::<Self>() {
        Inline::<T>::CAPACITY
    } else {
        0
    };

    const MAY_INLINE: bool = Self::INLINE_CAP > 0;

    const fn fit_inline(len: usize) -> bool {
        len > 0 && len <= Self::INLINE_CAP
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
        #[cfg(debug_assertions)]
        {
            check_wide_and_thin_compatibility::<T, B>();
        }
        Self::DEFAULT
    }

    /// Creates a `HipVec` from an array.
    #[must_use]
    #[inline]
    pub(crate) fn from_array<const N: usize>(array: [T; N]) -> Self {
        if N == 0 {
            Self::new()
        } else if const { Self::fit_inline(N) } {
            let inline = Inline::from_array(array);
            Self::from_inline(inline)
        } else {
            let smart = SmartThinVec::from_array(array);
            Self::from_smart_thin(smart)
        }
    }

    /// Creates a `HipVec` from a vector, normalizing the representation.
    ///
    /// A normalized representation is:
    ///
    /// - the usual empty vector (same as [`HipVec::DEFAULT`]),
    /// - inline vector if it fits,
    /// - allocated thin otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::HipVec;
    /// let a: HipVec<u8> = HipVec::from_vector_normalized(vec![1,2,3]);
    /// assert!(a.is_inline());
    /// let b: HipVec<u8> = HipVec::from_vector_normalized(vec![0; 1024]);
    /// assert!(b.is_allocated());
    /// assert!(b.is_thin());
    /// ```
    #[must_use]
    #[inline]
    pub fn from_vector_normalized(v: impl Mutate<Item = T>) -> Self {
        if v.len() == 0 {
            Self::new()
        } else if Self::fit_inline(v.len()) {
            let inline = Inline::from_vector(v);
            Self::from_inline(inline)
        } else {
            let smart = SmartThinVec::from_vector(v);
            Self::from_smart_thin(smart)
        }
    }

    /// Creates a `HipVec` from a [`Vec`].
    #[must_use]
    #[inline]
    pub(crate) fn from_vec(vec: Vec<T>) -> Self {
        let smart = SmartWideVec::from_vec(vec);
        let sliced = Sliced {
            ptr: smart.as_ptr(),
            len: smart.len(),
            owner: smart, // the cast is not necessary SmartWideVec is transparent
        };
        // SAFETY: repr is correct by construction
        unsafe { transmute::<Sliced<T, SmartWideVec<T, B>>, Self>(sliced) }
    }

    /// Creates a `HipVec` from a [`ThinVec`], reusing the representation if
    /// possible.
    #[must_use]
    #[inline]
    pub(crate) fn from_thin_vec<P: ConstDefault>(v: ThinVec<T, P>) -> Self {
        if can_reuse::<T, P, B>() {
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
    /// assert!(!a.is_borrowed());
    /// assert!(a.is_allocated());
    /// assert_eq!(a.len(), 1024);
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

    /// Returns `true` if the vector is allocated and uses the wide backend.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::HipVec;
    /// let a: HipVec<u8> = HipVec::from(vec![0; 32]);
    /// assert!(a.is_allocated());
    /// assert!(a.is_wide());
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_wide(&self) -> bool {
        self.is_allocated() && unsafe { self.as_allocated_unchecked() }.owner.is_wide()
    }

    /// Returns `true` if the vector is allocated and uses the thin backend.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::HipVec;
    /// let a: HipVec<u8> = HipVec::from([0; 1024]);
    /// assert!(a.is_allocated());
    /// assert!(a.is_thin());
    /// ```
    #[must_use]
    pub const fn is_thin(&self) -> bool {
        self.is_allocated() && unsafe { self.as_allocated_unchecked() }.owner.is_thin()
    }

    /// Returns a pointer to the first element of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::HipVec;
    /// let a: HipVec<u8> = HipVec::from([1, 2, 3]);
    /// assert_eq!(unsafe { *a.as_ptr() }, 1);
    /// ```
    #[must_use]
    pub const fn as_ptr(&self) -> *const T {
        if self.is_inline() {
            unsafe { self.as_inline_unchecked() }.as_ptr()
        } else {
            unsafe { self.as_sliced_unchecked() }.as_ptr()
        }
    }

    /// Returns the number of elements in the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::HipVec;
    ///
    /// let a: HipVec<u8> = HipVec::from([1, 2, 3]);
    /// assert_eq!(a.len(), 3);
    ///
    /// let b: HipVec<u8> = HipVec::new();
    /// assert_eq!(b.len(), 0);
    ///
    /// let c: HipVec<u8> = HipVec::from([0; 1024]);
    /// assert_eq!(c.len(), 1024);
    /// ```
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
    ///
    /// let a: HipVec<u8> = HipVec::new();
    /// assert!(a.is_empty());
    ///
    /// let b: HipVec<u8> = HipVec::from([1, 2, 3]);
    /// assert!(!b.is_empty());
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns a slice of the vector's contents.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::HipVec;
    ///
    /// let a: HipVec<u8> = HipVec::from([1, 2, 3]);
    /// assert_eq!(a.as_slice(), &[1, 2, 3]);
    ///
    /// let b: HipVec<u8> = HipVec::new();
    /// assert_eq!(b.as_slice(), &[]);
    /// ```
    #[must_use]
    #[inline]
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
    #[inline]
    const unsafe fn as_inline_unchecked(&self) -> &InlineVec<T, Bytes> {
        debug_assert!(self.is_inline());
        // SAFETY: precondition
        unsafe { &*ptr::from_ref(self).cast() }
    }

    /// Gets a mutable reference to the underlying inline representation.
    ///
    /// # Safety
    ///
    /// The vector must be inline.
    #[inline]
    const unsafe fn as_mut_inline_unchecked(&mut self) -> &mut InlineVec<T, Bytes> {
        debug_assert!(self.is_inline());
        // SAFETY: precondition
        unsafe { &mut *ptr::from_mut(self).cast() }
    }

    /// Gets a reference to the underlying sliced representation.
    ///
    /// # Safety
    ///
    /// The vector must not be inline.
    #[inline]
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
    #[inline]
    const unsafe fn as_mut_sliced_unchecked(&mut self) -> &mut UnknownSliced<T> {
        debug_assert!(!self.is_inline());
        // SAFETY: precondition
        unsafe { &mut *ptr::from_mut(self).cast() }
    }

    /// Gets a reference to the underlying allocated representation.
    ///
    /// # Safety
    ///
    /// The vector must be allocated.
    #[inline]
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
    #[inline]
    const unsafe fn as_mut_allocated_unchecked(&mut self) -> &mut Allocated<T, B> {
        debug_assert!(self.is_allocated());
        // SAFETY: precondition
        unsafe { &mut *ptr::from_mut(self).cast() }
    }

    #[inline]
    const unsafe fn into_allocated_unchecked(self) -> Allocated<T, B> {
        debug_assert!(self.is_allocated());
        // SAFETY: precondition
        unsafe { transmute::<Self, Allocated<T, B>>(self) }
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

        if const { Bytes::USIZE == L::USIZE } {
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
            unsafe { force_transmute::<InlineVec<T, Bytes>, Self>(new) }
        }
    }

    /// Creates a `HipVec` from a slice by cloning the elements.
    #[must_use]
    pub(crate) fn from_slice_clone(slice: &[T]) -> Self
    where
        T: Clone,
    {
        if slice.is_empty() {
            Self::DEFAULT
        } else if slice.len() <= Self::INLINE_CAP {
            let inline = Inline::from_slice_clone(slice);
            Self::from_inline(inline)
        } else {
            let smart = SmartThinVec::from_slice_clone(slice);
            Self::from_smart_thin(smart)
        }
    }

    #[must_use]
    pub fn from_slice_copy(slice: &[T]) -> Self
    where
        T: Copy,
    {
        if slice.is_empty() {
            Self::DEFAULT
        } else if slice.len() <= Self::INLINE_CAP {
            let inline = Inline::from_slice_copy(slice);
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
        unsafe { &mut self.as_mut_allocated_unchecked().owner }
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
        if range.is_empty() {
            Self::DEFAULT
        } else if Self::MAY_INLINE && range.len() < Self::INLINE_CAP {
            let inline = Inline::from_slice_clone(&self.as_slice()[range]);
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
                let copy = copy.as_mut_sliced_unchecked();
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
            let inline = unsafe { self.as_mut_inline_unchecked() };
            inline.pop()
        } else if self.is_empty() {
            None
        } else {
            if self.is_allocated() {
                // SAFETY: repr is checked above
                let allocated = unsafe { self.as_mut_allocated_unchecked() };
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
                        owner.set_len(actual_len - 1);

                        // move the last element out
                        let value = ptr.add(actual_len - 1).read();

                        // reduce the slice
                        allocated.len -= 1;

                        return Some(value);
                    }
                }
            }

            // not unique => we clone the last value and update the length

            // SAFETY: not inlined
            let sliced = unsafe { self.as_mut_sliced_unchecked() };

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
            let allocated = unsafe { self.as_mut_allocated_unchecked() };
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
            let allocated = unsafe { self.as_mut_allocated_unchecked() };
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
            let inline = unsafe { self.as_mut_inline_unchecked() };
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
                self.as_mut_sliced_unchecked().len = at;
            }

            // SAFETY: same repr for other
            unsafe {
                // set the slice for the other vector
                let other = other.as_mut_sliced_unchecked();
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
            let inline = unsafe { self.as_mut_inline_unchecked() };
            inline.truncate(len);
        } else {
            let sliced = unsafe { self.as_mut_sliced_unchecked() };
            sliced.len = len;
        }
    }

    pub fn mutate(&mut self) -> RefMut<'_, 'a, T, B>
    where
        T: Clone,
    {
        // ensures self is owned uniquely
        self.detach();
        // ensures self is tightened and starts at index 0
        self.tighten_and_shift();
        // SAFETY: self is now unique and starts at index 0
        unsafe { RefMut::new(self) }
    }
}

impl<T, B: Backend> Drop for HipVec<'_, T, B> {
    fn drop(&mut self) {
        if self.is_inline() {
            if needs_drop::<T>() {
                // SAFETY: repr checked above
                let inline = unsafe { self.as_mut_inline_unchecked() };
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

/// A mutable reference to a `HipVec`.
pub struct RefMut<'a, 'b, T, B: Backend>(&'a mut HipVec<'b, T, B>);

impl<'a, 'b, T, B: Backend> RefMut<'a, 'b, T, B> {
    #[must_use]
    unsafe fn new(origin: &'a mut HipVec<'b, T, B>) -> Self {
        #[cfg(debug_assertions)]
        if origin.is_allocated() {
            let allocated = unsafe { origin.as_allocated_unchecked() };
            assert_eq!(allocated.owner.data().as_ptr().cast_const(), allocated.ptr);
            assert_eq!(allocated.owner.len(), allocated.len);
        } else {
            assert!(origin.is_inline());
        }

        Self(origin)
    }

    #[must_use]
    pub const fn capacity(&self) -> usize {
        if self.0.is_inline() {
            unsafe { self.0.as_inline_unchecked() }.capacity()
        } else if self.0.is_allocated() {
            unsafe { self.0.as_allocated_unchecked() }.owner.capacity()
        } else {
            unreachable!();
        }
    }

    #[must_use]
    pub const fn len(&self) -> usize {
        if self.0.is_inline() {
            unsafe { self.0.as_inline_unchecked() }.len()
        } else if self.0.is_allocated() {
            unsafe { self.0.as_allocated_unchecked() }.owner.len()
        } else {
            unreachable!();
        }
    }

    #[must_use]
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub const unsafe fn set_len(&mut self, new_len: usize) {
        if self.0.is_inline() {
            let inline = unsafe { self.0.as_mut_inline_unchecked() };
            unsafe {
                inline.set_len(new_len);
            }
        } else if self.0.is_allocated() {
            let allocated = unsafe { self.0.as_mut_allocated_unchecked() };
            unsafe {
                allocated.owner.set_len(new_len);
            }
        } else {
            unreachable!();
        }
    }

    #[must_use]
    pub const fn as_ptr(&self) -> *const T {
        if self.0.is_inline() {
            unsafe { self.0.as_inline_unchecked() }.as_ptr()
        } else if self.0.is_allocated() {
            unsafe { self.0.as_allocated_unchecked() }
                .owner
                .data()
                .as_ptr()
        } else {
            unreachable!();
        }
    }

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
            unreachable!();
        }
    }

    #[must_use]
    #[inline]
    pub const fn as_slice(&self) -> &[T] {
        unsafe { core::slice::from_raw_parts(self.as_ptr(), self.len()) }
    }

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
        if additional >= cap - len {
            let required = self
                .len()
                .checked_add(additional)
                .expect("capacity overflow");
            let new_cap = required.max(cap * 2);
            unsafe {
                self.set_capacity(new_cap);
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
        let cap = self.capacity();

        debug_assert!(new_cap >= len);

        if cap == new_cap {
            return;
        }

        if self.0.is_inline() {
            // SAFETY: repr is checked above
            let owner = unsafe { self.0.as_mut_inline_unchecked() };
            let mut thin = ThinVec::<T, B>::with_capacity(new_cap);

            // SAFETY: capacity ≥ new length by `reserve`
            unsafe {
                owner.set_len(0);
                thin.as_mut_ptr()
                    .copy_from_nonoverlapping(owner.as_ptr(), len.min(new_cap));
                thin.set_len(len);
            }

            // SAFETY: thin vec with the default prefix
            let smart_thin: SmartThinVec<T, B> =
                unsafe { SmartThinVec::from_thin_vec_unchecked(thin) };

            // update the whole origin
            let old = mem::replace(self.0, HipVec::from_smart_thin(smart_thin));

            debug_assert!(self.0.is_thin());

            mem::forget(old); // old is inline and now empty, it can be forgotten
        } else if self.0.is_wide() {
            let old = mem::replace(self.0, HipVec::DEFAULT);
            // SAFETY: repr is checked above
            let allocated = unsafe { old.into_allocated_unchecked() };
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
            mem::forget(old); // old is empty, it can be forgotten
        } else {
            // SAFETY: repr is checked above
            let allocated = unsafe { self.0.as_mut_allocated_unchecked() };

            // SAFETY: repr is checked above (thin) and unique
            let ref_mut = unsafe { allocated.owner.as_mut_thin_vec() };

            // SAFETY: new capacity >= len by precondition
            unsafe {
                ref_mut.set_capacity(new_cap);
            }
        }
    }

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
            unreachable!("ref mut cannot be borrowed");
        }
    }
}
