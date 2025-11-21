//! Hip vector and related types.
//!
//! Hip vectors are vectors that can store their data in three different ways:
//! - inline (i.e., within the vector structure itself),
//! - a copy-on-write shared heap allocation (thin or fat),
//! - a borrowed slice.
//!
//! This design allows for efficient storage and manipulation of small vectors
//! while still providing the flexibility to handle larger vectors without
//! unnecessary heap allocations.
//!
//! # Examples
//!
//! ```
//! use hipstr::vecs::HipVec;
//! let h: HipVec<Box<i32>> = HipVec::from([1, 2, 3].map(Box::new));
//! let h2 = h.clone();
//! assert!(std::ptr::eq(h.as_slice(), h2.as_slice()));
//! ```

use alloc::vec::Vec;
use core::marker::PhantomData;
use core::mem::{transmute, ManuallyDrop, MaybeUninit};
use core::ops::{Range, RangeBounds};
use core::{ptr, slice};

use const_default::ConstDefault;
use rules_derive::rules_derive;
use typenum::Unsigned;

pub use self::mutate::RefMut;
use self::repr::{
    check_wide_and_thin_compatibility, Allocated, Borrowed, Pivot, Sliced, UnknownSliced,
};
use crate::backend::UpdateResult;
use crate::common::derives::{
    AsRef, ConstDefault, Copy, DelegateDebug, DelegateHash, Deref, From, Vector,
};
use crate::common::traits::Mutate;
use crate::common::{
    self, drop_raw_slice, force_transmute, range_of, unwrap_display, unwrap_unchecked_display,
    RangeError,
};
use crate::vecs::inline::{InlineLength, InlineVec};
use crate::vecs::thin::{can_reuse, SmartThinVec, ThinVec};
use crate::vecs::wide::{SmartWideVec, WideVec};
use crate::Backend;

pub(crate) mod mutate;
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
    From(WideVec<T, P>, Self::from_wide_vec, (P: ConstDefault)),
    From(&[T], Self::from_slice_clone, () where (T: Clone)),
    From(&[T; N], Self::from_slice_clone, (const N: usize) where (T: Clone)),
    From(InlineVec<T, L>, Self::from_inline, (L: InlineLength)),
    DelegateDebug(Self::as_slice where T: core::fmt::Debug),
    DelegateHash(Self::as_slice where T: core::hash::Hash),
    Vector(T),
)]
pub struct HipVec<'a, T, B: Backend>(Pivot, PhantomData<(B, &'a [T])>);

unsafe impl<T: Sync, B: Backend + Sync> Sync for HipVec<'_, T, B> {}
unsafe impl<T: Send, B: Backend + Send> Send for HipVec<'_, T, B> {}

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

    pub(crate) const fn fit_inline(len: usize) -> bool {
        len <= Self::INLINE_CAP
    }

    /// Checks if this hip vector is valid, constly
    const fn const_is_valid(&self) -> bool {
        (self.is_inline() ^ self.is_borrowed() ^ self.is_allocated())
            && if self.is_allocated() {
                let allocated = unsafe { self.as_allocated_unchecked() };
                allocated.owner.len() >= allocated.len && !allocated.ptr.is_null()
            } else {
                true
            }
    }

    /// Checks if this hip vector is valid.
    fn is_valid(&self) -> bool {
        (self.is_inline() ^ self.is_borrowed() ^ self.is_allocated())
            && if self.is_allocated() {
                let allocated = unsafe { self.as_allocated_unchecked() };
                let start = allocated.ptr;
                let end = start.wrapping_add(allocated.len);
                let owner_start = allocated.owner.data().as_ptr().cast_const();
                let owner_end = owner_start.wrapping_add(allocated.owner.len());
                owner_start <= start && start <= end && end <= owner_end
            } else {
                true
            }
    }

    /// Creates a new empty hip vector.
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

    /// Creates a `HipVec` with the specified capacity.
    ///
    /// The created vector will have a length of 0.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::HipVec;
    /// let a: HipVec<u8> = HipVec::with_capacity(10);
    /// assert_eq!(a.len(), 0);
    /// assert!(a.capacity() >= 10);
    /// ```
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        if capacity == 0 {
            Self::new()
        } else if Self::fit_inline(capacity) {
            let inline = Inline::with_capacity(capacity);
            Self::from_inline(inline)
        } else {
            let smart = SmartThinVec::with_capacity(capacity);
            Self::from_smart_thin(smart)
        }
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

    pub const fn inline_copy(slice: &[T]) -> Self
    where
        T: Copy,
    {
        let inline = Inline::from_slice_copy(slice);
        Self::from_inline(inline)
    }

    pub const fn try_inline_copy(slice: &[T]) -> Option<Self>
    where
        T: Copy,
    {
        if Self::fit_inline(slice.len()) {
            Some(Self::inline_copy(slice))
        } else {
            None
        }
    }

    pub const fn inline_array<const N: usize>(array: [T; N]) -> Self {
        let inline = Inline::from_array(array);
        Self::from_inline(inline)
    }

    pub(crate) const fn inline_empty() -> Self {
        let inline = Inline::new();
        Self::from_inline(inline)
    }

    /// Converts the vector into a borrowed slice without checking the representation.
    ///
    /// # Safety
    ///
    /// The vector must be in the borrowed representation.
    pub(crate) const unsafe fn into_borrowed_unchecked(self) -> &'a [T] {
        debug_assert!(self.is_borrowed(), "vector should be borrowed");
        let sliced = unsafe { self.as_sliced_unchecked() };
        let slice = unsafe { core::slice::from_raw_parts(sliced.ptr, sliced.len) };
        core::mem::forget(self);
        slice
    }

    /// Converts the vector into a borrowed slice if it is in the borrowed representation.
    ///
    /// # Errors
    ///
    /// Returns `Err(self)` if the vector is not borrowed.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::HipVec;
    /// let slice: &[u8] = &[1, 2, 3];
    /// let a: HipVec<u8> = HipVec::borrowed(slice);
    /// let b = a.into_borrowed().unwrap();
    /// assert_eq!(b, slice);
    /// ```
    pub const fn into_borrowed(self) -> Result<&'a [T], Self> {
        if self.is_borrowed() {
            // SAFETY: representation is checked above
            Ok(unsafe { self.into_borrowed_unchecked() })
        } else {
            Err(self)
        }
    }

    /// Returns the borrowed slice if the vector is in the borrowed
    /// representation, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::HipVec;
    /// let slice: &[u8] = &[1, 2, 3];
    /// let a: HipVec<u8> = HipVec::borrowed(slice);
    /// let b = a.as_borrowed().unwrap();
    /// assert_eq!(b, slice);
    /// ```
    pub const fn as_borrowed(&self) -> Option<&'a [T]> {
        if self.is_borrowed() {
            // SAFETY: representation checked above
            let sliced = unsafe { self.as_sliced_unchecked() };
            // SAFETY: type invariant of this representation
            let slice = unsafe { slice::from_raw_parts(sliced.ptr, sliced.len) };
            Some(slice)
        } else {
            None
        }
    }

    /// Creates a `HipVec` from an array.
    #[must_use]
    #[inline]
    pub(crate) fn from_array<const N: usize>(array: [T; N]) -> Self {
        if const { N == 0 } {
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
    pub(crate) fn from_vec(vec: Vec<T>) -> Self {
        Self::from_smart_wide_vec(SmartWideVec::from_vec(vec))
    }

    #[must_use]
    pub(crate) fn from_vec_normalized(vec: Vec<T>) -> Self {
        if vec.is_empty() {
            Self::DEFAULT
        } else if Self::fit_inline(vec.len()) {
            let inline = Inline::from_vector(vec);
            Self::from_inline(inline)
        } else {
            Self::from_smart_wide_vec(SmartWideVec::from_vec(vec))
        }
    }

    /// Creates a `HipVec` from a `SmartWideVec`.
    #[must_use]
    pub(crate) fn from_smart_wide_vec(vec: SmartWideVec<T, B>) -> Self {
        let sliced = Sliced {
            ptr: vec.as_ptr(),
            len: vec.len(),
            owner: vec, // the cast is not necessary SmartWideVec is transparent
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

    #[must_use]
    #[inline]
    pub(crate) fn from_wide_vec<P: ConstDefault>(v: WideVec<T, P>) -> Self {
        Self::from_smart_wide_vec(SmartWideVec::from_wide_vec(v))
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

        let result = if const { Bytes::USIZE == L::USIZE } {
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
        };
        debug_assert!(result.const_is_valid());
        result
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

    /// Creates a `HipVec` from a slice by copying the elements.
    ///
    /// Provided as an optimization over `HipVec::from` for types that implement `Copy`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::HipVec;
    /// let slice: &[u8] = &[1, 2, 3];
    /// let a: HipVec<u8> = HipVec::from_slice_copy(slice);
    /// assert_eq!(a.as_slice(), slice);
    /// ```
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
    pub(crate) const fn from_smart_thin(v: SmartThinVec<T, B>) -> Self {
        let len = v.len();
        let ptr = v.as_ptr();

        #[cfg(debug_assertions)]
        let is_null = v.capacity() == 0;

        let owner = v;
        let this =
            unsafe { transmute::<Sliced<T, SmartThinVec<T, B>>, Self>(Sliced { owner, ptr, len }) };

        debug_assert!(if is_null {
            this.is_borrowed()
        } else {
            this.is_allocated()
        });
        debug_assert!(this.const_is_valid());

        this
    }

    /// Returns `true` if the vector is the normalized empty vector, i.e., for
    /// now, borrowed and empty.
    pub(crate) const fn is_nil(&self) -> bool {
        self.0.is_borrowed() && self.len() == 0
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
            || self.is_nil()
    }

    pub(crate) fn is_trimmed(&self) -> bool {
        if self.is_allocated() {
            let allocated = unsafe { self.as_allocated_unchecked() };
            allocated.ptr == allocated.owner.data().as_ptr()
                && allocated.len == allocated.owner.len()
        } else {
            true
        }
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

    #[must_use]
    pub fn as_mut_ptr(&mut self) -> Option<*mut T> {
        if self.is_unique() {
            Some(unsafe { self.as_mut_ptr_unchecked() })
        } else {
            None
        }
    }

    #[must_use]
    pub unsafe fn as_mut_ptr_unchecked(&mut self) -> *mut T {
        debug_assert!(self.is_unique(), "vector must be uniquely owned");
        if self.is_inline() {
            unsafe { self.as_mut_inline_unchecked() }.as_mut_ptr()
        } else {
            unsafe { self.as_mut_sliced_unchecked() }.ptr.cast_mut()
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

    /// Returns the capacity of the vector.
    ///
    /// Depending on the representation, the meaning of capacity varies:
    ///
    /// - for inline vectors, this is the maximum number of elements that can be
    ///   stored inline,
    /// - for allocated vectors, this is the capacity of the underlying
    ///   allocation,
    /// - for borrowed vectors, this is the length of the slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::HipVec;
    ///
    /// let a = HipVec::from([1, 2, 3]);
    /// assert_eq!(a.capacity(), HipVec::<i32>::INLINE_CAP);
    ///
    /// let b = HipVec::from(Vec::with_capacity(100));
    /// assert_eq!(b.capacity() >= 100);
    /// ```
    #[must_use]
    pub const fn capacity(&self) -> usize {
        if self.is_inline() {
            unsafe { self.as_inline_unchecked() }.capacity()
        } else if self.is_allocated() {
            unsafe { self.as_allocated_unchecked() }.owner.capacity()
        } else {
            self.len()
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

    /// Extracts a mutable slice of the entire vector if possible.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::vecs::HipVec;
    /// let mut s = HipVec::from(b"foo");
    /// let slice = s.as_mut_slice().unwrap();
    /// slice.copy_from_slice(b"bar");
    /// assert_eq!(b"bar", slice);
    /// ```
    #[inline]
    pub fn as_mut_slice(&mut self) -> Option<&mut [T]> {
        if self.is_unique() {
            Some(unsafe { self.as_mut_slice_unchecked() })
        } else {
            None
        }
    }

    /// Extracts a mutable slice of the entire vector.
    ///
    /// # Safety
    ///
    /// This vector should be shared or borrowed.
    ///
    /// # Panics
    ///
    /// In debug mode, panics if the sequence is not uniquely owned.
    #[inline]
    pub unsafe fn as_mut_slice_unchecked(&mut self) -> &mut [T] {
        debug_assert!(self.is_unique(), "vector must be uniquely owned");
        // SAFETY: ptr is unique
        unsafe {
            let ptr = self.as_mut_ptr_unchecked();
            core::slice::from_raw_parts_mut(ptr, self.len())
        }
    }

    /// Extracts a mutable slice of the entire vector changing the
    /// representation if needed.
    ///
    /// The representation is changed to be uniquely owned.
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::vecs::HipVec;
    /// let mut s = HipVec::borrowed(b"foo");
    /// let slice = s.to_mut_slice();
    /// slice.copy_from_slice(b"bar");
    /// assert_eq!(b"bar", slice);
    /// assert!(s.is_inline());
    /// ```
    #[inline]
    pub fn to_mut_slice(&mut self) -> &mut [T]
    where
        T: Clone,
    {
        self.detach();
        // SAFETY: `detach` above ensures that it is uniquely owned
        unsafe { self.as_mut_slice_unchecked() }
    }

    /// Extracts a mutable slice of the entire vector changing the
    /// representation if needed.
    ///
    /// The representation is changed to be uniquely owned.
    ///
    /// This function is specialized for `T: Copy`. See [`to_mut_slice`] for the
    /// more general function.
    ///
    /// [`to_mut_slice`]: Self::to_mut_slice
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::vecs::HipVec;
    /// let mut s = HipVec::borrowed(b"foo");
    /// let slice = s.to_mut_slice_copy();
    /// slice.copy_from_slice(b"bar");
    /// assert_eq!(b"bar", slice);
    /// assert!(s.is_inline());
    /// ```
    #[inline]
    pub fn to_mut_slice_copy(&mut self) -> &mut [T]
    where
        T: Copy,
    {
        self.detach_copy();
        // SAFETY: `detach_copy` above ensures that it is uniquely owned
        unsafe { self.as_mut_slice_unchecked() }
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

    #[inline]
    const unsafe fn into_inline_unchecked(self) -> InlineVec<T, Bytes> {
        debug_assert!(self.is_inline());
        // SAFETY: precondition
        unsafe { force_transmute::<Self, InlineVec<T, Bytes>>(self) }
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

    /// Moves to the allocated representation.
    ///
    /// # Safety
    ///
    /// The vector must be allocated and unique.
    #[inline]
    const unsafe fn into_allocated_unchecked(self) -> Allocated<T, B> {
        debug_assert!(self.is_allocated());
        // SAFETY: precondition
        unsafe { transmute::<Self, Allocated<T, B>>(self) }
    }

    /// Bitwise copies the vector.
    ///
    /// # Safety
    ///
    /// The vector must be copyable:
    ///
    /// - A borrowed vector is copyable
    /// - An inline vector of Copy elements is copyable
    /// - A shared vector is copyiable if the counter has already been increased.
    const unsafe fn copy(&self) -> Self {
        Self(self.0, PhantomData)
    }

    /// Ensures the vector is uniquely owned, cloning the elements if necessary.
    ///
    /// After calling this method, it is guaranteed that [`is_unique`] returns
    /// `true`.
    ///
    /// If the vector is already unique, this method does nothing.
    /// Otherwise, the elements are cloned to a new **normalized** vector.
    ///
    /// See [`detach_copy`] for an optimized version for types that implement
    /// `Copy`.
    ///
    /// [`is_unique`]: Self::is_unique
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::HipVec;
    /// let mut hip = HipVec::from([1, 2, 3]);
    /// let hip2 = hip.clone();
    /// assert!(!hip.is_unique());
    /// hip.detach();
    /// assert!(hip.is_unique());
    /// ```
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

    /// Ensures the vector is uniquely owned, copying the elements if necessary.
    ///
    /// After calling this method, it is guaranteed that [`is_unique()`] returns
    /// `true`.
    ///
    /// If the vector is already unique, this method does nothing.
    /// Otherwise, the elements are copied to a new **normalized** vector.
    ///
    /// Functionally equivalent to [`detach`], this function is provided as an
    /// optimization for types that implement `Copy`.
    ///
    /// [`Self::is_unique()`]: Self::is_unique
    /// [`detach`]: Self::detach
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::HipVec;
    /// let mut hip = HipVec::from([1, 2, 3]);
    /// let hip2 = hip.clone();
    /// assert!(!hip.is_unique());
    /// hip.detach_copy();
    /// assert!(hip.is_unique());
    /// ```
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
        unwrap_display(self.try_slice(range))
    }

    /// Returns a slice of the vector without checking the range.
    ///
    /// # Panics
    ///
    /// In debug mode, this function panics if the range is out of bounds.
    ///
    /// # Safety
    ///
    /// The provided range must be valid for the vector.
    #[must_use]
    pub unsafe fn slice_unchecked(&self, range: impl RangeBounds<usize>) -> Self
    where
        T: Clone,
    {
        let range = common::range(range, self.len());
        let range = unwrap_unchecked_display(range);
        self.slice_range(range)
    }

    /// Returns a vector of a range of elements in this vector, if the range is
    /// valid.
    ///
    /// # Errors
    ///
    /// This function returns an error if the range is invalid.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::vecs::HipVec;
    /// let a = HipVec::from(b"abc");
    /// assert_eq!(a.try_slice(0..2), Ok(HipVec::from(b"ab")));
    /// assert!(a.try_slice(0..4).is_err());
    /// ```
    pub fn try_slice(&self, range: impl RangeBounds<usize>) -> Result<Self, RangeError>
    where
        T: Clone,
    {
        let range = common::range(range, self.len())?;
        Ok(self.slice_range(range))
    }

    /// Returns a slice of the vector given a valid range.
    fn slice_range(&self, range: Range<usize>) -> Self
    where
        T: Clone,
    {
        let this = if range.is_empty() {
            Self::DEFAULT
        } else if self.is_inline() {
            let slice = unsafe { self.as_inline_unchecked().as_slice().get_unchecked(range) };
            let inline = Inline::from_slice_clone(slice);
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
        };
        debug_assert!(this.is_valid());
        this
    }

    pub fn slice_ref_copy(&self, slice: &[T]) -> Option<Self>
    where
        T: Copy,
    {
        let _range = range_of(slice, self.as_slice())?;

        Some(if slice.is_empty() {
            Self::DEFAULT
        } else if self.is_inline() {
            let inline = Inline::from_slice_clone(slice);
            Self::from_inline(inline)
        } else {
            if self.is_allocated() {
                // SAFETY: repr is checked above
                let owner = unsafe { &self.as_allocated_unchecked().owner };
                if owner.counter().incr() == UpdateResult::Overflow {
                    return Some(Self::from_slice_copy(slice));
                }
            }

            unsafe {
                let mut result = self.copy();
                {
                    let sliced = result.as_mut_sliced_unchecked();
                    sliced.ptr = slice.as_ptr();
                    sliced.len = slice.len();
                }
                result
            }
        })
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
        let result = self._pop();
        debug_assert!(self.is_valid());
        result
    }

    #[inline]
    fn _pop(&mut self) -> Option<T>
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
                    let ptr = owner.as_mut_ptr();

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

    /// Appends an element to this vector.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::vecs::HipVec;
    /// let mut vec = HipVec::from([1, 2, 3]);
    /// vec.push(4);
    /// vec.push(5);
    /// vec.push(6);
    /// assert_eq!(vec.as_slice(), &[1, 2, 3, 4, 5, 6]);
    /// ```
    pub fn push(&mut self, value: T)
    where
        T: Clone,
    {
        self.mutate().push(value);
    }

    /// Appends an element to this vector.
    ///
    /// This function is a specialization of [`push`] for `T: Copy`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use hipstr::vecs::HipVec;
    /// let mut vec = HipVec::from([1, 2, 3]);
    /// vec.push_copy(4);
    /// vec.push_copy(5);
    /// vec.push_copy(6);
    /// assert_eq!(vec.as_slice(), &[1, 2, 3, 4, 5, 6]);
    /// ```
    pub fn push_copy(&mut self, value: T)
    where
        T: Copy,
    {
        self.mutate_copy().push(value)
    }

    /// Clears the vector, removing all values.
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
    pub fn right_trim(&mut self) {
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

                    // update the length
                    owner.set_len(actual_len);

                    // drop the remaining elements
                    drop_raw_slice(rem_ptr, rem_len);
                    // beware: drop after updating the length, to avoid
                    // double-drop if one element's drop panics
                    // TODO add test for this case?
                }
            }
        }
    }

    pub fn trim(&mut self) {
        if self.is_allocated() {
            // SAFETY: repr is checked above
            let allocated = unsafe { self.as_mut_allocated_unchecked() };
            let owner = &mut allocated.owner;
            if owner.is_unique() {
                let ptr = owner.data().as_ptr();
                let owner_len = owner.len();
                let shift = unsafe { allocated.ptr.offset_from_unsigned(ptr) };

                // SAFETY: the slice is inside the owner's buffer by type
                // invariant
                unsafe {
                    // temporarily set the length to zero to prevent double drop if a drop panics
                    owner.set_len(0);
                }

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
                debug_assert!(
                    owner_len >= excess_start,
                    "end of slice should be in bounds"
                );
                let excess_len = owner_len - excess_start;

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
                allocated.ptr = ptr;
            }
        }
        debug_assert!(
            self.is_valid(),
            "tighten_and_shift must return a valid vector"
        );
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
                let owner = unsafe { &mut self.as_mut_allocated_unchecked().owner };
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
        if len < self.len() {
            if self.is_inline() {
                // SAFETY: repr checked above
                let inline = unsafe { self.as_mut_inline_unchecked() };
                inline.truncate(len);
            } else {
                let sliced = unsafe { self.as_mut_sliced_unchecked() };
                sliced.len = len;
            }
        }
        debug_assert!(self.is_valid());
    }

    /// Returns a mutable view of this vector.
    ///
    /// This operation may reallocate a new vector if either:
    ///
    /// - the representation is not _allocated_ (i.e. _inline_ or _borrowed_),
    /// - the underlying buffer is shared.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hipstr::vecs::HipVec;
    /// let mut s = HipVec::borrowed(b"abc");
    /// {
    ///     let mut r = s.mutate();
    ///     r.extend_from_slice(b"def");
    ///     assert_eq!(r.as_slice(), b"abcdef");
    /// }
    /// assert_eq!(s.as_slice(), b"abcdef");
    /// ```
    pub fn mutate(&mut self) -> RefMut<'_, 'a, T, B>
    where
        T: Clone,
    {
        // ensures self is owned uniquely
        self.detach();
        // ensures self is trimmed
        self.trim();
        // SAFETY: self is now unique and trimmed
        unsafe { RefMut::new(self) }
    }

    /// Returns a mutable view of this vector.
    ///
    /// This operation may reallocate a new vector if either:
    ///
    /// - the representation is not _allocated_ (i.e. _inline_ or _borrowed_),
    /// - the underlying buffer is shared.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hipstr::vecs::HipVec;
    /// let mut s = HipVec::borrowed(b"abc");
    /// {
    ///     let mut r = s.mutate_copy();
    ///     r.extend_from_slice_copy(b"def");
    ///     assert_eq!(r.as_slice(), b"abcdef");
    /// }
    /// assert_eq!(s.as_slice(), b"abcdef");
    /// ```
    pub fn mutate_copy(&mut self) -> RefMut<'_, 'a, T, B>
    where
        T: Copy,
    {
        // ensures self is owned uniquely
        self.detach_copy();
        // ensures self is tightened and starts at index 0
        self.trim();
        // SAFETY: self is now unique and starts at index 0
        unsafe { RefMut::new(self) }
    }

    /// Returns a mutable view of this vector.
    ///
    /// # Safety
    ///
    /// The vector must be either the normal empty vector or a unique allocated
    /// vector.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hipstr::vecs::HipVec;
    /// let mut s = HipVec::borrowed(b"abc");
    /// {
    ///     let mut r = s.mutate_copy();
    ///     r.extend_from_slice_copy(b"def");
    ///     assert_eq!(r.as_slice(), b"abcdef");
    /// }
    /// assert_eq!(s.as_slice(), b"abcdef");
    /// ```
    pub(crate) unsafe fn mutate_unchecked(&mut self) -> RefMut<'_, 'a, T, B> {
        debug_assert!(self.is_unique());
        debug_assert!(self.is_trimmed());
        // SAFETY: preconditions above
        unsafe { RefMut::new(self) }
    }

    #[must_use]
    pub fn repeat_copy(&self, n: usize) -> Self
    where
        T: Copy,
    {
        if self.is_empty() {
            return Self::new();
        } else if n == 1 {
            // TODO clone copy
            return self.clone();
        }

        let src_len = self.len();
        let new_len = src_len.checked_mul(n).expect("capacity overflow");
        let mut result = Self::with_capacity(new_len);

        let src = self.as_ptr();
        // SAFETY: vec is unique
        let mut dst = unsafe { result.as_mut_ptr_unchecked() };

        // SAFETY: copy new_len bytes
        unsafe {
            // could be better from an algorithmic standpoint
            for _ in 0..n {
                ptr::copy_nonoverlapping(src, dst, src_len);
                dst = dst.add(src_len);
            }
            result.set_len(new_len);
        }

        result
    }

    /// Sets the length of the vector.
    ///
    /// # Safety
    ///
    /// The new length must be less than or equal to the capacity of the vector.
    ///
    /// If the new length is greater than the current length:
    /// - the vector must be uniquely owned,
    /// - the elements between the old length and the new length must be properly initialized.
    ///
    /// If the new length is less than the current length and the vector is inline,
    /// the elements between the new length and the old length will not be dropped.
    pub unsafe fn set_len(&mut self, new_len: usize) {
        if self.is_inline() {
            unsafe {
                self.as_mut_inline_unchecked().set_len(new_len);
            }
        } else {
            let is_allocated = self.is_allocated();
            let sliced = unsafe { self.as_mut_sliced_unchecked() };
            let len = sliced.len;

            if len >= new_len {
                sliced.len = new_len;
            } else {
                debug_assert!(is_allocated, "cannot increase length of borrowed slice");

                if is_allocated {
                    let allocated = unsafe { self.as_mut_allocated_unchecked() };
                    debug_assert!(
                        allocated.owner.is_unique(),
                        "cannot increase length of non-unique allocated vector"
                    );
                    let start = unsafe {
                        allocated
                            .ptr
                            .offset_from_unsigned(allocated.owner.data().as_ptr())
                    };
                    let expected_owner_len = start + len;
                    let owner_new_len = start + new_len;
                    debug_assert!(
                        allocated.owner.len() == expected_owner_len,
                        "the owner length is inconsistent with the slice"
                    );
                    debug_assert!(
                        owner_new_len <= allocated.owner.capacity(),
                        "new length exceeds capacity"
                    );
                    unsafe {
                        allocated.owner.set_len(owner_new_len);
                    }
                    allocated.len = new_len;
                }
            }
        }
    }

    pub fn spare_capacity_mut(&mut self) -> &mut [MaybeUninit<T>] {
        if self.is_unique() {
            if self.is_inline() {
                let inline = unsafe { self.as_mut_inline_unchecked() };
                inline.spare_capacity_mut()
            } else {
                self.right_trim();

                let allocated = unsafe { self.as_mut_allocated_unchecked() };
                let owner = &mut allocated.owner;
                let len = owner.len();
                let cap = owner.capacity();
                let ptr = owner.data_mut().as_ptr();

                let spare = cap - len;
                unsafe { core::slice::from_raw_parts_mut(ptr.add(len).cast(), spare) }
            }
        } else {
            &mut []
        }
    }

    pub fn shrink_to(&mut self, cap: usize)
    where
        T: Clone,
    {
        if cap >= self.len() && cap < self.capacity() {
            if self.is_unique() {
                self.trim();
                unsafe { self.mutate_unchecked() }.shrink_to(cap);
            } else {
                let mut new = Self::with_capacity(cap);
                unsafe { new.mutate_unchecked() }.extend_from_slice(self.as_slice());
                *self = new;
            }
        }
    }

    pub fn shrink_to_fit(&mut self)
    where
        T: Clone,
    {
        self.shrink_to(self.len());
    }

    pub fn extend_from_slice(&mut self, slice: &[T])
    where
        T: Clone,
    {
        if self.is_unique() {
            self.trim();

            // SAFETY: self is now unique and starts at index 0
            unsafe { RefMut::new(self) }.extend_from_slice(slice);
        } else {
            let mut new = Self::with_capacity(self.len() + slice.len());
            {
                let mut mutable = unsafe { RefMut::new(&mut new) };
                mutable.extend_from_slice(self.as_slice());
                mutable.extend_from_slice(slice);
            }
            *self = new;
        }
    }

    pub fn extend_from_slice_copy(&mut self, slice: &[T])
    where
        T: Copy,
    {
        // ensures self is owned uniquely
        if self.is_unique() {
            // ensures self is tightened and starts at index 0
            self.trim();

            // SAFETY: self is now unique and starts at index 0
            unsafe { RefMut::new(self) }.extend_from_slice_copy(slice);
        } else {
            let mut new = Self::with_capacity(self.len() + slice.len());
            {
                let mut mutable = unsafe { RefMut::new(&mut new) };
                mutable.extend_from_slice_copy(self.as_slice());
                mutable.extend_from_slice_copy(slice);
            }
            *self = new;
        }
    }

    /// Converts the `HipVec` into a standard `Vec<T>` without clone or allocation if possible.
    pub fn into_vec(self) -> Result<Vec<T>, Self> {
        if self.is_wide() && self.is_unique() {
            let allocated = unsafe { self.into_allocated_unchecked() };
            let mut vec = unsafe {
                allocated
                    .owner
                    .into_smart_wide_unchecked()
                    .into_vec_unchecked()
            };
            let slice_start = unsafe { allocated.ptr.offset_from_unsigned(vec.as_ptr()) };
            vec.drain(..slice_start);
            vec.truncate(allocated.len);

            Ok(vec)
        } else {
            Err(self)
        }
    }

    pub fn into_owned(self) -> HipVec<'static, T, B>
    where
        T: Clone,
    {
        if self.is_borrowed() {
            HipVec::from_slice_clone(self.as_slice())
        } else {
            let old = core::mem::ManuallyDrop::new(self);
            // SAFETY: old is not borrowed
            HipVec(old.0, PhantomData)
        }
    }
}

impl<T, B: Backend> Drop for HipVec<'_, T, B> {
    fn drop(&mut self) {
        if self.is_inline() {
            // SAFETY: repr checked above
            let inline = unsafe { self.as_mut_inline_unchecked() };
            // SAFETY: will no be used after drop
            unsafe {
                inline.drop_contents();
            }
        } else if self.is_allocated() {
            // SAFETY: repr checked above
            let owner = unsafe { &mut self.as_mut_allocated_unchecked().owner };
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
