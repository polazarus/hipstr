use alloc::vec::Vec;
use core::hint::unreachable_unchecked;
use core::marker::PhantomData;
use core::mem::ManuallyDrop;
use core::ops::RangeBounds;
use core::{panic, ptr};

use self::allocated::Allocated;
use self::inline::InlineVec;
pub use self::reprs::Tag;
use self::reprs::{Borrowed, Repr, Union};
use crate::backend::{
    Backend, BackendImpl, CloneOnOverflow, Counter, PanicOnOverflow, UpdateResult,
};
use crate::common::{self, RangeError};
use crate::smart::Smart;
use crate::vecs::hip::allocated::{Fat, Thin};
use crate::vecs::SmartThinVec;

mod allocated;
mod inline;
mod reprs;
#[cfg(test)]
mod tests;

const INLINE_BYTES: usize = size_of::<*mut ()>() * 3 - 1;

/// A hip vector is a vector that can be inline, thin, fat, or borrowed.
///
/// It is designed to optimize memory usage and performance:
///
/// - inline storage for small vectors
/// - borrowed representation to avoid allocation
/// - sharing (through [`Arc`] and [`Rc`] backends)
/// - reuse of existing “fat” [`Vec`] to avoid unnecessary copy
/// - thin vector to lower the overhead for new allocations
//  - and shared slices
pub struct HipVec<'borrow, T, B: Backend> {
    repr: Repr,
    _marker: PhantomData<&'borrow (T, B)>,
}

unsafe impl<T: Sync, B: Backend + Sync> Sync for HipVec<'_, T, B> {}

unsafe impl<T: Send, B: Backend + Send> Send for HipVec<'_, T, B> {}

type Inline<T> = InlineVec<T, INLINE_BYTES>;

impl<'borrow, T, B: Backend> HipVec<'borrow, T, B> {
    /// An empty `HipVec` constant.
    const EMPTY: Self = Self::from_inline(Inline::new());

    /// Creates a new empty `HipVec`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hipstr::vecs::HipVec;
    /// use hipstr::vecs::hip::Tag;
    /// use hipstr::Arc;
    /// let vec: HipVec<u8, Arc> = HipVec::new();
    /// assert!(vec.is_empty());
    /// assert!(matches!(vec.tag(), Tag::Inline | Tag::Borrowed));
    /// assert_eq!(vec.as_slice(), &[]);
    /// ```
    #[inline]
    pub const fn new() -> Self {
        Self::EMPTY
    }

    /// Creates a new inline vector from an array.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hipstr::vecs::HipVec;
    /// use hipstr::vecs::hip::Tag;
    ///
    /// let vec = HipVec::<u8, Arc>::inline([1, 2, 3]);
    /// assert_eq!(vec.tag(), Tag::Inline);
    /// assert_eq!(vec.as_slice(), [1, 2, 3]);
    /// ```
    pub const fn inline<const N: usize>(arr: [T; N]) -> Self {
        const {
            assert!(Self::fit_inline(N), "array too large for inline");
        }
        Self::from_inline(Inline::from_array(arr))
    }

    /// Creates a new `HipVec` from an array.
    /// If the array fits inline, it will be stored inline.
    /// Otherwise, it will be stored as a thin vector.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hipstr::vecs::HipVec;
    /// use hipstr::vecs::hip::Tag;
    /// use hipstr::Arc;
    /// let vec = HipVec::<u8, Arc>::from_array([1, 2, 3]);
    /// assert_eq!(vec.tag(), Tag::Inline);
    /// assert_eq!(vec.as_slice(), [1, 2, 3]);
    ///
    /// let vec = HipVec::<u8, Arc>::from_array([1; 40]);
    /// assert_eq!(vec.tag(), Tag::Thin);
    /// assert_eq!(vec.as_slice(), [1; 40]);
    /// ```
    #[inline]
    pub fn from_array<const N: usize>(arr: [T; N]) -> Self {
        if const { Self::fit_inline(N) } {
            Self::from_inline(Inline::from_array(arr))
        } else {
            let owner = SmartThinVec::from_array(arr);
            Self::from_thin(owner)
        }
    }

    #[inline]
    const fn from_union(union: reprs::Union<'borrow, T, B>) -> Self {
        Self {
            repr: unsafe { union.pivot },
            _marker: PhantomData,
        }
    }

    #[inline]
    pub fn from_vec(value: Vec<T>) -> Self {
        let owner = Smart::new(value);
        Self::from_fat(owner)
    }

    #[inline]
    fn from_fat(owner: Smart<Vec<T>, B>) -> Self {
        let ptr = owner.as_ptr();
        let len = owner.len();
        let fat = ManuallyDrop::new(Allocated::new(owner, ptr, len));
        let union = reprs::Union { fat };
        Self::from_union(union)
    }

    #[inline]
    fn from_thin(owner: SmartThinVec<T, B>) -> Self {
        let ptr = owner.as_ptr();
        let len = owner.len();
        let thin = ManuallyDrop::new(Allocated::new(owner, ptr, len));
        let union = reprs::Union { thin };
        Self::from_union(union)
    }

    #[inline]
    const fn from_inline(inline: Inline<T>) -> Self {
        assert!(Self::MAY_INLINE, "inline should be possible");
        Self {
            repr: unsafe { Repr::from_inline(inline) },
            _marker: PhantomData,
        }
    }

    /// Returns `true` if the vector is not shared currently.
    ///
    /// If the vector is inline, it is always unique.
    /// Conversely, if the vector is borrowed, it is never unique.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hipstr::vecs::HipVec;
    /// use hipstr::vecs::hip::Tag;
    /// use hipstr::Arc;
    /// let vec1 = HipVec::<u8, Arc>::from_array([1, 2, 3]);
    /// assert!(vec1.is_unique());
    ///
    /// let array = [1, 2, 3];
    /// let vec2 = HipVec::<u8, Arc>::borrowed(&array);
    /// assert!(!vec.is_unique());
    ///
    /// let vec3 = vec1.clone();
    /// assert!(!vec1.is_unique());
    /// assert!(!vec3.is_unique());
    /// ```
    #[inline]
    pub fn is_unique(&self) -> bool {
        match self.tag() {
            Tag::Borrowed => false,
            Tag::Inline => true,
            Tag::Thin | Tag::Fat => {
                unsafe { &self.repr.shared_view::<B>() }.with(Counter::is_unique)
            }
        }
    }

    /// Returns `true` if the vector is allocated on the heap.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hipstr::vecs::HipVec;
    /// use hipstr::Arc;
    /// let vec = HipVec::<u8, Arc>::from_array([1, 2, 3]);
    /// assert!(!vec.is_allocated());
    ///
    /// let vec = HipVec::<u8, Arc>::from_slice_clone(&[1, 2, 3]);
    /// assert!(vec.is_allocated());
    /// ```
    #[inline]
    pub const fn is_allocated(&self) -> bool {
        matches!(self.tag(), Tag::Thin | Tag::Fat)
    }

    /// Returns `true` if the vector is borrowed.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hipstr::vecs::HipVec;
    /// use hipstr::Arc;
    /// let vec = HipVec::<u8, Arc>::from_array([1, 2, 3]);
    /// assert!(!vec.is_borrowed());
    ///
    /// let array = [1, 2, 3];
    /// let vec = HipVec::<u8, Arc>::borrowed(&array);
    /// assert!(vec.is_borrowed());
    /// assert_eq!(vec.as_ptr(), array.as_ptr());
    /// ```
    pub const fn is_borrowed(&self) -> bool {
        matches!(self.tag(), Tag::Borrowed)
    }

    /// Returns `true` if the vector is inline.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hipstr::vecs::HipVec;
    /// use hipstr::Arc;
    /// let vec = HipVec::<u8, Arc>::from_array([1, 2, 3]);
    /// assert!(vec.is_inline());
    ///
    /// let vec = HipVec::<u8, Arc>::from_array([0; 1024]);
    /// assert!(!vec.is_inline());
    /// ```
    pub const fn is_inline(&self) -> bool {
        matches!(self.tag(), Tag::Inline)
    }

    /// Creates a new `HipVec` from a borrowed slice.
    ///
    /// # Examples
    /// /// ```rust
    /// use hipstr::vecs::HipVec;
    /// use hipstr::Arc;
    /// let array = [1, 2, 3];
    /// let vec = HipVec::<u8, Arc>::borrowed(&array);
    /// assert!(vec.is_borrowed());
    /// assert_eq!(&raw const *vec.as_slice(), &raw const *array.as_slice());
    /// ```
    #[inline]
    pub const fn borrowed(slice: &'borrow [T]) -> Self {
        let borrowed = Borrowed::new(slice);
        let union: Union<'borrow, T, B> = Union { borrowed };
        // SAFETY: the layout of `Pivot` matches the layout of `Borrowed`.
        // Type invariant ensures that the resulting repr
        // will only be manipulated as a borrowed repr.
        let pivot = unsafe { union.pivot };
        Self {
            repr: pivot,
            _marker: PhantomData,
        }
    }

    /// Returns a value identifying the current reprenstaiton of this vector.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hipstr::vecs::HipVec;
    /// use hipstr::vecs::hip::Tag;
    /// use hipstr::Arc;
    /// let vec = HipVec::<u8, Arc>::from_array([1, 2, 3]);
    /// assert_eq!(vec.tag(), Tag::Inline);
    ///
    /// let array = [1, 2, 3];
    /// let vec = HipVec::<u8, Arc>::borrowed(&array);
    /// assert_eq!(vec.tag(), Tag::Borrowed);
    /// ```
    pub const fn tag(&self) -> Tag {
        self.repr.repr()
    }

    /// Gets the borrowed slice.
    ///
    /// # Safety
    ///
    /// This function assumes that the vector is borrowed.
    #[inline]
    pub const unsafe fn as_borrowed_unchecked(&self) -> &'borrow [T] {
        // SAFETY: repr precondition
        let borrowed = unsafe { self.repr.borrowed() };
        borrowed.as_slice()
    }

    /// Gets the borrowed slice if the vector is borrowed.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hipstr::vecs::HipVec;
    /// use hipstr::Arc;
    /// let array = [1, 2, 3];
    /// let vec = HipVec::<u8, Arc>::borrowed(&array);
    /// assert_eq!(vec.as_borrowed(), Some(&array[..]));
    /// let vec = HipVec::<u8, Arc>::from_array([1, 2, 3]);
    /// assert_eq!(vec.as_borrowed(), None);
    /// ```
    #[inline]
    pub const fn as_borrowed(&self) -> Option<&'borrow [T]> {
        if let Tag::Borrowed = self.tag() {
            // SAFETY: repr is checked above
            let borrowed = unsafe { &self.repr.borrowed() };
            Some(borrowed.as_slice())
        } else {
            None
        }
    }

    const fn thin(&self) -> Option<&Thin<T, B>> {
        if let Tag::Thin = self.tag() {
            // SAFETY: the representaiton is checked
            Some(unsafe { self.repr.thin() })
        } else {
            None
        }
    }

    const fn fat(&self) -> Option<&Fat<T, B>> {
        if let Tag::Fat = self.tag() {
            // SAFETY: the representation is checked
            Some(unsafe { self.repr.fat() })
        } else {
            None
        }
    }

    const MAY_INLINE: bool = align_of::<T>() <= align_of::<Repr>() && Inline::<T>::CAP > 0;

    const fn fit_inline(len: usize) -> bool {
        Self::MAY_INLINE && len < Inline::<T>::CAP
    }

    /// Returns a slice of the vector.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hipstr::vecs::HipVec;
    /// use hipstr::Arc;
    /// let vec = HipVec::<u8, Arc>::from_array([1, 2, 3]);
    /// assert_eq!(vec.as_slice(), &[1, 2, 3]);
    /// ```
    #[inline]
    pub fn as_slice(&self) -> &[T] {
        if let Tag::Inline = self.tag() {
            unsafe { self.repr.inline() }.as_slice()
        } else {
            unsafe { self.repr.slice_view() }.as_slice()
        }
    }

    /// Returns a pointer to the vector's data.
    ///
    /// If the vector is borrowed, it returns a pointer to the borrowed slice.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hipstr::vecs::HipVec;
    /// use hipstr::Arc;
    /// let array = [1, 2, 3];
    /// let vec = HipVec::<u8, Arc>::borrowed(&array);
    /// assert_eq!(vec.as_ptr(), array.as_ptr());
    /// ```
    #[inline]
    pub fn as_ptr(&self) -> *const T {
        if let Tag::Inline = self.tag() {
            unsafe { self.repr.inline() }.as_ptr()
        } else {
            unsafe { self.repr.slice_view() }.ptr.as_ptr()
        }
    }

    /// Returns the length of the vector.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hipstr::vecs::HipVec;
    /// use hipstr::Arc;
    /// let vec = HipVec::<u8, Arc>::from_array([1, 2, 3]);
    /// assert_eq!(vec.len(), 3);
    /// ```
    #[inline]
    pub const fn len(&self) -> usize {
        if let Tag::Inline = self.tag() {
            unsafe { self.repr.inline::<T>() }.len()
        } else {
            unsafe { self.repr.slice_view::<T>() }.len
        }
    }

    /// Returns `true` if the vector is empty.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hipstr::vecs::HipVec;
    /// use hipstr::Arc;
    /// let vec = HipVec::<u8, Arc>::from_array([]);
    /// assert!(vec.is_empty());
    /// let vec = HipVec::<u8, Arc>::from_array([1, 2, 3]);
    /// assert!(!vec.is_empty());
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub const fn take(&mut self) -> Self {
        core::mem::replace(self, Self::EMPTY)
    }

    /// Clones the hip vector without cloning or copying the elements if
    /// possible, returns `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hipstr::vecs::HipVec;
    /// use hipstr::vecs::hip::Tag;
    /// use hipstr::{Arc, Unique};
    ///
    /// let vec = HipVec::<u8, Arc>::from_array([1, 2, 3]);
    /// assert_eq!(vec.tag(), Tag::Inline);
    /// let cloned = vec.try_clone();
    /// assert!(cloned.is_none(), "inline vector cannot be shared");
    ///
    /// let vec = HipVec::<u8, Unique>::from_array([1; 40]);
    /// assert_eq!(vec.tag(), Tag::Thin);
    /// let cloned = vec.try_clone();
    /// assert!(cloned.is_none(), "unique vector cannot be shared");
    ///
    /// let vec = HipVec::<u8, Arc>::from_array([1; 40]);
    /// assert_eq!(vec.tag(), Tag::Thin);
    /// let cloned = vec.try_clone();
    /// assert!(cloned.is_some(), "arc thin vector can be shared");
    ///
    /// let arr = [1,2,3,4,5];
    /// let vec = HipVec::<u8, Arc>::borrowed(&arr);
    /// assert_eq!(vec.tag(), Tag::Borrowed);
    /// let cloned = vec.try_clone();
    /// assert!(cloned.is_some(), "borrowed vector can be shared");
    #[inline]
    pub fn try_clone(&self) -> Option<Self> {
        match self.tag() {
            Tag::Inline => None,
            Tag::Thin | Tag::Fat => {
                // SAFETY: the repr is checked above
                let view = unsafe { self.repr.shared_view::<B>() };
                let result = view.with(|counter| counter.incr());
                match result {
                    UpdateResult::Done => Some(Self {
                        repr: self.repr,
                        _marker: PhantomData,
                    }),
                    UpdateResult::Overflow => None,
                }
            }
            Tag::Borrowed => Some(Self {
                repr: self.repr,
                _marker: PhantomData,
            }),
        }
    }
}

impl<'borrow, T: Clone, B: Backend> HipVec<'borrow, T, B> {
    #[inline]
    #[must_use]
    pub fn from_slice_clone(slice: &[T]) -> Self {
        if Self::fit_inline(slice.len()) {
            Self::from_inline(Inline::from_slice_clone(slice))
        } else {
            let owner = SmartThinVec::from_slice_clone(slice);
            Self::from_thin(owner)
        }
    }

    #[inline]
    #[must_use]
    pub fn slice(&self, range: impl RangeBounds<usize>) -> Self {
        match self.try_slice_clone(range) {
            Ok(slice) => slice,
            Err(err) => panic!("invalid range: {}", err),
        }
    }

    /// Slices the vector, returning a new `HipVec` that contains the specified range.
    ///
    /// # Errors
    ///
    /// Returns an error if the range is out of bounds or invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hipstr::vecs::HipVec;
    /// use hipstr::vecs::hip::Tag;
    /// use hipstr::Arc;
    /// let vec = HipVec::<u8, Arc>::from_array([1, 2, 3, 4, 5]);
    /// assert_eq!(vec.tag(), Tag::Inline);
    /// let sliced = vec.slice(1..4);
    /// assert_eq!(sliced.as_slice(), &[2, 3, 4]);
    ///
    /// let vec = HipVec::<u8, Arc>::from_array([1; 40]);
    /// assert_eq!(vec.tag(), Tag::Thin);
    /// let sliced = vec.slice(0..4);
    /// assert_eq!(sliced.tag(), Tag::Inline); // normalized to inline
    /// assert_eq!(sliced.as_slice(), &[1, 1, 1, 1]);
    ///
    /// let sliced = vec.slice(0..39);
    /// assert_eq!(sliced.as_slice(), &[1; 39]);
    /// assert_eq!(sliced.tag(), Tag::Thin); // remains thin
    /// assert_eq!(sliced.as_ptr(), vec.as_ptr()); // no copy
    /// ```
    pub fn try_slice_clone(&self, range: impl RangeBounds<usize>) -> Result<Self, RangeError>
    where
        T: Clone,
    {
        let range = common::range(range, self.len())?;
        let len = range.len();
        if len == 0 {
            Ok(Self::EMPTY)
        } else if Self::fit_inline(len) {
            // normalize to inline if possible
            let slice = unsafe { self.as_slice().get_unchecked(range) };
            Ok(Self::from_inline(Inline::from_slice_clone(slice)))
        } else {
            match self.tag() {
                Tag::Inline => unsafe { unreachable_unchecked() },
                Tag::Thin | Tag::Fat => {
                    let shared_view = unsafe { self.repr.shared_view::<B>() };

                    let UpdateResult::Done = shared_view.with(Counter::incr) else {
                        // the counter overflows, we need to clone the data
                        let slice = unsafe { self.as_slice().get_unchecked(range) };
                        return Ok(Self::from_slice_clone(slice));
                    };

                    // do nothing here, will update the slice below
                }
                Tag::Borrowed => {} // do nothing here, will update the slice below
            }

            // copy the whole structure
            let mut new = Self {
                repr: self.repr,
                _marker: PhantomData,
            };

            // update the slice part
            let ref_mut = unsafe { new.repr.slice_view_mut::<T>() };
            ref_mut.ptr = unsafe { ref_mut.ptr.add(range.start) };
            ref_mut.len = len;

            Ok(new)
        }
    }

    /// Clones the vector, returning a new hip vector that contains the same
    /// elements, possibly clong them if necessary.
    ///
    /// It will clone the data if either the vector is inline or the sharing
    /// is impossible.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hipstr::vecs::HipVec;
    /// use hipstr::vecs::hip::Tag;
    /// use hipstr::{Arc, Unique};
    /// let vec = HipVec::<u8, Arc>::from_array([1, 2, 3]);
    /// assert_eq!(vec.tag(), Tag::Inline);
    /// let cloned = vec.force_clone();
    /// assert_eq!(cloned.tag(), Tag::Inline);
    ///
    /// let vec = HipVec::<u8, Unique>::from_array([0; 40]);
    /// assert_eq!(vec.tag(), Tag::Thin);
    /// let cloned = vec.force_clone();
    /// assert_eq!(cloned.tag(), Tag::Thin);
    ///
    ///
    /// let vec = HipVec::<u8, Arc>::from_array([0; 40]);
    /// assert_eq!(vec.tag(), Tag::Thin);
    /// let cloned = vec.force_clone();
    /// assert_eq!(cloned.tag(), Tag::Thin);
    /// assert_eq!(cloned.as_ptr(), vec.as_ptr());
    /// ```
    #[inline]
    pub fn force_clone(&self) -> Self {
        self.try_clone()
            .unwrap_or_else(|| Self::from_slice_clone(self.as_slice()))
    }

    pub fn detach(&mut self) {
        match self.tag() {
            Tag::Inline => {
                // do nothing
            }
            Tag::Thin | Tag::Fat if self.is_unique() => {
                // do nothing
            }
            _ => *self = Self::from_slice_clone(self.as_slice()),
        }
    }
}

impl<'borrow, T: Copy, B: Backend> HipVec<'borrow, T, B> {
    #[inline]
    pub fn from_slice_copy(slice: &[T]) -> Self
    where
        T: Copy,
    {
        if Self::fit_inline(slice.len()) {
            Self::from_inline(Inline::from_slice_copy(slice))
        } else {
            let owner = SmartThinVec::from_slice_copy(slice);
            Self::from_thin(owner)
        }
    }

    pub fn slice_copy(&self, range: impl RangeBounds<usize>) -> Self {
        match self.try_slice_copy(range) {
            Ok(slice) => slice,
            Err(err) => panic!("invalid range: {}", err),
        }
    }

    pub fn try_slice_copy(&self, range: impl RangeBounds<usize>) -> Result<Self, RangeError>
    where
        T: Copy,
    {
        let range = common::range(range, self.len())?;
        let len = range.len();
        if len == 0 {
            Ok(Self::EMPTY)
        } else if Self::fit_inline(len) {
            let slice = unsafe { self.as_slice().get_unchecked(range) };
            Ok(Self::from_inline(Inline::from_slice_copy(slice)))
        } else {
            match self.tag() {
                Tag::Inline => {
                    // SAFETY: a subslice of an inline vector is always inlinable. Already done above.
                    unsafe {
                        unreachable_unchecked();
                    }
                }
                Tag::Thin | Tag::Fat => {
                    todo!()
                }
                Tag::Borrowed => {
                    // SAFETY: tag is checked.
                    let borrowed = unsafe { self.as_borrowed_unchecked() };
                    let slice = unsafe { borrowed.get_unchecked(range) };
                    Ok(Self::borrowed(slice))
                }
            }
        }
    }

    #[inline]
    pub fn force_clone_or_copy(&self) -> Self
    where
        T: Copy,
    {
        self.try_clone()
            .unwrap_or_else(|| Self::from_slice_copy(self.as_slice()))
    }

    #[inline]
    pub fn detach_copy(&mut self) {
        match self.tag() {
            Tag::Inline => {
                // do nothing
            }
            Tag::Thin | Tag::Fat if self.is_unique() => {
                // do nothing
            }
            _ => *self = Self::from_slice_copy(self.as_slice()),
        }
    }
}

impl<T, B: Backend> Default for HipVec<'_, T, B> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T, C: Counter> Clone for HipVec<'_, T, BackendImpl<C, PanicOnOverflow>> {
    fn clone(&self) -> Self {
        self.try_clone().unwrap_or_else(|| panic!("count overflow"))
    }
}

impl<T: Clone, C: Counter> Clone for HipVec<'_, T, BackendImpl<C, CloneOnOverflow>> {
    fn clone(&self) -> Self {
        self.force_clone()
    }
}

impl<T, B: Backend> Drop for HipVec<'_, T, B> {
    fn drop(&mut self) {
        match self.tag() {
            Tag::Inline => {
                // SAFETY: representation is inline
                // converts to inline mut ref and drops it in place
                unsafe {
                    ptr::drop_in_place(self.repr.inline_mut::<T>());
                }
            }
            Tag::Thin => {
                // SAFETY: representation is thin
                // converts to thin mut ref and drops the owner in place
                unsafe {
                    ptr::drop_in_place(self.repr.thin_mut::<T, B>().owner_mut().as_mut());
                }
            }
            Tag::Fat => {
                // SAFETY: representation is fat
                // converts to fat mut ref and drops the owner in place
                unsafe {
                    ptr::drop_in_place(self.repr.fat_mut::<T, B>().owner_mut().as_mut());
                }
            }

            Tag::Borrowed => {
                // do nothing, borrowed repr does not own the data
            }
            _ => unreachable!(),
        }
    }
}
