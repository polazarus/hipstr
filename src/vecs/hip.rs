use alloc::boxed::Box;
use alloc::vec::Vec;
use core::hint::unreachable_unchecked;
use core::marker::PhantomData;
use core::mem::ManuallyDrop;
use core::ops::RangeBounds;
use core::{panic, ptr};
use std::borrow::Cow;

use rules_derive::rules_derive;

use self::allocated::Allocated;
use self::inline::InlineVec;
pub use self::reprs::Tag;
use self::reprs::{Borrowed, Repr, Union};
use crate::backend::{
    Backend, BackendImpl, CloneOnInlineClone, CloneOnOverflow, Counter, PanicOnInlineClone,
    PanicOnOverflow, UpdateResult,
};
use crate::common::boo::Boo;
use crate::common::{self, derives, vec_push_within_capacity, RangeError};
use crate::smart::Smart;
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
#[rules_derive(
    derives::AsRefAndDeref(target = [T], method = as_slice),
    derives::Default,
    derives::From(
        bindings = (<'borrow, T, B: Backend,const N: usize>),
        source = [T; N],
        cons = Self::from_array
    ),
    derives::From(
        bindings = (<'borrow, T, B: Backend>),
        source = Box<[T]>,
        cons = Self::from_boxed_slice
    ),
    derives::From(
        bindings = (<'borrow, T, B: Backend>),
        source = Vec<T>,
        cons = Self::from_vec
    ),
    derives::From(
        bindings = (<'borrow, T: Clone, B: Backend>),
        source = &[T],
        cons = Self::from_slice_clone
    ),
    derives::Vector(T),
)]
pub struct HipVec<'borrow, T, B: Backend> {
    repr: Repr,
    _marker: PhantomData<&'borrow (T, B)>,
}

unsafe impl<T: Sync, B: Backend + Sync> Sync for HipVec<'_, T, B> {}

unsafe impl<T: Send, B: Backend + Send> Send for HipVec<'_, T, B> {}

type Inline<T> = InlineVec<T, u8, INLINE_BYTES>;

impl<'borrow, T, B: Backend> HipVec<'borrow, T, B> {
    /// An empty `HipVec` constant.
    const EMPTY: Self = Self::borrowed(&[]);

    /// Can the type be inlined?
    const MAY_INLINE: bool = align_of::<T>() <= align_of::<Repr>() && Inline::<T>::CAP > 0;

    /// Checks if the given length fits in the inline repr.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::HipVec;
    /// use hipstr::Arc;
    /// assert!(!HipVec::<u128, Arc>::fit_inline(0)); // alignment issue
    /// assert!(HipVec::<u8, Arc>::fit_inline(size_of::<usize>() * 3 - 1));
    /// ````
    pub const fn fit_inline(len: usize) -> bool {
        Self::MAY_INLINE && len <= Inline::<T>::CAP
    }

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
    #[must_use]
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

    /// Creates a new `HipVec` from a borrowed slice.
    ///
    /// # Examples
    /// ```rust
    /// use hipstr::vecs::HipVec;
    /// use hipstr::Arc;
    /// let array = [1, 2, 3];
    /// let vec = HipVec::<u8, Arc>::borrowed(&array);
    /// assert!(vec.is_borrowed());
    /// assert_eq!(&raw const *vec.as_slice(), &raw const *array.as_slice());
    /// ```
    #[inline]
    #[must_use]
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

    /// Creates a new `HipVec` from an array.
    /// If the array fits inline, it will be stored inline.
    /// Otherwise, it will be stored as a thin vector.
    #[inline]
    #[must_use]
    pub fn from_array<const N: usize>(arr: [T; N]) -> Self {
        if const { Self::fit_inline(N) } {
            Self::from_inline(Inline::from_array(arr))
        } else {
            let owner = SmartThinVec::from_array(arr);
            Self::from_thin(owner)
        }
    }

    /// Creates a new `HipVec` from a boxed slice.
    /// If the slice fits inline, it will be stored inline.
    /// Otherwise, it will be stored as a thin vector.
    #[inline]
    #[must_use]
    pub(crate) fn from_boxed_slice(slice: Box<[T]>) -> Self {
        if Self::fit_inline(slice.len()) {
            Self::from_inline(Inline::from_boxed_slice(slice))
        } else {
            let owner = SmartThinVec::from_boxed_slice(slice);
            Self::from_thin(owner)
        }
    }

    /// Creates a new `HipVec` from a raw pointer and length by moving data (taking ownership)
    #[inline]
    #[must_use]
    pub(crate) fn from_raw(ptr: *mut T, len: usize) -> Self {
        if Self::fit_inline(len) {
            Self::from_inline(Inline::from_raw(ptr, len))
        } else {
            let owner = SmartThinVec::from_raw_ptr(ptr, len);
            Self::from_thin(owner)
        }
    }

    /// Creates a new `HipVec` from a [`Vec`]`.
    /// If the vector fits inline, it will be stored inline.
    /// Otherwise, it will be stored as a fat vector to spare the move and the allocation.
    #[inline]
    #[must_use]
    pub(crate) fn from_vec(value: Vec<T>) -> Self {
        if Self::fit_inline(value.len()) {
            Self::from_inline(Inline::from_mut_vector(value))
        } else {
            Self::from_fat(Smart::new(value))
        }
    }

    #[inline]
    const fn from_union(union: Union<'borrow, T, B>) -> Self {
        Self {
            repr: unsafe { union.pivot },
            _marker: PhantomData,
        }
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
                unsafe { self.repr.shared_view::<B>() }.with(Counter::is_unique)
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
    #[must_use]
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
    #[must_use]
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
    #[must_use]
    pub const fn is_inline(&self) -> bool {
        matches!(self.tag(), Tag::Inline)
    }
    /// Returns a value identifying the current representation of this vector.
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
    #[must_use]
    pub const fn tag(&self) -> Tag {
        self.repr.repr()
    }

    /// Gets the borrowed slice.
    ///
    /// # Safety
    ///
    /// This function assumes that the vector is borrowed.
    #[inline]
    #[must_use]
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
    #[must_use]
    pub const fn as_borrowed(&self) -> Option<&'borrow [T]> {
        #[allow(clippy::equatable_if_let, reason = "const")]
        if let Tag::Borrowed = self.tag() {
            // SAFETY: repr is checked above
            let borrowed = unsafe { &self.repr.borrowed() };
            Some(borrowed.as_slice())
        } else {
            None
        }
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
    #[must_use]
    pub const fn as_slice(&self) -> &[T] {
        #[allow(clippy::equatable_if_let, reason = "const")]
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
    #[must_use]
    pub const fn as_ptr(&self) -> *const T {
        #[allow(clippy::equatable_if_let, reason = "const")]
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
    #[must_use]
    pub const fn len(&self) -> usize {
        #[allow(clippy::equatable_if_let, reason = "const")]
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
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the capacity of the underlying buffer.
    ///
    /// If the vector is borrowed, it returns 0.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hipstr::vecs::HipVec;
    /// use hipstr::Arc;
    /// let vec = HipVec::<u8, Arc>::from_array([1, 2, 3]);
    /// assert!(vec.capacity() >= 3);
    /// let vec2 = HipVec::<u8, Arc>::from_array([1; 40]);
    /// assertq!(vec2.capacity() >= 40);
    /// let slice = vec2.try_slice(0..16).unwrap();
    /// assert_eq!(slice.capacity(), vec2.capacity());
    /// ```
    #[must_use]
    pub const fn capacity(&self) -> usize {
        match self.tag() {
            Tag::Inline => Inline::<T>::CAP,
            Tag::Thin => {
                let v = unsafe { self.repr.thin::<T, B>() };
                v.owner.get().as_ref().capacity()
            }
            Tag::Fat => {
                let v = unsafe { self.repr.fat::<T, B>() };
                v.owner.get().as_ref().capacity()
            }
            Tag::Borrowed => 0,
        }
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
    #[must_use]
    pub fn try_clone(&self) -> Option<Self> {
        let clonable = match self.tag() {
            Tag::Inline => false,
            Tag::Thin | Tag::Fat => {
                // SAFETY: the repr is checked above
                let view = unsafe { self.repr.shared_view::<B>() };
                view.with(Counter::incr) == UpdateResult::Done
            }
            Tag::Borrowed => true,
        };

        clonable.then(|| Self {
            repr: self.repr,
            _marker: PhantomData,
        })
    }

    /// Truncates the vector to the specified length.
    ///
    /// Contrarily to [`Vec::truncate`], this function does not release the
    /// elements if the vector is shared.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::HipVec;
    /// use hipstr::Arc;
    /// let mut vec = HipVec::<u8, Arc>::from_array([1, 2, 3, 4, 5]);
    /// assert_eq!(vec.as_slice(), &[1, 2, 3, 4, 5]);
    /// vec.truncate(3);
    /// assert_eq!(vec.as_slice(), &[1, 2, 3]);
    /// ```
    pub fn truncate(&mut self, len: usize) {
        match self.tag() {
            Tag::Inline => {
                // SAFETY: repr is inline
                let inline = unsafe { self.repr.inline_mut::<T>() };
                inline.truncate(len);
            }
            tag @ (Tag::Thin | Tag::Fat | Tag::Borrowed) => {
                // SAFETY: repr is thin, fat or borrowed
                let slice_view = unsafe { self.repr.slice_view_mut::<T>() };
                if len >= slice_view.len {
                    return;
                }

                slice_view.len = len;

                if let Tag::Thin | Tag::Fat = tag {
                    if self.is_unique() {
                        if tag == Tag::Thin {
                            let thin = unsafe { self.repr.thin_mut::<T, B>() };
                            thin.with_mut(|t, range| {
                                // SAFETY: repr is thin and unique
                                let t = unsafe { t.as_mut_unchecked() };
                                t.truncate(range.start + len);
                            });
                        } else {
                            let fat = unsafe { self.repr.fat_mut::<T, B>() };
                            fat.with_mut(|v, range| {
                                // SAFETY: repr is fat and unique
                                let v = unsafe { Smart::get_mut_unchecked(v) };
                                v.truncate(range.start + len);
                            });
                        }
                    }
                }
            }
        }
    }

    /// Tries to push a new element into the vector without reallocating.
    ///
    /// Note that, if the vector is borrowed, it will return an error
    /// systematically.
    ///
    /// # Errors
    ///
    /// Returns the value as error if the vector is shared or if it cannot fit
    /// the new element.
    ///
    /// # Examples
    ///
    /// ```
    ///
    /// use hipstr::vecs::HipVec;
    /// use hipstr::vecs::hip::Tag;
    /// use hipstr::Arc;
    /// let mut vec = HipVec::<u8, Arc>::from_array([1, 2, 3]);
    /// assert_eq!(vec.tag(), Tag::Inline);
    /// assert!(vec.push_within_capacity(4).is_ok());
    /// assert_eq!(vec.as_slice(), &[1, 2, 3, 4]);
    ///
    /// let mut vec = HipVec::<u8, Arc>::borrowed(&[]);
    /// assert_eq!(vec.tag(), Tag::Borrowed);
    /// assert!(vec.push_within_capacity(2).is_err());
    /// ```
    pub fn push_within_capacity(&mut self, value: T) -> Result<(), T> {
        if !self.is_unique() {
            return Err(value);
        }

        match self.tag() {
            Tag::Inline => unsafe { self.repr.inline_mut() }.try_push(value),

            Tag::Thin => {
                // SAFETY: repr is thin
                let thin = unsafe { self.repr.thin_mut::<T, B>() };
                thin.with_mut(|t, range| {
                    // SAFETY: vec is unique
                    let t = unsafe { t.as_mut_unchecked() };
                    t.truncate(range.end);
                    t.push_within_capacity(value)
                })
            }

            Tag::Fat => {
                // SAFETY: repr is fat and unique
                let fat = unsafe { self.repr.fat_mut::<T, B>() };
                fat.with_mut(|v, range| {
                    // SAFETY: vec is unique
                    let v = unsafe { Smart::get_mut_unchecked(v) };
                    v.truncate(range.end);
                    vec_push_within_capacity(v, value)
                })
            }

            // SAFETY: repr borrowed cannot be unique
            Tag::Borrowed => unsafe { unreachable_unchecked() },
        }
    }

    /// Tries to slice the vector, returning a new `HipVec` that contains the specified range,
    /// without allocating or cloning.
    ///
    /// Note that this function do not normalize the vector, so it will never return an inline
    /// vector.
    ///
    /// # Errors
    ///
    /// Returns an error for three distinct reasons:
    ///
    /// - the range is invalid,
    /// - the vector is inline, which cannot be sliced without cloning,
    /// - the vector is shared and the counter overflows.
    ///
    /// # Examples
    ///
    /// ```
    /// use hipstr::vecs::HipVec;
    /// use hipstr::vecs::hip::Tag;
    /// use hipstr::Arc;
    ///
    /// let vec = HipVec::<u8, Arc>::from_array([1, 2, 3, 4, 5]);
    /// assert_eq!(vec.tag(), Tag::Inline);
    /// assert!(vec.try_slice(1..4).is_err());
    ///
    /// let vec = HipVec::<u8, Arc>::from_array([1; 40]);
    /// assert_eq!(vec.tag(), Tag::Thin);
    /// let sliced = vec.try_slice(0..4).unwrap();
    /// assert_eq!(sliced.tag(), Tag::Thin); // not normalized
    ///
    pub fn try_slice(&self, range: impl RangeBounds<usize>) -> Result<Self, SliceError> {
        match common::range(range, self.len()) {
            Err(range_error) => Err(SliceError::Range(range_error)),
            Ok(range) if range.start == range.end => Ok(Self::EMPTY),
            Ok(range) => match self.tag() {
                Tag::Inline => Err(SliceError::Unshared),
                Tag::Borrowed => {
                    let slice = unsafe { self.as_borrowed_unchecked() };
                    Ok(Self::borrowed(unsafe { slice.get_unchecked(range) }))
                }
                Tag::Thin | Tag::Fat => {
                    // try to update the counter
                    let shared_view = unsafe { self.repr.shared_view::<B>() };
                    if shared_view.with(Counter::incr) == UpdateResult::Done {
                        // copy the handle
                        let mut this = Self {
                            repr: self.repr,
                            _marker: PhantomData,
                        };

                        // update the slice
                        {
                            let slice_view_mut = unsafe { this.repr.slice_view_mut::<T>() };
                            slice_view_mut.len = range.end - range.start;
                            slice_view_mut.ptr = unsafe { slice_view_mut.ptr.add(range.start) };
                        }

                        Ok(this)
                    } else {
                        Err(SliceError::Overflow)
                    }
                }
            },
        }
    }

    pub fn try_pop(&mut self) -> Option<Boo<'_, T>> {
        if self.is_unique() {
            match self.tag() {
                Tag::Inline => unsafe { self.repr.inline_mut() }.pop(),

                Tag::Thin => {
                    // SAFETY: repr is thin
                    let thin = unsafe { self.repr.thin_mut::<T, B>() };
                    thin.with_mut(|t, range| {
                        // SAFETY: vec is unique
                        let t = unsafe { t.as_mut_unchecked() };
                        t.truncate(range.end);
                        t.pop()
                    })
                }

                Tag::Fat => {
                    // SAFETY: repr is fat and unique
                    let fat = unsafe { self.repr.fat_mut::<T, B>() };
                    fat.with_mut(|v, range| {
                        // SAFETY: vec is unique
                        let v = unsafe { Smart::get_mut_unchecked(v) };
                        v.truncate(range.end);
                        v.pop()
                    })
                }

                Tag::Borrowed => unreachable!(),
            }
            .map(Boo::Owned)
        } else {
            match self.tag() {
                Tag::Inline => unreachable!(),
                Tag::Borrowed | Tag::Thin | Tag::Fat => {
                    // SAFETY: repr is borrowed, thin or fat
                    let slice_view = unsafe { self.repr.slice_view::<T>() };
                    if slice_view.len == 0 {
                        None
                    } else {
                        // SAFETY: length is checked above
                        let value = unsafe { slice_view.ptr.add(slice_view.len - 1).as_ref() };
                        Some(Boo::Borrowed(value))
                    }
                }
            }
        }
    }

    pub fn try_pop_if(&mut self, predicate: impl FnOnce(&T) -> bool) -> Option<Boo<'_, T>> {
        if self.is_unique() {
            match self.tag() {
                Tag::Inline => unsafe { self.repr.inline_mut() }.pop_if(|v| predicate(v)),

                Tag::Thin => {
                    // SAFETY: repr is thin
                    let thin = unsafe { self.repr.thin_mut::<T, B>() };
                    thin.with_mut(|t, range| {
                        // SAFETY: vec is unique
                        let t = unsafe { t.as_mut_unchecked() };
                        t.truncate(range.end);
                        t.pop_if(|v| predicate(v))
                    })
                }

                Tag::Fat => {
                    // SAFETY: repr is fat and unique
                    let fat = unsafe { self.repr.fat_mut::<T, B>() };
                    fat.with_mut(|v, range| {
                        // SAFETY: vec is unique
                        let v = unsafe { Smart::get_mut_unchecked(v) };
                        v.truncate(range.end);
                        v.pop_if(|v| predicate(v))
                    })
                }

                // SAFETY: repr borrowed cannot be unique
                Tag::Borrowed => unsafe { unreachable_unchecked() },
            }
            .map(Boo::Owned)
        } else {
            match self.tag() {
                Tag::Inline => unreachable!(),
                Tag::Borrowed | Tag::Thin | Tag::Fat => {
                    // SAFETY: repr is borrowed, thin or fat
                    let slice_view = unsafe { self.repr.slice_view::<T>() };
                    if slice_view.len == 0 {
                        None
                    } else {
                        // SAFETY: length is checked above
                        let value = unsafe { slice_view.ptr.add(slice_view.len - 1).as_ref() };
                        if predicate(value) {
                            Some(Boo::Borrowed(value))
                        } else {
                            None
                        }
                    }
                }
            }
        }
    }

    pub fn try_split_off(&mut self, offset: usize) -> Option<Self> {
        if !self.is_unique() {
            return None;
        }

        match self.tag() {
            Tag::Inline => {
                let new_inline = unsafe { self.repr.inline_mut() }.split_off(offset);
                Some(Self::from_inline(new_inline))
            }

            Tag::Thin => {
                // SAFETY: repr is thin
                let thin = unsafe { self.repr.thin_mut::<T, B>() };
                thin.with_mut(|t, range| {
                    // SAFETY: vec is unique
                    let t = unsafe { t.as_mut_unchecked() };
                    t.truncate(range.end);
                    unsafe {
                        t.set_len(range.start + offset);
                        Some(Self::from_raw(
                            t.as_mut_ptr().add(offset),
                            range.end - offset,
                        ))
                    }
                })
            }

            Tag::Fat => {
                // SAFETY: repr is fat and unique
                let fat = unsafe { self.repr.fat_mut::<T, B>() };
                fat.with_mut(|v, range| {
                    // SAFETY: vec is unique
                    let v = unsafe { Smart::get_mut_unchecked(v) };
                    v.truncate(range.end);
                    unsafe {
                        v.set_len(range.start + offset);
                        Some(Self::from_raw(
                            v.as_mut_ptr().add(offset),
                            range.end - offset,
                        ))
                    }
                })
            }

            // SAFETY: repr borrowed cannot be unique
            Tag::Borrowed => unsafe { unreachable_unchecked() },
        }
    }
}

impl<T: Clone, B: Backend> HipVec<'_, T, B> {
    /// Creates a new `HipVec` from a slice by cloning the elements.
    #[inline]
    #[must_use]
    pub(crate) fn from_slice_clone(slice: &[T]) -> Self {
        if Self::fit_inline(slice.len()) {
            Self::from_inline(Inline::from_slice_clone(slice))
        } else {
            let owner = SmartThinVec::from_slice_clone(slice);
            Self::from_thin(owner)
        }
    }

    /// Slices the vector, returning a new `HipVec` that contains the specified
    /// range.
    ///
    /// It may clone the data if necessary, for example, if the vector is inline
    /// or if the sharing is impossible.
    ///
    /// # Panics
    ///
    /// This function panics if the range is out of bounds or invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hipstr::vecs::HipVec;
    /// use hipstr::vecs::hip::Tag;
    /// use hipstr::{Arc, Unique};
    /// let vec = HipVec::<u8, Arc>::from_array([1, 2, 3, 4, 5]);
    /// assert_eq!(vec.tag(), Tag::Inline);
    /// let sliced = vec.slice(1..4);
    /// assert_eq!(sliced.as_slice(), &[2, 3, 4]);
    ///
    /// let vec = HipVec::<u8, Unique>::from_array([1; 40]);
    /// assert_eq!(vec.tag(), Tag::Thin);
    /// let sliced = vec.slice(0..4);
    /// assert_eq!(sliced.tag(), Tag::Inline); // normalized to inline
    /// assert_eq!(sliced.as_slice(), &[1, 1, 1, 1]);
    /// let sliced = vec.slice(0..39);
    /// assert_eq!(sliced.as_slice(), &[1; 39]);
    /// ```
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
        Ok(self.try_slice_clone_range(range))
    }

    fn try_slice_clone_range(&self, range: core::ops::Range<usize>) -> Self {
        let len = range.len();
        if len == 0 {
            Self::EMPTY
        } else if Self::fit_inline(len) {
            // normalize to inline if possible
            let slice = unsafe { self.as_slice().get_unchecked(range) };
            Self::from_inline(Inline::from_slice_clone(slice))
        } else {
            match self.tag() {
                Tag::Inline => unsafe { unreachable_unchecked() },

                Tag::Thin | Tag::Fat => {
                    let shared_view = unsafe { self.repr.shared_view::<B>() };

                    let UpdateResult::Done = shared_view.with(Counter::incr) else {
                        // the counter overflows, we need to clone the data
                        let slice = unsafe { self.as_slice().get_unchecked(range) };
                        return Self::from_slice_clone(slice);
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
            {
                let mutable_view = unsafe { new.repr.slice_view_mut::<T>() };
                mutable_view.ptr = unsafe { mutable_view.ptr.add(range.start) };
                mutable_view.len = len;
            }

            new
        }
    }

    /// Clones the vector, returning a new hip vector that contains the same
    /// elements, possibly cloning them if necessary.
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
    #[must_use]
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

    pub fn pop(&mut self) -> Option<T> {
        self.try_pop().map(Boo::into_owned)
    }

    pub fn pop_if(&mut self, predicate: impl FnOnce(&T) -> bool) -> Option<T> {
        if self.is_empty() {
            return None;
        }
        if self.is_unique() {
            match self.tag() {
                Tag::Inline => return unsafe { self.repr.inline_mut() }.pop_if(|v| predicate(v)),
                Tag::Thin => {
                    // SAFETY: repr is thin
                    let thin = unsafe { self.repr.thin_mut::<T, B>() };
                    return thin.with_mut(|t, range| {
                        // SAFETY: vec is unique
                        let t = unsafe { t.as_mut_unchecked() };
                        t.truncate(range.end);
                        t.pop_if(|v| predicate(v))
                    });
                }
                Tag::Fat => {
                    // SAFETY: repr is fat and unique
                    let fat = unsafe { self.repr.fat_mut::<T, B>() };
                    return fat.with_mut(|v, range| {
                        // SAFETY: vec is unique
                        let v = unsafe { Smart::get_mut_unchecked(v) };
                        v.truncate(range.end);
                        v.pop_if(|v| predicate(v))
                    });
                }
                Tag::Borrowed => unsafe { unreachable_unchecked() },
            }
        } else {
            let value = self.as_slice().last().filter(|p| predicate(*p)).cloned()?;
            *self =
                Self::from_slice_clone(unsafe { self.as_slice().get_unchecked(0..self.len() - 1) });
            Some(value)
        }
    }
}

impl<T: Copy, B: Backend> HipVec<'_, T, B> {
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

    /// Slices the vector, returning a new `HipVec` that contains the specified range.
    ///
    /// It may copy the data if necessary, for example, if the vector is inline
    /// or if the sharing is impossible.
    ///
    /// # Panics
    ///
    /// Panics if the range is out of bounds or invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hipstr::vecs::HipVec;
    /// use hipstr::vecs::hip::Tag;
    /// use hipstr::Arc;
    /// let vec = HipVec::<u8, Arc>::from_array([1, 2, 3, 4, 5]);
    /// assert_eq!(vec.tag(), Tag::Inline);
    /// let sliced = vec.slice_copy(1..4);
    /// assert_eq!(sliced.as_slice(), &[2, 3, 4]);
    /// ```
    #[must_use]
    pub fn slice_copy(&self, range: impl RangeBounds<usize>) -> Self {
        match self.try_slice_copy(range) {
            Ok(slice) => slice,
            Err(err) => panic!("invalid range: {}", err),
        }
    }

    /// Slices the vector, returning a new `HipVec` that contains the specified range.
    ///
    /// It may copy the data if necessary, for example, if the vector is inline
    /// or if the sharing is impossible.
    ///
    /// See [`slice_copy`](Self::slice_copy) for the panicky equivalent.
    ///
    /// # Errors
    ///
    /// Returns an error if the range is out of bounds or invalid.
    pub fn try_slice_copy(&self, range: impl RangeBounds<usize>) -> Result<Self, RangeError>
    where
        T: Copy,
    {
        let range = common::range(range, self.len())?;
        Ok(self.try_slice_copy_range(range))
    }

    fn try_slice_copy_range(&self, range: core::ops::Range<usize>) -> Self {
        let len = range.len();
        if len == 0 {
            Self::EMPTY
        } else if Self::fit_inline(len) {
            // normalize to inline if possible
            let slice = unsafe { self.as_slice().get_unchecked(range) };
            Self::from_inline(Inline::from_slice_copy(slice))
        } else {
            match self.tag() {
                Tag::Inline => unsafe { unreachable_unchecked() },
                Tag::Thin | Tag::Fat => {
                    let shared_view = unsafe { self.repr.shared_view::<B>() };

                    let UpdateResult::Done = shared_view.with(Counter::incr) else {
                        // the counter overflows, we need to clone the data
                        let slice = unsafe { self.as_slice().get_unchecked(range) };
                        return Self::from_slice_copy(slice);
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
            {
                let mutable_view = unsafe { new.repr.slice_view_mut::<T>() };
                mutable_view.ptr = unsafe { mutable_view.ptr.add(range.start) };
                mutable_view.len = len;
            }

            new
        }
    }

    #[inline]
    #[must_use]
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

    pub fn pop_copy(&mut self) -> Option<T> {
        self.try_pop().map(Boo::into_copy)
    }

    pub fn pop_if_copy(&mut self, predicate: impl FnOnce(&T) -> bool) -> Option<T> {
        self.try_pop_if(predicate).map(Boo::into_copy)
    }
}

impl<T, C: Counter> Clone for HipVec<'_, T, BackendImpl<C, PanicOnOverflow, PanicOnInlineClone>> {
    fn clone(&self) -> Self {
        self.try_clone().unwrap_or_else(|| {
            if self.is_inline() {
                panic!("inline clone");
            } else {
                panic!("count overflow");
            }
        })
    }
}

impl<T: Clone, C: Counter> Clone
    for HipVec<'_, T, BackendImpl<C, PanicOnOverflow, CloneOnInlineClone>>
{
    fn clone(&self) -> Self {
        self.try_clone().unwrap_or_else(|| {
            if self.is_inline() {
                Self::from_slice_clone(self.as_slice())
            } else {
                panic!("count overflow");
            }
        })
    }
}

impl<T: Clone, C: Counter> Clone
    for HipVec<'_, T, BackendImpl<C, CloneOnOverflow, PanicOnInlineClone>>
{
    fn clone(&self) -> Self {
        self.try_clone().unwrap_or_else(|| {
            if self.is_inline() {
                panic!("inline clone");
            } else {
                Self::from_slice_clone(self.as_slice())
            }
        })
    }
}

impl<T: Clone, C: Counter> Clone
    for HipVec<'_, T, BackendImpl<C, CloneOnOverflow, CloneOnInlineClone>>
{
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
                // SAFETY:
                // - representation is thin
                // - the handle is not used after
                unsafe {
                    ptr::drop_in_place(self.repr.thin_mut::<T, B>());
                }
            }
            Tag::Fat => {
                // SAFETY:
                // - representation is fat
                // - the handle is not used after
                unsafe {
                    ptr::drop_in_place(self.repr.fat_mut::<T, B>());
                }
            }

            Tag::Borrowed => {
                // do nothing, borrowed repr does not own the data
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SliceError {
    Range(RangeError),
    Unshared,
    Overflow,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PopError {
    Empty,
    Shared,
}
