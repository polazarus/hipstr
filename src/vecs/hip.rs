use alloc::vec::Vec;
use core::hint::unreachable_unchecked;
use core::marker::PhantomData;
use core::mem::ManuallyDrop;
use core::ops::RangeBounds;

use self::allocated::Allocated;
use self::borrowed::Borrowed;
use self::inline::InlineVec;
pub use self::pivot::Repr;
use self::pivot::{Pivot, Union};
use crate::backend::{Backend, Counter};
use crate::common::{self, manually_drop_as_ref, RangeError};
use crate::smart::Smart;
use crate::vecs::hip::allocated::{Fat, Thin};
use crate::vecs::{SmartThinVec, TAG_BORROWED_MASKED, TAG_FAT, TAG_INLINE, TAG_MASK, TAG_THIN};

mod allocated;
mod borrowed;
mod inline;
mod pivot;
#[cfg(test)]
mod tests;

const INLINE_BYTES: usize = size_of::<*mut ()>() * 3 - 1;

pub struct HipVec<'borrow, T, B: Backend> {
    pivot: Pivot,
    _marker: PhantomData<&'borrow (T, B)>,
}

unsafe impl<T: Sync, B: Backend + Sync> Sync for HipVec<'_, T, B> {}
unsafe impl<T: Send, B: Backend + Send> Send for HipVec<'_, T, B> {}

type Inline<T> = InlineVec<T, INLINE_BYTES>;

impl<'borrow, T, B: Backend> HipVec<'borrow, T, B> {
    /// An empty `HipVec` constant.
    const EMPTY: Self = Self::borrowed(&[]);

    /// Creates a new empty `HipVec`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hipstr::vecs::HipVec;
    /// use hipstr::Arc;
    /// let vec: HipVec<u8, Arc> = HipVec::new();
    /// assert!(vec.is_empty());
    /// assert_eq!(vec.as_slice(), &[]);
    /// ```
    #[inline]
    pub const fn new() -> Self {
        Self::EMPTY
    }

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
    const fn from_union(union: pivot::Union<'borrow, T, B>) -> Self {
        Self {
            pivot: unsafe { union.pivot },
            _marker: PhantomData,
        }
    }

    #[inline]
    pub fn from_slice_clone(slice: &[T]) -> Self
    where
        T: Clone,
    {
        if Self::fit_inline(slice.len()) {
            Self::from_inline(Inline::from_slice_clone(slice))
        } else {
            let owner = SmartThinVec::from_slice_clone(slice);
            Self::from_thin(owner)
        }
    }

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

    #[inline]
    fn from_fat(owner: Smart<Vec<T>, B>) -> Self {
        let ptr = owner.as_ptr();
        let len = owner.len();
        let fat = ManuallyDrop::new(Allocated::new(owner, ptr, len));
        let union = pivot::Union { fat };
        Self::from_union(union)
    }

    #[inline]
    fn from_thin(owner: SmartThinVec<T, B>) -> Self {
        let ptr = owner.as_ptr();
        let len = owner.len();
        let thin = ManuallyDrop::new(Allocated::new(owner, ptr, len));
        let union = pivot::Union { thin };
        Self::from_union(union)
    }

    #[inline]
    const fn from_inline(inline: Inline<T>) -> Self {
        assert!(Self::MAY_INLINE, "inline should be possible");
        assert!(size_of::<Inline<T>>() == size_of::<Pivot>());
        assert!(align_of::<Inline<T>>() <= align_of::<Pivot>());

        union Tr<T> {
            pivot: Pivot,
            inline: ManuallyDrop<Inline<T>>,
        }
        let inline = ManuallyDrop::new(inline);
        let pivot = unsafe { Tr { inline }.pivot };
        let union = pivot::Union { pivot };
        Self::from_union(union)
    }

    #[inline]
    pub fn is_unique(&self) -> bool {
        match self.repr() {
            Repr::Inline => true,
            Repr::Thin | Repr::Fat => unsafe { &self.union().shared }.with(Counter::is_unique),
            Repr::Borrowed => false,
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
        matches!(self.repr(), Repr::Thin | Repr::Fat)
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
        matches!(self.repr(), Repr::Borrowed)
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
        matches!(self.repr(), Repr::Inline)
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
        let union = Union { borrowed };
        Self::from_union(union)
    }

    const unsafe fn union(&self) -> &pivot::Union<'borrow, T, B> {
        const {
            assert!(size_of::<Union<'borrow, T, B>>() == size_of::<Pivot>());
            assert!(align_of::<Union<'borrow, T, B>>() == align_of::<Pivot>());
        }

        unsafe { &*(&raw const self.pivot as *const pivot::Union<'borrow, T, B>) }
    }

    const unsafe fn union_mut(&mut self) -> &mut pivot::Union<'borrow, T, B> {
        unsafe { &mut *(&raw mut self.pivot as *mut pivot::Union<'borrow, T, B>) }
    }

    /// Returns the representation tag of the vector.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hipstr::vecs::HipVec;
    /// use hipstr::vecs::hip::Repr;
    /// use hipstr::Arc;
    /// let vec = HipVec::<u8, Arc>::from_array([1, 2, 3]);
    /// assert_eq!(vec.repr(), Repr::Inline);
    ///
    /// let array = [1, 2, 3];
    /// let vec = HipVec::<u8, Arc>::borrowed(&array);
    /// assert_eq!(vec.repr(), Repr::Borrowed);
    /// ```
    pub const fn repr(&self) -> Repr {
        self.pivot.repr()
    }

    /// Gets the borrowed slice.
    ///
    /// # Safety
    ///
    /// This function assumes that the vector is borrowed.
    pub const unsafe fn as_borrowed_unchecked(&self) -> &'borrow [T] {
        // SAFETY: repr precondition
        let borrowed = unsafe { self.pivot.as_borrowed() };
        borrowed.as_slice()
    }

    pub const fn as_borrowed(&self) -> Option<&'borrow [T]> {
        match self.repr() {
            Repr::Borrowed => {
                let borrowed = unsafe { &self.union().borrowed };
                Some(borrowed.as_slice())
            }
            _ => None,
        }
    }

    const fn thin(&self) -> Option<&Thin<T, B>> {
        match self.repr() {
            Repr::Thin => Some(manually_drop_as_ref(unsafe { &self.union().thin })),
            _ => None,
        }
    }

    const fn fat(&self) -> Option<&Fat<T, B>> {
        match self.repr() {
            Repr::Thin => Some(manually_drop_as_ref(unsafe { &self.union().fat })),
            _ => None,
        }
    }

    const MAY_INLINE: bool = align_of::<T>() <= align_of::<Pivot>() && Inline::<T>::CAP > 0;

    const fn fit_inline(len: usize) -> bool {
        Self::MAY_INLINE && len < Inline::<T>::CAP
    }

    #[inline]
    const unsafe fn as_inline_unchecked(&self) -> &InlineVec<T, INLINE_BYTES> {
        debug_assert!(Self::MAY_INLINE, "inline should be possible");
        debug_assert!(
            self.is_inline(),
            "invalid repr (allocated or borrowed expected)"
        );
        // SAFETY: inline by precondition
        unsafe { self.pivot.as_inline() }
    }

    #[inline]
    const unsafe fn as_slice_view(&self) -> &pivot::SliceView<T> {
        debug_assert!(
            !self.is_inline(),
            "invalid repr (allocated or borrowed expected)"
        );
        // SAFETY: the pivot is guaranteed to be a SliceView<T> when not inline
        let view = unsafe { &self.pivot.as_slice_view() };
        view
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
        if self.is_inline() {
            unsafe { self.as_inline_unchecked() }.as_slice()
        } else {
            unsafe { self.as_slice_view() }.as_slice()
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
        if self.is_inline() {
            unsafe { self.as_inline_unchecked() }.as_ptr()
        } else {
            unsafe { self.as_slice_view() }.ptr.as_ptr()
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
        if self.is_inline() {
            unsafe { self.as_inline_unchecked().len() }
        } else {
            unsafe { self.as_slice_view() }.len
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

    /// Slices the vector, returning a new `HipVec` that contains the specified range.
    pub fn try_slice_clone(&self, range: impl RangeBounds<usize>) -> Result<Self, RangeError>
    where
        T: Clone,
    {
        let range = common::range(range, self.len())?;
        let len = range.len();
        if len == 0 {
            Ok(Self::EMPTY)
        } else if Self::fit_inline(len) {
            let slice = unsafe { self.as_slice().get_unchecked(range) };
            Ok(Self::from_inline(Inline::from_slice_clone(slice)))
        } else {
            match self.repr() {
                Repr::Inline => unsafe { unreachable_unchecked() },
                Repr::Thin => {
                    let thin = unsafe { self.thin().unwrap_unchecked() };
                    let owner = thin.owner();
                    if let Some(owner) = owner.try_clone() {
                        Ok(Self::from_union(Union {
                            thin: ManuallyDrop::new(Allocated::new(
                                owner,
                                unsafe { thin.ptr.add(range.start) },
                                len,
                            )),
                        }))
                    } else {
                        //let new_owner = owner.detached_clone();
                        // force_clone()
                        // retrieve the slice's index
                        // set correctly the new ptr/len
                        todo!();
                    }
                }
                Repr::Fat => {
                    let fat = unsafe { self.fat().unwrap_unchecked() };
                    if let Some(owner) = fat.owner().try_clone() {
                        Ok(Self::from_union(Union {
                            fat: ManuallyDrop::new(Allocated::new(
                                owner,
                                unsafe { fat.ptr.add(range.start) },
                                len,
                            )),
                        }))
                    } else {
                        // force_clone()
                        // retrieve the slice's index
                        // set correctly the new ptr/len
                        todo!();
                    }
                }
                Repr::Borrowed => {
                    let borrowed = unsafe { self.as_borrowed_unchecked() };
                    let slice = unsafe { borrowed.get_unchecked(range) };
                    Ok(Self::borrowed(slice))
                }
            }
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
            match self.repr() {
                Repr::Inline => {
                    // SAFETY: a subslice of an inline vector is always inlinable. Already done above.
                    unsafe {
                        unreachable_unchecked();
                    }
                }
                Repr::Thin | Repr::Fat => {
                    todo!()
                }
                Repr::Borrowed => {
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
        todo!()
    }

    pub const fn take(&mut self) -> Self {
        core::mem::replace(self, Self::EMPTY)
    }

    const fn into_union(self) -> pivot::Union<'borrow, T, B> {
        let pivot = self.pivot;
        core::mem::forget(self);
        Union { pivot }
    }

    const unsafe fn into_inline_unchecked(self) -> Inline<T> {
        debug_assert!(Self::MAY_INLINE, "inline should be possible");
        debug_assert!(
            self.is_inline(),
            "invalid repr (allocated or borrowed expected)"
        );
        assert!(
            size_of::<Inline<T>>() == size_of::<Pivot>(),
            "inline size mismatch"
        );
        assert!(
            align_of::<Inline<T>>() <= align_of::<Pivot>(),
            "inline alignment mismatch"
        );
        union Tr<T> {
            pivot: Pivot,
            inline: ManuallyDrop<Inline<T>>,
        }

        let pivot = self.pivot;
        core::mem::forget(self);

        ManuallyDrop::into_inner(unsafe { Tr { pivot }.inline })
    }
}

impl<'borrow, T, B: Backend> Default for HipVec<'borrow, T, B> {
    fn default() -> Self {
        Self::new()
    }
}
