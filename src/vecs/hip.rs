use core::hint::unreachable_unchecked;
use core::marker::PhantomData;
use core::mem::ManuallyDrop;
use core::ops::RangeBounds;

use self::allocated::Allocated;
use self::borrowed::Borrowed;
use self::inline::InlineVec;
use self::pivot::{Pivot, Tag, Union};
use crate::backend::Backend;
use crate::common::{self, manually_drop_as_ref, RangeError};
use crate::vecs::{
    SmartThinVec, SmartVec, TAG_BORROWED_MASKED, TAG_FAT, TAG_INLINE, TAG_MASK, TAG_THIN,
};

mod allocated;
mod borrowed;
mod inline;
mod pivot;
#[cfg(test)]
mod tests;

const WORD_SIZE_M1: usize = size_of::<*mut ()>() - 1;
const INLINE_BYTES: usize = size_of::<*mut ()>() * 3 - 1;

pub struct HipVec<'borrow, T, B: Backend> {
    pivot: Pivot,
    _marker: PhantomData<&'borrow (T, B)>,
}

unsafe impl<T: Sync, B: Backend + Sync> Sync for HipVec<'_, T, B> {}
unsafe impl<T: Send, B: Backend + Send> Send for HipVec<'_, T, B> {}

type Inline<T> = InlineVec<T, INLINE_BYTES>;

impl<'borrow, T, B: Backend> HipVec<'borrow, T, B> {
    #[inline]
    pub fn from_array<const N: usize>(arr: [T; N]) -> Self {
        if const { Self::fit_inline(N) } {
            Self::from_inline(Inline::from_array(arr))
        } else {
            let stv = SmartThinVec::from_array(arr);
            let owner = SmartVec::from_thin(stv);
            Self::from_smart_vec(owner)
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
            let stv = SmartThinVec::from_slice_clone(slice);
            let owner = SmartVec::from_thin(stv);
            Self::from_smart_vec(owner)
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
            let stv = SmartThinVec::from_slice_copy(slice);
            let owner = SmartVec::from_thin(stv);
            Self::from_smart_vec(owner)
        }
    }

    #[inline]
    fn from_smart_vec(owner: SmartVec<T, B>) -> Self {
        let allocated = ManuallyDrop::new(Allocated::new(owner));
        let union = pivot::Union { allocated };
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
        match self.tag() {
            Tag::Inline => true,
            Tag::Thin | Tag::Fat => unsafe { self.as_allocated_unchecked().owner.is_unique() },
            Tag::Borrowed => false,
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

    const fn tag(&self) -> Tag {
        let byte = unsafe { self.union().pivot.tag_byte.get() };
        match byte & TAG_MASK {
            TAG_BORROWED_MASKED => Tag::Borrowed,
            TAG_INLINE => Tag::Inline,
            TAG_THIN => Tag::Thin,
            TAG_FAT => Tag::Fat,
            _ => unsafe { unreachable_unchecked() },
        }
    }

    pub const unsafe fn as_borrowed_unchecked(&self) -> &'borrow [T] {
        debug_assert!(self.is_borrowed(), "not a borrowed vector");
        let borrowed = unsafe { &self.union().borrowed };
        borrowed.as_slice()
    }

    pub const fn as_borrowed(&self) -> Option<&'borrow [T]> {
        match self.tag() {
            Tag::Borrowed => {
                let borrowed = unsafe { &self.union().borrowed };
                Some(borrowed.as_slice())
            }
            _ => None,
        }
    }

    unsafe fn as_allocated_unchecked(&self) -> &Allocated<T, B> {
        unsafe { manually_drop_as_ref(&self.union().allocated) }
    }

    const MAY_INLINE: bool = align_of::<T>() > align_of::<Pivot>() && Inline::<T>::CAP > 0;

    const fn fit_inline(len: usize) -> bool {
        Self::MAY_INLINE && len < Inline::<T>::CAP
    }

    #[inline]
    unsafe fn as_inline_unchecked(&self) -> &InlineVec<T, INLINE_BYTES> {
        debug_assert!(Self::MAY_INLINE, "inline should be possible");
        debug_assert!(
            self.is_inline(),
            "invalid repr (allocated or borrowed expected)"
        );
        unsafe { core::mem::transmute(&self.pivot) }
    }

    #[inline]
    const unsafe fn as_slice_view(&self) -> &pivot::SliceView<T> {
        debug_assert!(
            !self.is_inline(),
            "invalid repr (allocated or borrowed expected)"
        );
        let view = unsafe { &self.union().slice };
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
            unsafe { self.as_inline_unchecked().as_slice() }
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
            unsafe { self.as_inline_unchecked().as_ptr() }
        } else {
            unsafe { self.union().slice.ptr.as_ptr() }
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
    pub fn len(&self) -> usize {
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

    const EMPTY: Self = Self::borrowed(&[]);

    /// Slices the vector, returning a new `HipVec` that contains the specified range.
    pub fn try_slice_clone(&self, range: impl RangeBounds<usize>) -> Result<Self, RangeError>
    where
        Self: Clone,
    {
        let range = common::range(range, self.len())?;
        let len = range.len();
        if len == 0 {
            Ok(Self::EMPTY)
        } else if Self::fit_inline(len) {
            let slice = unsafe { self.as_slice().get_unchecked(range) };
            Ok(Self::from_inline(Inline::from_slice_clone(slice)))
        } else {
            match self.tag() {
                Tag::Inline => unsafe { unreachable_unchecked() },
                Tag::Thin | Tag::Fat => {
                    let allocated = unsafe { self.as_allocated_unchecked() };
                    let owner = allocated.owner.clone();
                    let new_allocated = Allocated {
                        owner,
                        ptr: unsafe { allocated.ptr.add(range.start) },
                        len,
                    };
                    todo!()
                }
                Tag::Borrowed => {
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
