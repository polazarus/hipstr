use core::marker::PhantomData;
use core::mem::{needs_drop, transmute_copy};

use rules_derive::rules_derive;

use crate::backend::UpdateResult;
use crate::common::derives::*;
use crate::common::{transmute2, transmute_mut, transmute_ref, transmute_unaligned};
use crate::vecs::reprs::{Borrowed, FatOrThinRepr, Pivot, Sliced, UnknownSliced, Variant};
use crate::vecs::smart_fat::SmartFatVec;
use crate::vecs::{InlineVec, SmartThinVec};
use crate::Backend;

#[cfg(test)]
mod tests;

#[rules_derive(
    ConstDefault(Self::EMPTY),
    AsRef([T], Self::as_slice),
    Deref([T], Self::as_slice),
    From(bindings = (<'a, T, B: Backend, const N: usize>), source = [T; N], cons = Self::from_array),
)]
pub struct HipVec<'a, T, B: Backend>(Pivot, PhantomData<(B, &'a [T])>);
pub const INLINE_BYTES: usize = size_of::<Borrowed<()>>();
pub type InlineBytes = crate::typenum::U<INLINE_BYTES>;

impl<'a, T, B: Backend> HipVec<'a, T, B> {
    const EMPTY: Self = Self::borrowed(&[]);
    pub const INLINE_CAP: usize = InlineVec::<T, InlineBytes>::CAP;

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
            return Self::new();
        } else if N <= Self::INLINE_CAP {
            let inline = InlineVec::from_array(array);
            Self::from_inline(inline)
        } else {
            let smart = SmartThinVec::from_array(array);
            Self::from_smart_thin(smart)
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
    /// use hipstr::Arc;
    /// let a: HipVec<u8, Arc> = HipVec::from([0; 1024]);
    /// assert!(!a.is_inline());
    /// //assert!(!a.is_borrowed());
    /// //assert!(a.is_allocated());
    /// //assert_eq!(a.len(), 1024);
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_allocated(&self) -> bool {
        !self.is_inline() && unsafe { self.as_sliced_unchecked() }.is_allocated()
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
        !self.is_inline() && unsafe { self.as_sliced_unchecked() }.is_borrowed()
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
    /// use hipstr::Arc;
    /// let a: HipVec<u8,Arc> = HipVec::new();
    /// assert!(a.is_empty());
    ///
    /// let b: HipVec<u8,Arc> = HipVec::from([1,2,3]);
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

    const unsafe fn as_inline_unchecked(&self) -> &InlineVec<T, InlineBytes> {
        debug_assert!(self.is_inline());
        // SAFETY: precondition
        unsafe { transmute_ref::<Self, InlineVec<T, InlineBytes>>(self) }
    }

    const unsafe fn as_inline_mut_unchecked(&mut self) -> &mut InlineVec<T, InlineBytes> {
        debug_assert!(self.is_inline());
        // SAFETY: precondition
        unsafe { transmute_mut::<Self, InlineVec<T, InlineBytes>>(self) }
    }

    const unsafe fn as_sliced_unchecked(&self) -> &UnknownSliced<T> {
        debug_assert!(!self.is_inline());
        // SAFETY: precondition
        unsafe { transmute_ref::<Self, UnknownSliced<T>>(self) }
    }

    const unsafe fn as_allocated_unchecked(&self) -> &Allocated<T, B> {
        debug_assert!(self.is_allocated());
        // SAFETY: precondition
        unsafe { transmute_ref::<Self, Allocated<T, B>>(self) }
    }

    const unsafe fn as_allocated_mut_unchecked(&mut self) -> &mut Allocated<T, B> {
        debug_assert!(self.is_allocated());
        // SAFETY: precondition
        unsafe { transmute_mut::<Self, Allocated<T, B>>(self) }
    }

    #[must_use]
    pub const fn borrowed(slice: &'a [T]) -> Self {
        let borrowed = Borrowed::<'a, T>::new(slice);
        unsafe { Self::from_sliced(borrowed) }
    }

    #[must_use]
    pub const fn from_inline(inline: InlineVec<T, InlineBytes>) -> Self {
        unsafe { transmute2(inline) }
    }

    #[must_use]
    pub(super) const unsafe fn from_sliced<O>(owned: Sliced<T, O>) -> Self {
        const {
            assert!(size_of::<O>() == size_of::<usize>());
        }
        unsafe { transmute2(owned) }
    }

    #[must_use]
    pub(crate) fn from_slice_clone(slice: &[T]) -> Self
    where
        T: Clone,
    {
        if slice.len() <= Self::INLINE_CAP {
            let inline = InlineVec::from_slice_clone(slice);
            Self::from_inline(inline)
        } else {
            let smart = SmartThinVec::from_slice_clone(slice);
            Self::from_smart_thin(smart)
        }
    }

    #[must_use]
    pub const fn from_smart_thin(v: SmartThinVec<T, B>) -> Self {
        let len = v.len();
        let ptr = v.as_ptr();

        #[cfg(debug_assertions)]
        let is_null = v.capacity() == 0;

        let owner = unsafe { v.into_repr() };
        let this = unsafe { Self::from_sliced(Sliced { owner, ptr, len }) };

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
        } else if self.is_borrowed() {
            // SAFETY: repr is checked above, the borrowed slice is copyable
            unsafe { self.copy() }
        } else {
            // SAFETY: repr is checked above
            let allocated = unsafe { self.as_allocated_unchecked() };
            if allocated.owner.counter().incr() == UpdateResult::Done {
                // SAFETY: the reference count was incremented
                unsafe { self.copy() }
            } else {
                Self::from_slice_clone(allocated.as_slice())
            }
        }
    }
}

type Allocated<T, B> = Sliced<T, Owner<T, B>>;

#[repr(transparent)]
struct Owner<T, B>(FatOrThinRepr<T, B>);

impl<T, B: Backend> Owner<T, B> {
    /// Drops the owner now.
    ///
    /// # Safety
    ///
    /// The owner must not be used after drop.
    unsafe fn drop(&mut self) {
        match self.0.into_split() {
            Variant::Thin(repr) => {
                // SAFETY: should not be used after drop
                let _ = unsafe { SmartThinVec::from_repr(repr) };
            }
            Variant::Fat(repr) => {
                // SAFETY: should not be used after drop
                let _ = unsafe { SmartFatVec::from_repr(repr) };
            }
        }
    }

    fn is_unique(&self) -> bool {
        self.0.as_ref().prefix.is_unique()
    }

    const fn is_fat(&self) -> bool {
        self.0.is_fat()
    }

    const fn is_thin(&self) -> bool {
        self.0.is_thin()
    }

    const fn counter(&self) -> &B {
        &self.0.as_ref().prefix
    }
}
