//! 3-word representation: inline, borrowed or heap, with O(1) slicing.
//!
//! ```text
//!            little endian: word 0 first          big endian: word 0 last
//! inline     [tagged len|data...][data][data]     bit 0 of word 0 = 1
//! sliced     [owner][slice ptr, slice len]        bits 1..0 of word 0 = 0b10
//! ```
//!
//! "Sliced" covers both borrowed (null owner) and heap values: the slice is
//! any subslice of the owned buffer, so slicing a heap value is O(1).

use alloc::vec::Vec;
use core::marker::PhantomData;
use core::mem::{MaybeUninit, offset_of, transmute};
use core::ptr::NonNull;

use super::owner::Owner;
use super::{Kind, Repr, capacity_overflow};
use crate::backend::Backend;
use crate::inline::base::Base as InlineBase;
use crate::inline::layouts::BasicLayout;
use crate::thin::TryReserveError;

type Inline<T> = InlineBase<T, BasicLayout>;

/// Raw 3 words; word 0 is never zero.
#[repr(C)]
#[derive(Clone, Copy)]
struct Pivot {
    #[cfg(target_endian = "little")]
    lsw: NonNull<()>,
    rest: [MaybeUninit<*mut ()>; 2],
    #[cfg(target_endian = "big")]
    lsw: NonNull<()>,
}

#[repr(C)]
struct Sliced<T: Copy + 'static, B: Backend> {
    #[cfg(target_endian = "little")]
    owner: Owner<T, B>,
    slice: NonNull<[T]>,
    #[cfg(target_endian = "big")]
    owner: Owner<T, B>,
}

impl<T: Copy + 'static, B: Backend> Copy for Sliced<T, B> {}
impl<T: Copy + 'static, B: Backend> Clone for Sliced<T, B> {
    fn clone(&self) -> Self {
        *self
    }
}

const _: () = {
    type S = Sliced<u8, crate::backend::Rc>;
    assert!(size_of::<Pivot>() == 3 * size_of::<usize>());
    assert!(size_of::<S>() == size_of::<Pivot>());
    assert!(size_of::<Inline<u8>>() == size_of::<Pivot>());
    assert!(offset_of!(S, owner) == offset_of!(Pivot, lsw));
};

/// 3-word copy-on-write sequence (see the module documentation).
#[repr(transparent)]
pub struct Wide<'a, T: Copy + 'static, B: Backend> {
    pivot: Pivot,
    marker: PhantomData<(&'a [T], Owner<T, B>)>,
}

const _: () = {
    type F = Wide<'static, u8, crate::backend::Rc>;
    assert!(size_of::<F>() == 3 * size_of::<usize>());
    assert!(size_of::<Option<F>>() == size_of::<F>());
};

// SAFETY: shared state is either immutable borrowed data or behind the
// backend's counter, which decides thread safety
unsafe impl<T: Copy + Send + Sync + 'static, B: Backend> Send for Wide<'_, T, B> where
    B::Counter: Send + Sync
{
}
// SAFETY: same as `Send`
unsafe impl<T: Copy + Send + Sync + 'static, B: Backend> Sync for Wide<'_, T, B> where
    B::Counter: Send + Sync
{
}

impl<'a, T: Copy + 'static, B: Backend> Wide<'a, T, B> {
    const fn from_inline(inline: Inline<T>) -> Self {
        Self {
            // SAFETY: same size, word 0 of an inline is tagged and non-zero
            pivot: unsafe { transmute::<Inline<T>, Pivot>(inline) },
            marker: PhantomData,
        }
    }

    const fn from_sliced(sliced: Sliced<T, B>) -> Self {
        Self {
            // SAFETY: same size, word 0 of a sliced is a tagged owner, non-zero
            pivot: unsafe { transmute::<Sliced<T, B>, Pivot>(sliced) },
            marker: PhantomData,
        }
    }

    #[inline]
    pub const fn new() -> Self {
        Self::from_inline(Inline::new())
    }

    /// Borrows a slice, in a const context too.
    ///
    /// Unlike the other representations, empty slices stay borrowed.
    #[inline]
    pub const fn borrowed(slice: &'a [T]) -> Self {
        Self::from_sliced(Sliced {
            owner: Owner::NONE,
            slice: NonNull::from_ref(slice),
        })
    }

    /// Copies `slice` inline, in a `const` context too.
    ///
    /// # Panics
    ///
    /// Panics if `slice` is longer than the inline capacity.
    #[inline]
    pub const fn inline_copy(slice: &[T]) -> Self {
        assert!(
            slice.len() <= Inline::<T>::CAPACITY,
            "too long to be inlined"
        );
        Self::from_inline(Inline::from_slice_copy(slice))
    }

    #[inline]
    pub const fn is_inline(&self) -> bool {
        super::word_bits(&self.pivot.lsw) & 1 == 1
    }

    #[inline]
    pub const fn is_borrowed(&self) -> bool {
        !self.is_inline() && self.sliced().owner.is_none()
    }

    #[inline]
    pub const fn is_heap(&self) -> bool {
        !self.is_inline() && self.sliced().owner.is_some()
    }

    /// The borrowed slice, with its full lifetime, if borrowed.
    #[inline]
    pub const fn borrowed_slice(&self) -> Option<&'a [T]> {
        if self.is_borrowed() {
            // SAFETY: borrowed case, the slice is valid for `'a`
            Some(unsafe { self.sliced().slice.as_ref() })
        } else {
            None
        }
    }

    #[inline]
    const fn inline(&self) -> &Inline<T> {
        debug_assert!(self.is_inline());
        // SAFETY: inline case, same size
        unsafe { transmute::<&Pivot, &Inline<T>>(&self.pivot) }
    }

    #[inline]
    const fn inline_mut(&mut self) -> &mut Inline<T> {
        debug_assert!(self.is_inline());
        // SAFETY: inline case, same size
        unsafe { transmute::<&mut Pivot, &mut Inline<T>>(&mut self.pivot) }
    }

    #[inline]
    const fn sliced(&self) -> &Sliced<T, B> {
        debug_assert!(!self.is_inline());
        // SAFETY: sliced case, same size
        unsafe { transmute::<&Pivot, &Sliced<T, B>>(&self.pivot) }
    }

    #[inline]
    const fn sliced_mut(&mut self) -> &mut Sliced<T, B> {
        debug_assert!(!self.is_inline());
        // SAFETY: sliced case, same size
        unsafe { transmute::<&mut Pivot, &mut Sliced<T, B>>(&mut self.pivot) }
    }

    #[inline]
    pub const fn as_slice(&self) -> &[T] {
        if self.is_inline() {
            self.inline().as_slice()
        } else {
            // SAFETY: type invariant, the slice is valid for `'a` or owned
            unsafe { self.sliced().slice.as_ref() }
        }
    }

    #[inline]
    pub const fn len(&self) -> usize {
        if self.is_inline() {
            self.inline().len()
        } else {
            self.sliced().slice.len()
        }
    }

    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// O(1) subslice sharing the same storage, copied if inline.
    ///
    /// # Panics
    ///
    /// Panics if the range is out of bounds.
    pub fn slice(&self, range: core::ops::Range<usize>) -> Self {
        let start = range.start;
        let sub = &self.as_slice()[range];
        if self.is_inline() || (self.is_heap() && sub.len() <= Inline::<T>::CAPACITY) {
            // inline, or a short slice of a heap value: copy inline (normalized)
            return Self::from_inline(Inline::from_slice_copy(sub));
        }
        // borrowed values stay borrowed, whatever the length
        let owner = self.sliced().owner;
        if owner.is_some() && owner.try_clone().is_none() {
            // the backend refuses sharing (e.g. unique): copy the subslice
            return <Self as Repr<'a, T>>::from_slice(sub);
        }
        // borrowed (valid for `'a`) or shared (one more reference taken);
        // derived from the stored raw pointer, not from `sub`: a pointer made
        // from a shared reference must not be written through later
        // SAFETY: `start..start + sub.len()` is in bounds (checked by indexing)
        let ptr = unsafe { self.sliced().slice.cast::<T>().add(start) };
        Self::from_sliced(Sliced {
            owner,
            slice: NonNull::slice_from_raw_parts(ptr, sub.len()),
        })
    }

    /// Copies `slice` to a new heap buffer; kept out of line so that the
    /// inline path of `from_slice` stays small enough to be inlined.
    #[inline(never)]
    fn heap_from_slice(slice: &[T]) -> Self {
        let owner = Owner::from_slice(slice);
        Self::from_sliced(Sliced {
            owner,
            slice: NonNull::slice_from_raw_parts(owner.data(), owner.len()),
        })
    }

    /// Offset of the slice in the owner's buffer.
    fn offset(sliced: &Sliced<T, B>) -> usize {
        // SAFETY: the slice lies within the owner's buffer
        let offset = unsafe { sliced.slice.cast::<T>().offset_from(sliced.owner.data()) };
        debug_assert!(offset >= 0);
        offset.cast_unsigned()
    }

    /// Moves the slice to the start of a unique owner's buffer.
    ///
    /// Makes the owner's length equal to the slice's.
    fn normalize(sliced: &mut Sliced<T, B>) {
        let owner = sliced.owner;
        let data = owner.data();
        let len = sliced.slice.len();
        if sliced.slice.cast::<T>() != data {
            // SAFETY: unique owner, the slice lies within its buffer
            unsafe { data.as_ptr().copy_from(sliced.slice.cast().as_ptr(), len) };
        }
        // SAFETY: unique owner, `len` elements initialized at the start
        unsafe { owner.set_len(len) };
        sliced.slice = NonNull::slice_from_raw_parts(data, len);
    }

    fn try_from_slice(slice: &[T], capacity: usize) -> Result<Self, TryReserveError> {
        debug_assert!(capacity >= slice.len());
        if capacity <= Inline::<T>::CAPACITY {
            return Ok(Self::from_inline(Inline::from_slice_copy(slice)));
        }
        let owner = Owner::<T, B>::try_with_capacity(capacity)?;
        // SAFETY: fresh unique owner with enough capacity
        unsafe {
            owner
                .data()
                .as_ptr()
                .copy_from_nonoverlapping(slice.as_ptr(), slice.len());
            owner.set_len(slice.len());
        }
        Ok(Self::from_sliced(Sliced {
            owner,
            slice: NonNull::slice_from_raw_parts(owner.data(), slice.len()),
        }))
    }
}

impl<T: Copy + 'static, B: Backend> Default for Wide<'_, T, B> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Copy + 'static, B: Backend> Clone for Wide<'_, T, B> {
    fn clone(&self) -> Self {
        if self.is_inline() || self.sliced().owner.is_none() {
            return Self {
                pivot: self.pivot,
                marker: PhantomData,
            };
        }
        match self.sliced().owner.try_clone() {
            Some(_) => Self {
                pivot: self.pivot,
                marker: PhantomData,
            },
            None => Self::from_slice(self.as_slice()),
        }
    }
}

impl<T: Copy + 'static, B: Backend> Drop for Wide<'_, T, B> {
    fn drop(&mut self) {
        if !self.is_inline() {
            let owner = self.sliced().owner;
            if owner.is_some() {
                // SAFETY: this handle is dropped
                unsafe { owner.release() };
            }
        }
    }
}

// SAFETY: see the trait's contract, upheld by `try_reserve`
unsafe impl<'a, T: Copy + 'static, B: Backend> Repr<'a, T> for Wide<'a, T, B> {
    type Owned = Wide<'static, T, B>;
    const WORDS: usize = 3;
    const INLINE_CAPACITY: usize = Inline::<T>::CAPACITY;
    const MAX_LEN: usize = isize::MAX as usize;
    const BORROWS: bool = true;

    #[inline]
    fn new() -> Self {
        Self::new()
    }

    #[inline]
    fn from_slice(slice: &[T]) -> Self {
        if slice.len() <= Inline::<T>::CAPACITY {
            Self::from_inline(Inline::from_slice_copy(slice))
        } else {
            Self::heap_from_slice(slice)
        }
    }

    #[inline]
    fn from_borrowed(slice: &'a [T]) -> Self {
        Self::borrowed(slice)
    }

    fn from_vec(vec: Vec<T>) -> Self {
        if vec.len() <= Inline::<T>::CAPACITY {
            Self::from_inline(Inline::from_slice_copy(&vec))
        } else {
            let owner = Owner::from_vec(vec);
            Self::from_sliced(Sliced {
                owner,
                slice: NonNull::slice_from_raw_parts(owner.data(), owner.len()),
            })
        }
    }

    fn into_owned(self) -> Self::Owned {
        if self.as_borrowed().is_some() {
            return <Self::Owned as Repr<'static, T>>::from_slice(self.as_slice());
        }
        let this = core::mem::ManuallyDrop::new(self);
        // SAFETY: not borrowed, so nothing depends on `'a`; same type otherwise
        unsafe { core::ptr::read((&raw const *this).cast::<Self::Owned>()) }
    }

    #[inline]
    fn as_borrowed(&self) -> Option<&'a [T]> {
        self.borrowed_slice()
    }

    fn kind(&self) -> Kind {
        if self.is_inline() {
            Kind::Inline
        } else if self.sliced().owner.is_none() {
            Kind::Borrowed
        } else {
            Kind::Heap(self.sliced().owner.kind())
        }
    }

    #[inline]
    fn as_slice(&self) -> &[T] {
        self.as_slice()
    }

    #[inline]
    fn len(&self) -> usize {
        self.len()
    }

    fn into_vec(self) -> Vec<T> {
        if !self.is_inline() {
            let sliced = *self.sliced();
            if sliced.owner.is_some()
                && sliced.owner.is_unique()
                && sliced.slice.cast() == sliced.owner.data()
            {
                let this = core::mem::ManuallyDrop::new(self);
                let mut vec = sliced.owner.into_vec();
                vec.truncate(this.len());
                return vec;
            }
        }
        self.as_slice().to_vec()
    }

    fn is_unique(&self) -> bool {
        if self.is_inline() {
            return true;
        }
        let owner = self.sliced().owner;
        owner.is_some() && owner.is_unique()
    }

    fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        let len = self.len();
        let required = len.checked_add(additional).ok_or(capacity_overflow())?;

        if self.is_inline() {
            if required > Inline::<T>::CAPACITY {
                *self = Self::try_from_slice(self.as_slice(), required)?;
            }
            return Ok(());
        }

        let sliced = self.sliced_mut();
        if sliced.owner.is_some() && sliced.owner.is_unique() {
            let offset = Self::offset(sliced);
            if offset + required <= sliced.owner.capacity() {
                // room after the slice: drop the owned tail, keep the slice in place
                // SAFETY: unique owner, the first `offset + len` elements are initialized
                unsafe { sliced.owner.set_len(offset + len) };
            } else {
                Self::normalize(sliced);
                if required > sliced.owner.capacity() {
                    // SAFETY: unique owner, the updated handle is stored back
                    unsafe { sliced.owner.try_grow(required)? };
                    sliced.slice = NonNull::slice_from_raw_parts(sliced.owner.data(), len);
                }
            }
        } else {
            // borrowed or shared: copy
            *self = Self::try_from_slice(self.as_slice(), required)?;
        }
        Ok(())
    }

    fn capacity(&self) -> usize {
        if self.is_inline() {
            Inline::<T>::CAPACITY
        } else {
            let sliced = self.sliced();
            if sliced.owner.is_some() {
                // writable from the start of the slice
                sliced.owner.capacity() - Self::offset(sliced)
            } else {
                0
            }
        }
    }

    fn shrink_view(&mut self, len: usize) -> bool {
        if self.is_inline() {
            return false;
        }
        let sliced = self.sliced_mut();
        sliced.slice = NonNull::slice_from_raw_parts(sliced.slice.cast(), len);
        true
    }

    unsafe fn as_mut_ptr(&mut self) -> *mut T {
        if self.is_inline() {
            self.inline_mut().as_mut_ptr()
        } else {
            self.sliced().slice.cast().as_ptr()
        }
    }

    unsafe fn set_len(&mut self, len: usize) {
        if self.is_inline() {
            // SAFETY: precondition
            unsafe { self.inline_mut().set_len(len) };
        } else {
            let sliced = self.sliced_mut();
            let offset = Self::offset(sliced);
            // SAFETY: precondition, unique owner
            unsafe { sliced.owner.set_len(offset + len) };
            sliced.slice = NonNull::slice_from_raw_parts(sliced.slice.cast(), len);
        }
    }
}
