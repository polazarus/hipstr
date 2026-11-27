//! 2-word representation: inline, borrowed or heap, without slicing.
//!
//! ```text
//!            little endian            big endian
//! inline     [data...][data|len]      [len|data][data...]   top bits of "len word" = 0b11
//! heap       [owner][0b10 | len]      [0b10 | len][owner]
//! borrowed   [ptr][len]               [len][ptr]            top bit of "len word" = 0
//! ```
//!
//! The discriminant lives in the two most significant bits of the length word
//! because a borrowed pointer may be unaligned (e.g. to `u8`) and cannot carry
//! a tag. Consequences:
//!
//! - heap values hold at most `2^(usize::BITS - 2) - 1` elements;
//! - borrowed values hold at most `isize::MAX` elements (any real slice of a
//!   non-zero-sized type);
//! - the length word is never zero (empty values are inline), which gives
//!   `Option<Small>` a niche.

use alloc::vec::Vec;
use core::marker::PhantomData;
use core::mem::{MaybeUninit, offset_of, transmute};
use core::num::NonZeroUsize;
use core::ptr::NonNull;

use super::owner::Owner;
use super::{Kind, Repr, capacity_overflow};
use crate::backend::Backend;
use crate::thin::TryReserveError;

type Inline = crate::inline_buf::Small;

const SHIFT: u32 = usize::BITS - 2;
const TAG_MASK: usize = 0b11 << SHIFT;
const HEAP_TAG: usize = 0b10 << SHIFT;
const LEN_MASK: usize = !TAG_MASK;

/// Maximal heap length.
pub const MAX_HEAP_LEN: usize = LEN_MASK;
/// Maximal borrowed length.
pub const MAX_BORROWED_LEN: usize = usize::MAX >> 1;

/// Raw 2 words; the length word is never zero.
#[repr(C)]
#[derive(Clone, Copy)]
struct Pivot {
    #[cfg(target_endian = "big")]
    msw: NonZeroUsize,
    w0: MaybeUninit<*mut ()>,
    #[cfg(target_endian = "little")]
    msw: NonZeroUsize,
}

/// Heap or borrowed view: a pointer-sized word and the length word.
#[repr(C)]
struct Split<W: Copy> {
    #[cfg(target_endian = "big")]
    msw: usize,
    w0: W,
    #[cfg(target_endian = "little")]
    msw: usize,
}

impl<W: Copy> Copy for Split<W> {}
impl<W: Copy> Clone for Split<W> {
    fn clone(&self) -> Self {
        *self
    }
}

type Heap<B> = Split<Owner<B>>;
type Borrowed = Split<NonNull<u8>>;

const _: () = {
    type H = Heap<crate::backend::Rc>;
    assert!(size_of::<Pivot>() == 2 * size_of::<usize>());
    assert!(size_of::<H>() == size_of::<Pivot>());
    assert!(size_of::<Borrowed>() == size_of::<Pivot>());
    assert!(size_of::<Inline>() == size_of::<Pivot>());
    assert!(offset_of!(H, msw) == offset_of!(Pivot, msw));
    assert!(offset_of!(Borrowed, msw) == offset_of!(Pivot, msw));
};

/// 2-word copy-on-write sequence (see the module documentation).
#[repr(transparent)]
pub struct Small<'a, B: Backend> {
    pivot: Pivot,
    marker: PhantomData<(&'a [u8], Owner<B>)>,
}

const _: () = {
    type P = Small<'static, crate::backend::Rc>;
    assert!(size_of::<P>() == 2 * size_of::<usize>());
    assert!(size_of::<Option<P>>() == size_of::<P>());
};

// SAFETY: see `Wide`
unsafe impl<B: Backend> Send for Small<'_, B> where B::Counter: Send + Sync {}
// SAFETY: see `Wide`
unsafe impl<B: Backend> Sync for Small<'_, B> where B::Counter: Send + Sync {}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Tag {
    Inline,
    Heap,
    Borrowed,
}

impl<'a, B: Backend> Small<'a, B> {
    const fn from_inline(inline: Inline) -> Self {
        Self {
            // SAFETY: same size, the length word of an inline is tagged 0b11
            pivot: unsafe { transmute::<Inline, Pivot>(inline) },
            marker: PhantomData,
        }
    }

    const fn from_heap(owner: Owner<B>, len: usize) -> Self {
        debug_assert!(len <= MAX_HEAP_LEN);
        let heap = Heap {
            w0: owner,
            msw: HEAP_TAG | len,
        };
        Self {
            // SAFETY: same size, the length word is tagged 0b10, non-zero
            pivot: unsafe { transmute::<Heap<B>, Pivot>(heap) },
            marker: PhantomData,
        }
    }

    #[inline]
    pub const fn new() -> Self {
        Self::from_inline(Inline::new())
    }

    /// Borrows a slice, in a const context too.
    ///
    /// # Panics
    ///
    /// Panics if the slice is longer than [`MAX_BORROWED_LEN`], which is only
    /// possible for zero-sized types.
    #[inline]
    pub const fn borrowed(slice: &'a [u8]) -> Self {
        if slice.is_empty() {
            return Self::new();
        }
        assert!(slice.len() <= MAX_BORROWED_LEN, "borrowed slice too long");
        let borrowed = Borrowed {
            w0: NonNull::from_ref(slice).cast::<u8>(),
            msw: slice.len(),
        };
        Self {
            // SAFETY: same size, the length word is non-zero with a clear top bit
            pivot: unsafe { transmute::<Borrowed, Pivot>(borrowed) },
            marker: PhantomData,
        }
    }

    #[inline]
    const fn tag(&self) -> Tag {
        match self.pivot.msw.get() >> SHIFT {
            0b11 => Tag::Inline,
            0b10 => Tag::Heap,
            _ => Tag::Borrowed,
        }
    }

    /// Copies `slice` inline, in a `const` context too.
    ///
    /// # Panics
    ///
    /// Panics if `slice` is longer than the inline capacity.
    #[inline]
    pub const fn inline_copy(slice: &[u8]) -> Self {
        assert!(slice.len() <= Inline::CAPACITY, "too long to be inlined");
        Self::from_inline(Inline::from_slice_copy(slice))
    }

    #[inline]
    pub const fn is_inline(&self) -> bool {
        matches!(self.tag(), Tag::Inline)
    }

    #[inline]
    pub const fn is_borrowed(&self) -> bool {
        matches!(self.tag(), Tag::Borrowed)
    }

    #[inline]
    pub const fn is_heap(&self) -> bool {
        matches!(self.tag(), Tag::Heap)
    }

    /// The borrowed slice, with its full lifetime, if borrowed.
    #[inline]
    pub const fn borrowed_slice(&self) -> Option<&'a [u8]> {
        if self.is_borrowed() {
            let borrowed = self.borrowed_view();
            // SAFETY: borrowed case, valid for `'a`
            Some(unsafe { core::slice::from_raw_parts(borrowed.w0.as_ptr(), borrowed.msw) })
        } else {
            None
        }
    }

    #[inline]
    const fn inline(&self) -> &Inline {
        // SAFETY: inline case, same size
        unsafe { transmute::<&Pivot, &Inline>(&self.pivot) }
    }

    #[inline]
    const fn inline_mut(&mut self) -> &mut Inline {
        // SAFETY: inline case, same size
        unsafe { transmute::<&mut Pivot, &mut Inline>(&mut self.pivot) }
    }

    #[inline]
    const fn heap(&self) -> &Heap<B> {
        // SAFETY: heap case, same size
        unsafe { transmute::<&Pivot, &Heap<B>>(&self.pivot) }
    }

    #[inline]
    const fn heap_mut(&mut self) -> &mut Heap<B> {
        // SAFETY: heap case, same size
        unsafe { transmute::<&mut Pivot, &mut Heap<B>>(&mut self.pivot) }
    }

    #[inline]
    const fn borrowed_view(&self) -> &Borrowed {
        // SAFETY: borrowed case, same size
        unsafe { transmute::<&Pivot, &Borrowed>(&self.pivot) }
    }

    #[inline]
    pub const fn len(&self) -> usize {
        match self.tag() {
            Tag::Inline => self.inline().len(),
            Tag::Heap => self.pivot.msw.get() & LEN_MASK,
            // the whole word (top bit clear): borrowed lengths may use the
            // bit below it, part of the tag for heap lengths
            Tag::Borrowed => self.pivot.msw.get(),
        }
    }

    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    pub const fn as_slice(&self) -> &[u8] {
        match self.tag() {
            Tag::Inline => self.inline().as_slice(),
            Tag::Heap => {
                let heap = self.heap();
                let len = heap.msw & LEN_MASK;
                // SAFETY: type invariant, `len` initialized owned elements
                unsafe { core::slice::from_raw_parts(heap.w0.data().as_ptr(), len) }
            }
            Tag::Borrowed => {
                let borrowed = self.borrowed_view();
                // SAFETY: type invariant, borrowed for `'a`
                unsafe { core::slice::from_raw_parts(borrowed.w0.as_ptr(), borrowed.msw) }
            }
        }
    }

    /// Copies `slice` to a new heap buffer; kept out of line so that the
    /// inline path of `from_slice` stays small enough to be inlined.
    #[inline(never)]
    fn heap_from_slice(slice: &[u8]) -> Self {
        crate::thin::unwrap_or_oom(Self::try_from_slice(slice, slice.len()))
    }

    fn try_from_slice(slice: &[u8], capacity: usize) -> Result<Self, TryReserveError> {
        debug_assert!(capacity >= slice.len());
        if capacity <= Inline::CAPACITY {
            return Ok(Self::from_inline(Inline::from_slice_copy(slice)));
        }
        if capacity > MAX_HEAP_LEN {
            return Err(capacity_overflow());
        }
        let owner = Owner::<B>::try_with_capacity(capacity)?;
        // SAFETY: fresh unique owner with enough capacity
        unsafe {
            owner
                .data()
                .as_ptr()
                .copy_from_nonoverlapping(slice.as_ptr(), slice.len());
            owner.set_len(slice.len());
        }
        Ok(Self::from_heap(owner, slice.len()))
    }
}

impl<B: Backend> Default for Small<'_, B> {
    fn default() -> Self {
        Self::new()
    }
}

impl<B: Backend> Clone for Small<'_, B> {
    fn clone(&self) -> Self {
        if self.tag() == Tag::Heap && self.heap().w0.try_clone().is_none() {
            return Self::from_slice(self.as_slice());
        }
        Self {
            pivot: self.pivot,
            marker: PhantomData,
        }
    }
}

impl<B: Backend> Drop for Small<'_, B> {
    fn drop(&mut self) {
        if self.tag() == Tag::Heap {
            // SAFETY: this handle is dropped
            unsafe { self.heap().w0.release() };
        }
    }
}

// SAFETY: see the trait's contract, upheld by `try_reserve`
unsafe impl<'a, B: Backend> Repr<'a> for Small<'a, B> {
    type Owned = Small<'static, B>;
    const WORDS: usize = 2;
    const INLINE_CAPACITY: usize = Inline::CAPACITY;
    const MAX_LEN: usize = MAX_HEAP_LEN;
    const BORROWS: bool = true;

    #[inline]
    fn new() -> Self {
        Self::new()
    }

    #[inline]
    fn from_slice(slice: &[u8]) -> Self {
        if slice.len() <= Inline::CAPACITY {
            Self::from_inline(Inline::from_slice_copy(slice))
        } else {
            Self::heap_from_slice(slice)
        }
    }

    #[inline]
    fn from_borrowed(slice: &'a [u8]) -> Self {
        Self::borrowed(slice)
    }

    fn from_vec(vec: Vec<u8>) -> Self {
        if vec.len() <= Inline::CAPACITY || vec.len() > MAX_HEAP_LEN {
            // the second case panics with a capacity overflow
            Self::from_slice(&vec)
        } else {
            let len = vec.len();
            Self::from_heap(Owner::from_vec(vec), len)
        }
    }

    fn into_owned(self) -> Self::Owned {
        if self.tag() == Tag::Borrowed {
            return <Self::Owned as Repr<'static>>::from_slice(self.as_slice());
        }
        let this = core::mem::ManuallyDrop::new(self);
        // SAFETY: not borrowed, so nothing depends on `'a`; same type otherwise
        unsafe { core::ptr::read((&raw const *this).cast::<Self::Owned>()) }
    }

    #[inline]
    fn as_borrowed(&self) -> Option<&'a [u8]> {
        self.borrowed_slice()
    }

    fn kind(&self) -> Kind {
        match self.tag() {
            Tag::Inline => Kind::Inline,
            Tag::Heap => Kind::Heap(self.heap().w0.kind()),
            Tag::Borrowed => Kind::Borrowed,
        }
    }

    #[inline]
    fn as_slice(&self) -> &[u8] {
        self.as_slice()
    }

    #[inline]
    fn len(&self) -> usize {
        self.len()
    }

    fn into_vec(self) -> Vec<u8> {
        if self.tag() == Tag::Heap {
            let len = self.len();
            let this = core::mem::ManuallyDrop::new(self);
            // the view may be shorter than the owned buffer
            let mut vec = this.heap().w0.into_vec();
            vec.truncate(len);
            return vec;
        }
        self.as_slice().to_vec()
    }

    fn is_unique(&self) -> bool {
        match self.tag() {
            Tag::Inline => true,
            Tag::Heap => self.heap().w0.is_unique(),
            Tag::Borrowed => false,
        }
    }

    fn try_reserve_with(&mut self, additional: usize, exact: bool) -> Result<(), TryReserveError> {
        let len = self.len();
        let required = len.checked_add(additional).ok_or(capacity_overflow())?;
        match self.tag() {
            Tag::Inline if required <= Inline::CAPACITY => {}
            Tag::Heap if self.heap().w0.is_unique() => {
                if required > MAX_HEAP_LEN {
                    return Err(capacity_overflow());
                }
                let heap = self.heap_mut();
                // the view may be shorter than the owned buffer: drop the tail
                // SAFETY: unique owner, the first `len` elements are initialized
                unsafe { heap.w0.set_len(len) };
                if required > heap.w0.capacity() {
                    // SAFETY: unique owner, the updated handle is stored back
                    unsafe { heap.w0.try_grow(required, exact)? };
                }
            }
            _ => *self = Self::try_from_slice(self.as_slice(), required)?,
        }
        Ok(())
    }

    fn shrink_view(&mut self, len: usize) -> bool {
        match self.tag() {
            Tag::Inline => false,
            // each handle has its own length word: shrinking the view is O(1)
            Tag::Heap => {
                self.heap_mut().msw = HEAP_TAG | len;
                true
            }
            Tag::Borrowed => {
                debug_assert!(len > 0, "empty values are inline");
                // SAFETY: same layout, the length word stays non-zero (len > 0)
                unsafe { transmute::<&mut Pivot, &mut Borrowed>(&mut self.pivot) }.msw = len;
                true
            }
        }
    }

    fn capacity(&self) -> usize {
        match self.tag() {
            Tag::Inline => Inline::CAPACITY,
            // no more than the length word can hold (an adopted vector, or a
            // geometric growth, may have more on 32-bit targets)
            Tag::Heap => {
                let capacity = self.heap().w0.capacity();
                if capacity > MAX_HEAP_LEN {
                    MAX_HEAP_LEN
                } else {
                    capacity
                }
            }
            Tag::Borrowed => 0,
        }
    }

    unsafe fn as_mut_ptr(&mut self) -> *mut u8 {
        match self.tag() {
            Tag::Inline => self.inline_mut().as_mut_ptr(),
            Tag::Heap => self.heap().w0.data().as_ptr(),
            Tag::Borrowed => unreachable!("borrowed after reserve"),
        }
    }

    unsafe fn set_len(&mut self, len: usize) {
        match self.tag() {
            // SAFETY: precondition
            Tag::Inline => unsafe { self.inline_mut().set_len(len) },
            Tag::Heap => {
                // the tag must survive (precondition: `len <= capacity()`)
                debug_assert!(len <= MAX_HEAP_LEN);
                let heap = self.heap_mut();
                // SAFETY: precondition, unique owner
                unsafe { heap.w0.set_len(len) };
                heap.msw = HEAP_TAG | len;
            }
            Tag::Borrowed => unreachable!("borrowed after reserve"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::backend::Rc;

    type S = Small<'static, Rc>;

    #[test]
    #[allow(clippy::clone_on_copy, reason = "covers the impl")]
    fn accessors() {
        let split = Split { msw: 1, w0: 2u8 };
        assert_eq!(split.clone().w0, 2);
        assert!(S::default().is_empty());
        assert!(!S::from_slice(b"ab").is_empty());
        assert_eq!(S::from_slice(b"ab").borrowed_slice(), None);
        assert_eq!(S::borrowed(b"ab").borrowed_slice(), Some(&b"ab"[..]));
    }

    /// A borrowed length with the bit below the top one set (≥ 1 GiB on
    /// 32-bit targets): that bit belongs to the length, not to a tag.
    #[test]
    fn long_borrowed_len() {
        let len = (1 << SHIFT) + 5;
        assert!(len <= MAX_BORROWED_LEN);
        let borrowed = Borrowed {
            w0: NonNull::dangling(),
            msw: len,
        };
        // only the words are read, never the bytes
        let s = S {
            // SAFETY: same layout, non-zero length word
            pivot: unsafe { transmute::<Borrowed, Pivot>(borrowed) },
            marker: PhantomData,
        };
        assert!(s.is_borrowed());
        assert_eq!(s.len(), len);
        assert!(!s.is_empty());
    }

    /// A heap capacity beyond what the length word holds (an adopted vector
    /// on 32-bit targets) is reported clamped.
    #[test]
    fn huge_capacity_is_clamped() {
        // a fake vector header on the stack, never dereferenced as bytes
        let mut header = super::super::owner::VecHeader::<Rc> {
            prefix: crate::backend::Count(core::cell::Cell::new(0)),
            ptr: Some(NonNull::dangling()),
            cap: usize::MAX >> 1,
            len: 100,
        };
        let owner = Owner::<Rc>::from_header_for_tests(NonNull::from(&mut header));
        let s = core::mem::ManuallyDrop::new(S::from_heap(owner, 100));
        assert!(s.is_heap());
        assert_eq!(s.capacity(), MAX_HEAP_LEN.min(usize::MAX >> 1));
    }

    // the contract excludes these (a reserve unborrows): checked anyway

    #[test]
    #[should_panic(expected = "borrowed after reserve")]
    fn borrowed_as_mut_ptr() {
        let mut s = S::borrowed(b"ab");
        let _ = unsafe { s.as_mut_ptr() };
    }

    #[test]
    #[should_panic(expected = "borrowed after reserve")]
    fn borrowed_set_len() {
        let mut s = S::borrowed(b"ab");
        unsafe { s.set_len(1) };
    }
}
