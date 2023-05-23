//! Raw shared sequence of bytes

use std::mem::{size_of, ManuallyDrop, MaybeUninit};
use std::ops::Range;

use crate::{AllocatedBackend, ThreadSafe};

/// Maximal byte capacity of an inline [`HipStr`](super::HipStr) or [`HipByt`](super::HipByt).
///
/// *Unstable!* name and access path may change with backend evolution.
pub const INLINE_CAPACITY: usize = size_of::<Allocated<ThreadSafe>>() - 1;

/// Static string.
///
/// Warning!
/// For big-endian platform, the reserved word is **after** the data.
/// For little-endian platform, the reserved word is **before** the data.

#[derive(Clone, Copy)]
#[repr(C)]
struct Static {
    #[cfg(target_endian = "little")]
    reserved: usize,

    slice: &'static [u8],

    #[cfg(target_endian = "big")]
    reserved: usize,
}

impl Static {
    #[inline]
    const fn new(slice: &'static [u8]) -> Self {
        Self { slice, reserved: 0 }
    }

    #[inline]
    const fn empty() -> Self {
        Self::new(b"")
    }

    #[inline]
    const fn len(&self) -> usize {
        debug_assert!(self.is_valid(), "Static::len on an invalid representation");
        self.slice.len()
    }

    #[inline]
    const fn as_slice(&self) -> &'static [u8] {
        debug_assert!(
            self.is_valid(),
            "Static::as_slice on an invalid representation"
        );
        self.slice
    }

    /// Return `true` iff this representation is valid.
    #[inline]
    const fn is_valid(&self) -> bool {
        self.reserved == 0
    }
}

//// Inline string.
///
/// Warning!
/// For big-endian platform, the shifted length is **after** the data.
/// For little-endian platform, the shifted length is **before** the data.
#[derive(Clone, Copy)]
#[repr(C)]
struct Inline {
    #[cfg(target_endian = "little")]
    shifted_len: u8,

    data: [MaybeUninit<u8>; INLINE_CAPACITY],

    #[cfg(target_endian = "big")]
    shifted_len: u8,
}

impl Inline {
    /// Creates a new `Inline` string by copying a byte slice.
    #[inline]
    fn new(s: &[u8]) -> Self {
        let len = s.len();
        debug_assert!(len != 0);
        assert!(len <= INLINE_CAPACITY);

        let mut data: [MaybeUninit<u8>; INLINE_CAPACITY];
        unsafe {
            data = MaybeUninit::uninit().assume_init();
            std::ptr::copy_nonoverlapping(s.as_ptr(), data.as_mut_ptr().cast(), len);
        }

        #[allow(clippy::cast_possible_truncation)]
        let shifted_len = ((len << 1) | 1) as u8;

        #[allow(clippy::inconsistent_struct_constructor)]
        Self { data, shifted_len }
    }

    /// Returns the length of this inline string.
    #[inline]
    const fn len(&self) -> usize {
        debug_assert!(self.is_valid(), "Inline::len on an invalid representation");

        (self.shifted_len >> 1) as usize
    }

    /// Returns an immutable view of this `Inline` string.
    #[inline]
    const fn as_slice(&self) -> &[u8] {
        debug_assert!(
            self.is_valid(),
            "Inline::as_slice on an invalid representation"
        );

        // waiting for const_slice_index
        let data = self.data.as_ptr();
        let len = self.len();

        // SAFETY: type invariant
        unsafe { std::slice::from_raw_parts(data.cast(), len) }
    }

    /// Returns a mutable view of this `Inline` string.
    #[inline]
    fn as_mut_slice(&mut self) -> &mut [u8] {
        debug_assert!(
            self.is_valid(),
            "Inline::as_mut_slice on an invalid representation"
        );

        let len = self.len();
        unsafe { std::slice::from_raw_parts_mut(self.data.as_mut_ptr().cast(), len) }
    }

    /// Return `true` iff this representation is valid.
    #[inline]
    const fn is_valid(&self) -> bool {
        (self.shifted_len & 1) != 0
    }

    #[inline]
    const fn capacity() -> usize {
        INLINE_CAPACITY
    }
}

#[cfg(target_endian = "big")]
#[derive(Copy)]
#[repr(C)]
struct Allocated<B: AllocatedBackend> {
    ptr: *const u8,
    len: usize,
    owner: B::RawPointer,
}

#[cfg(target_endian = "little")]
#[repr(C)]
struct Allocated<B: AllocatedBackend> {
    owner: B::RawPointer,
    ptr: *const u8,
    len: usize,
}

impl<B: AllocatedBackend> Copy for Allocated<B> {}

impl<B: AllocatedBackend> Clone for Allocated<B> {
    fn clone(&self) -> Self {
        *self
    }
}

unsafe impl<B: AllocatedBackend + Sync> Sync for Allocated<B> {}

unsafe impl<B: AllocatedBackend + Send> Send for Allocated<B> {}

impl<B: AllocatedBackend> Allocated<B> {
    const _ASSERTS: () = {
        assert!(size_of::<B::RawPointer>() == size_of::<usize>());
    };

    /// Creates an allocated from a vector.
    ///
    /// Takes ownership of the vector without copying the data.
    #[inline]
    fn new(v: Vec<u8>) -> Self {
        let ptr = v.as_ptr();
        let len = v.len();
        let owner = B::new_raw(v);

        #[allow(clippy::inconsistent_struct_constructor)]
        Self { ptr, len, owner }
    }

    /// Returns the length of this allocated string.
    #[inline]
    const fn len(&self) -> usize {
        // debug_assert!(self.is_valid()); // is_valid is not const!

        self.len
    }

    /// Returns as a byte slice.
    #[inline]
    const fn as_slice(&self) -> &[u8] {
        // debug_assert!(self.is_valid()); // is_valid is not const!

        // SAFETY: Type invariant
        unsafe { std::slice::from_raw_parts(self.ptr, self.len) }
    }

    /// Returns a mutable slice if possible (unique non-static reference).
    #[inline]
    fn as_mut_slice(&mut self) -> Option<&mut [u8]> {
        debug_assert!(
            self.is_valid(),
            "Inline::as_mut_slice on invalid representation"
        );

        // SAFETY: if this reference is unique, no one else can "see" the string
        if unsafe { B::is_unique(self.owner) } {
            Some(unsafe { std::slice::from_raw_parts_mut(self.ptr as *mut u8, self.len) })
        } else {
            None
        }
    }

    /// Creates a new `Allocated` for some range with the same owner.
    #[inline]
    fn slice(&self, range: Range<usize>) -> Self {
        debug_assert!(self.is_valid(), "Inline::slice on invalid representation");
        debug_assert!(self.is_valid());
        assert!(range.start <= self.len);
        assert!(range.end <= self.len);
        self.incr_ref_count();
        let ptr = unsafe { self.ptr.add(range.start) };
        Self {
            ptr,
            len: range.len(),
            owner: self.owner,
        }
    }

    /// Gets a reference to the vector.
    fn vec_ref(&self) -> &Vec<u8> {
        unsafe { B::vec_ref(self.owner) }
    }

    /// Increments the reference count.
    #[inline]
    fn incr_ref_count(&self) {
        debug_assert!(
            self.is_valid(),
            "Inline::incr_ref_count on invalid representation"
        );
        debug_assert!(self.is_valid());
        unsafe { B::increment_count(self.owner) };
    }

    /// Decrements the reference count.
    #[inline]
    fn decr_ref_count(self) {
        debug_assert!(
            self.is_valid(),
            "Inline::decr_ref_count on invalid representation"
        );
        debug_assert!(self.is_valid());
        unsafe { B::decrement_count(self.owner) };
    }

    /// Return `true` iff this representation is valid.
    #[inline]
    fn is_valid(&self) -> bool {
        B::is_valid(self.owner)
    }

    #[inline]
    fn try_into_vec(self) -> Result<Vec<u8>, Self> {
        unsafe { B::try_unwrap(self.owner) }.map_err(|owner| Self { owner, ..self })
    }
}

/// Raw immutable byte sequence.
#[repr(C)]
pub union Raw<B: AllocatedBackend> {
    inline: Inline,
    allocated: Allocated<B>,
    static_: Static,
}

enum RawSplit<'a, B: AllocatedBackend> {
    Inline(&'a Inline),
    Allocated(&'a Allocated<B>),
    Static(&'a Static),
}

impl<B: AllocatedBackend> Raw<B> {
    const _ASSERTS: () = {
        assert!(size_of::<Inline>() == size_of::<Allocated<B>>());
        assert!(size_of::<Inline>() == size_of::<Static>());
        assert!(size_of::<*mut Vec<u8>>() == size_of::<usize>());
    };

    /// Creates a new empty `Raw`.
    #[inline]
    pub const fn empty() -> Self {
        Self {
            static_: Static::empty(),
        }
    }

    /// Creates a new `Raw` from a static slice.
    #[inline]
    pub const fn from_static(bytes: &'static [u8]) -> Self {
        Self {
            static_: Static::new(bytes),
        }
    }

    /// Creates a new `Raw` from a vector.
    #[inline]
    pub fn from_vec(vec: Vec<u8>) -> Self {
        Self {
            allocated: Allocated::new(vec),
        }
    }

    /// Creates a new `Raw` from a slice.
    #[inline]
    pub fn from_slice(bytes: &[u8]) -> Self {
        let len = bytes.len();
        if len == 0 {
            Self::empty()
        } else if len <= INLINE_CAPACITY {
            Self {
                inline: Inline::new(bytes),
            }
        } else {
            Self {
                allocated: Allocated::new(bytes.to_vec()),
            }
        }
    }

    /// Splits this raw into its possible representation.
    #[inline]
    const fn split(&self) -> RawSplit<B> {
        // SAFETY: type invariant, see is_inline & is_static
        if self.is_inline() {
            RawSplit::Inline(unsafe { &self.inline })
        } else if self.is_static() {
            RawSplit::Static(unsafe { &self.static_ })
        } else {
            debug_assert!(self.is_allocated());
            RawSplit::Allocated(unsafe { &self.allocated })
        }
    }

    #[inline]
    pub const fn is_inline(&self) -> bool {
        // SAFETY: if self is not inline, shifted_len corresponds to the
        // lower byte of the owner and must have an alignment > 1
        unsafe { self.inline.is_valid() }
    }

    #[inline]
    pub const fn is_static(&self) -> bool {
        // SAFETY:
        // * If self is inline, the shifted length plus one is in reserved and will be non null.
        // * If self is allocated, the reinterpretation of the owner will be non null too.
        unsafe {
            !self.inline.is_valid() // required for miri, compiled away!
            && self.static_.is_valid()
        }
    }

    #[inline]
    pub const fn is_allocated(&self) -> bool {
        !self.is_inline() && !self.is_static()
    }

    #[inline]
    pub fn into_static(self) -> Result<&'static [u8], Self> {
        if self.is_static() {
            let this = ManuallyDrop::new(self);
            Ok(unsafe { this.static_.slice })
        } else {
            Err(self)
        }
    }

    #[inline]
    pub const fn len(&self) -> usize {
        match self.split() {
            RawSplit::Inline(inline) => inline.len(),
            RawSplit::Allocated(heap) => heap.len(),
            RawSplit::Static(static_) => static_.len(),
        }
    }

    #[inline]
    pub const fn as_slice(&self) -> &[u8] {
        match self.split() {
            RawSplit::Inline(inline) => inline.as_slice(),
            RawSplit::Allocated(heap) => heap.as_slice(),
            RawSplit::Static(static_) => static_.as_slice(),
        }
    }

    pub fn slice(&self, range: Range<usize>) -> Self {
        if range.is_empty() {
            return Self::from_static(b"");
        }

        match self.split() {
            RawSplit::Inline(inline) => {
                assert!(range.len() < inline.len());
                Self {
                    inline: Inline::new(&inline.as_slice()[range]),
                }
            }
            RawSplit::Static(static_) => Self::from_static(&static_.slice[range]),
            RawSplit::Allocated(allocated) => Self {
                allocated: allocated.slice(range),
            },
        }
    }

    #[inline]
    pub fn as_mut_slice(&mut self) -> Option<&mut [u8]> {
        if self.is_inline() {
            Some(unsafe { &mut self.inline }.as_mut_slice())
        } else if self.is_allocated() {
            unsafe { &mut self.allocated }.as_mut_slice()
        } else {
            None
        }
    }

    #[inline]
    pub const fn inline_capacity() -> usize {
        Inline::capacity()
    }

    #[inline]
    pub fn capacity(&self) -> usize {
        if self.is_inline() {
            Self::inline_capacity()
        } else if self.is_static() {
            // provide something to simplify the API
            self.len()
        } else {
            unsafe { &self.allocated }.vec_ref().capacity()
        }
    }

    #[inline]
    pub fn into_vec(mut self) -> Result<Vec<u8>, Self> {
        if let Some(allocated) = self.take_allocated() {
            allocated.try_into_vec().map_err(|allocated| Self { allocated })
        } else {
            Err(self)
        }
    }

    fn take_allocated(&mut self) -> Option<Allocated<B>> {
        if self.is_allocated() {
            let old = ManuallyDrop::new(std::mem::replace(self, Self::empty()));
            Some(unsafe { old.allocated })
        } else {
            None
        }
    }
}

impl<B: AllocatedBackend> Drop for Raw<B> {
    #[inline]
    fn drop(&mut self) {
        // Formally drops this `Raw` decreasing the ref count if needed
        if let Some(allocated) = self.take_allocated() {
            allocated.decr_ref_count();
        }
    }
}

impl<B: AllocatedBackend> Clone for Raw<B> {
    fn clone(&self) -> Self {
        // Duplicates this `Raw` increasing the ref count if needed.
        match self.split() {
            RawSplit::Inline(&inline) => Self { inline },
            RawSplit::Static(&static_) => Self { static_ },
            RawSplit::Allocated(&allocated) => {
                allocated.incr_ref_count();
                Self { allocated }
            }
        }
    }
}
