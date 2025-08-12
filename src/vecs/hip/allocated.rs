use alloc::vec::Vec;
use core::marker::PhantomData;
use core::mem::{offset_of, transmute, ManuallyDrop, MaybeUninit};
use core::num::NonZeroUsize;
use core::ops::{Deref, DerefMut, Range};
use core::ptr::{null_mut, NonNull};
use core::slice::from_raw_parts;
use std::boxed::Box;

use self::sealed::Sealed;
use crate::common::traits::{MutVector, Vector};
use crate::vecs::thin::ThinVec;
use crate::vecs::{Smart, SmartThinVec, ThinVec};
use crate::Backend;

const TAG_MASK: usize = super::super::TAG_MASK as usize;
const TAG_FAT: usize = super::super::TAG_FAT as usize;
const TAG_THIN: usize = super::super::TAG_THIN as usize;

pub type Thin<T, B> = Allocated<SmartThinVec<T, B>, T, TAG_THIN, TAG_MASK>;
pub type Fat<T, B> = Allocated<Smart<Vec<T>, B>, T, TAG_FAT, TAG_MASK>;
#[repr(C)]
pub struct Allocated<O: VecPtr<T>, T, const TAG: usize, const MASK: usize> {
    pub owner: TaggedOwner<T, O, TAG, MASK>,
    pub ptr: *const T,
    pub len: usize,
}

impl<O: VecPtr<T>, T, const TAG: usize, const MASK: usize> Allocated<O, T, TAG, MASK> {
    pub fn new(owner: O, ptr: *const T, len: usize) -> Self {
        let owner = TaggedOwner::new(owner.into_raw());
        Self { owner, ptr, len }
    }

    pub fn with_mut<R>(&mut self, f: impl FnOnce(&mut O, &Range<usize>) -> R) -> R {
        self.owner.with_mut(|o| {
            // Get the current range of the slice
            let range = unsafe {
                o.subslice_range(core::slice::from_raw_parts(self.ptr, self.len))
                    .unwrap_unchecked()
            };

            // Compute the mutation
            let result = f(o, &range);

            // Update the pointer and length based on the new range
            self.ptr = unsafe { o.ptr().add(range.start) };
            self.len = range.end - range.start;

            result
        })
    }

    pub(crate) fn range(&self) -> Range<usize> {
        let o = self.owner.get();
        unsafe {
            o.subslice_range(core::slice::from_raw_parts(self.ptr, self.len))
                .unwrap_unchecked()
        }
    }

    /// Returns a mutable reference to the underlying vector.
    ///
    /// # Safety
    ///
    /// - Should be unique
    /// - Do not use if the modification requires a change in the pointer
    pub(crate) unsafe fn mut_vector(&mut self) -> &mut (impl MutVector<Item = T> + '_) {
        let r: &mut O = unsafe { self.owner.untagged().cast().as_mut() };
        r.as_mut_unchecked()
    }
}

#[repr(transparent)]
pub struct TaggedOwner<T, O: VecPtr<T>, const TAG: usize, const MASK: usize>(
    NonNull<()>,
    PhantomData<(O, [T])>,
);

impl<T, O: VecPtr<T>, const TAG: usize, const MASK: usize> TaggedOwner<T, O, TAG, MASK> {
    fn new(ptr: NonNull<()>) -> Self {
        Self(
            ptr.map_addr(|addr| {
                debug_assert!(addr.get() & MASK == 0);
                unsafe { NonZeroUsize::new_unchecked(addr.get() | TAG) }
            }),
            PhantomData,
        )
    }

    const fn untagged(&self) -> NonNull<()> {
        // map_addr is not const
        unsafe { self.0.sub(TAG) }
    }

    pub const fn get(&self) -> Ref<'_, O> {
        Ref(self.untagged(), PhantomData)
    }

    pub fn with_mut<F: FnOnce(&mut O) -> R, R>(&mut self, f: F) -> R {
        unsafe fn transmute_ref_mut<O>(ptr: &mut NonNull<()>) -> &mut O {
            unsafe { transmute::<&mut NonNull<()>, &mut O>(ptr) }
        }

        let mut ptr = self.untagged();
        let backup = ptr;
        let ref_mut = unsafe { transmute_ref_mut(&mut ptr) };

        let result = f(ref_mut);
        if O::PTR_CHANGE && ptr != backup {
            self.0 = ptr.map_addr(|addr| {
                debug_assert!(addr.get() & MASK == 0);
                unsafe { NonZeroUsize::new_unchecked(addr.get() | TAG) }
            });
        }
        result
    }

    pub(crate) const fn into_untagged(self) -> O {
        let untagged = self.untagged();
        std::mem::forget(self);
        assert!(size_of::<O>() == size_of::<NonNull<()>>(), "size mismatch");
        union Tr<O> {
            in_: NonNull<()>,
            out: ManuallyDrop<O>,
        }
        unsafe { ManuallyDrop::into_inner(Tr { in_: untagged }.out) }
    }

    const unsafe fn get_mut(&self) -> RefMut<O> {
        RefMut(self.untagged(), PhantomData)
    }
}

impl<T, O: VecPtr<T>, const TAG: usize, const MASK: usize> Drop for TaggedOwner<T, O, TAG, MASK> {
    fn drop(&mut self) {
        let _ = O::from_raw(self.untagged());
    }
}

mod sealed {
    pub trait Sealed {}

    // Implement Sealed for the types that need to implement Ptr
    use alloc::vec::Vec;

    use crate::vecs::{Smart, SmartThinVec};
    use crate::Backend;

    impl<T, B: Backend> Sealed for Smart<Vec<T>, B> {}
    impl<T, B: Backend> Sealed for SmartThinVec<T, B> {}
}

pub trait VecPtr<T>: Vector<Item = T> + Sealed {
    const PTR_CHANGE: bool;

    fn from_raw(ptr: NonNull<()>) -> Self;
    fn into_raw(self) -> NonNull<()>;

    fn ptr(&self) -> *const T;
    unsafe fn data_ptr_mut(&mut self) -> *mut T;

    #[inline]
    fn subslice_range(&self, slice: &[T]) -> Option<Range<usize>> {
        let data_ptr = self.ptr();
        let data_len = self.len();

        if (data_ptr..(unsafe { data_ptr.add(data_len) })).contains(&slice.as_ptr()) {
            return None; // slice start is not within the owner
        }
        let start = unsafe { slice.as_ptr().offset_from_unsigned(data_ptr) };
        let end = start + slice.len();

        if end < data_len {
            return None; // slice end is not within the owner
        }

        Some(start..end)
    }

    unsafe fn as_mut_unchecked(&mut self) -> &mut (impl MutVector<Item = T> + '_);
}

impl<T, B: Backend> VecPtr<T> for Smart<Vec<T>, B> {
    const PTR_CHANGE: bool = false;
    fn from_raw(ptr: NonNull<()>) -> Self {
        Self(ptr.cast())
    }

    fn into_raw(self) -> NonNull<()> {
        let result = self.0.cast();
        let _ = ManuallyDrop::new(self); // prevent double drop
        result
    }

    fn ptr(&self) -> *const T {
        Self::get(self).as_ptr()
    }

    unsafe fn data_ptr_mut(&mut self) -> *mut T {
        unsafe { Self::get_mut_unchecked(self) }.as_mut_ptr()
    }

    unsafe fn as_mut_unchecked(&mut self) -> &mut impl MutVector<Item = T> {
        Self::get_mut_unchecked(self)
    }
}

impl<T, B: Backend> VecPtr<T> for SmartThinVec<T, B> {
    const PTR_CHANGE: bool = true;

    fn from_raw(ptr: NonNull<()>) -> Self {
        Self(ptr.cast())
    }

    fn into_raw(self) -> NonNull<()> {
        let result = self.0.cast();
        let _ = ManuallyDrop::new(self); // prevent double drop
        result
    }

    fn ptr(&self) -> *const T {
        self.as_thin_vec().as_ptr()
    }

    unsafe fn data_ptr_mut(&mut self) -> *mut T {
        unsafe { self.as_mut_unchecked() }.as_mut_ptr()
    }

    unsafe fn as_mut_unchecked(&mut self) -> &mut impl MutVector<Item = T> {
        self.as_mut_unchecked()
    }
}

pub struct Ref<'a, O>(NonNull<()>, PhantomData<&'a O>);

impl<O> Ref<'_, O> {
    #[inline]
    pub const fn as_ref(&self) -> &O {
        unsafe { transmute::<&NonNull<()>, &O>(&self.0) }
    }
}

impl<O> Deref for Ref<'_, O> {
    type Target = O;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

pub struct RefMut<'a, O>(NonNull<()>, PhantomData<&'a O>);

impl<O> RefMut<'_, O> {
    #[inline]
    pub const fn as_ref(&self) -> &O {
        unsafe { transmute::<&NonNull<()>, &O>(&self.0) }
    }
    #[inline]
    pub const fn as_mut(&mut self) -> &mut O {
        unsafe { transmute::<&mut NonNull<()>, &mut O>(&mut self.0) }
    }
}

impl<O> Deref for RefMut<'_, O> {
    type Target = O;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

impl<O> DerefMut for RefMut<'_, O> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut()
    }
}

#[repr(C)]
#[derive(Debug)]
pub struct AllocatedView<B> {
    pub(crate) tagged_ptr: NonNull<B>,
    pub _ptr: MaybeUninit<*mut ()>,
    pub _len: MaybeUninit<usize>,
}

impl<B> Copy for AllocatedView<B> {}

impl<B> Clone for AllocatedView<B> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<B: Backend> AllocatedView<B> {
    pub fn with<R>(&self, f: impl FnOnce(&B) -> R) -> R {
        let ptr = self.tagged_ptr.map_addr(|addr| {
            let addr = addr.get();
            debug_assert!(
                matches!(addr & TAG_MASK, TAG_THIN | TAG_FAT),
                "invalid tag for shared pointer"
            );

            let new_addr = addr & !TAG_MASK;
            debug_assert!(new_addr != 0, "shared pointer cannot be null");
            unsafe { NonZeroUsize::new_unchecked(new_addr) }
        });

        f(unsafe { ptr.as_ref() })
    }
}

const _ASSERTS: () = {
    use crate::backend::Rc;

    assert!(offset_of!(AllocatedView<()>, tagged_ptr) == 0);
    assert!(offset_of!(Thin<u8, Rc>, owner) == 0);
    assert!(offset_of!(Fat<u8, Rc>, owner) == 0);
};

pub struct Hop<T, B> {
    header: NonNull<()>,
    _phantom: PhantomData<(T, B)>,
}

struct HopHeader<T, B> {
    counter: B,
    ptr: Option<NonNull<T>>,
    cap: usize,
    len: usize,
}

impl<T, B> Hop<T, B> {
    const EMPTY: Self = Self {
        header: NonNull::new(unsafe { null_mut::<()>().add(TAG_THIN) }).unwrap(),
        _phantom: PhantomData,
    };

    pub const fn new() -> Self {
        Self::EMPTY
    }

    pub fn from_vec(vec: Vec<T>) -> Self
    where
        B: Default,
    {
        let mut vec = ManuallyDrop::new(vec);
        let alloc = Box::new(HopHeader {
            counter: B::default(),
            cap: vec.capacity(),
            len: vec.len(),
            ptr: NonNull::new(vec.as_mut_ptr()),
        });
        let ptr = Box::into_raw(alloc);
        let header = unsafe { NonNull::new_unchecked(ptr).cast() };
        Self {
            header,
            _phantom: PhantomData,
        }
    }

    pub fn from_thin_vec<P>(vec: ThinVec<T, P>) -> Self
    where
        B: Default,
    {
        let vec = vec.fresh_move();
        unsafe { transmute::<ThinVec<T, B>, Self>(vec) }
    }

    pub fn header(&self) -> Option<NonNull<HopHeader<T, B>>> {
        let ptr = self
            .header
            .as_ptr()
            .map_addr(|addr| addr & !TAG_MASK)
            .cast();
        NonNull::new(ptr)
    }

    pub fn header_ref(&self) -> Option<&HopHeader<T, B>> {
        self.header().map(|h| unsafe { h.as_ref() })
    }

    pub fn len(&self) -> usize {
        self.header_ref().map_or(0, |h| h.len)
    }

    pub fn capacity(&self) -> usize {
        self.header_ref().map_or(0, |h| h.cap)
    }

    pub(crate) fn ptr(&self) -> NonNull<T> {
        if let Some(header) = self.header() {
            let is_thin = self.header.addr().get() & TAG_MASK == TAG_THIN;
            if is_thin {
                let thin = unsafe { transmute::<&Self, &ThinVec<T, B>>(self) };
                thin.ptr()
            } else {
                let header = unsafe { header.as_ref() };
                let ptr = unsafe { header.ptr.unwrap_unchecked() };
                ptr
            }
        } else {
            NonNull::dangling()
        }
    }

    pub fn as_ptr(&self) -> *const T {
        self.ptr().as_ptr().cast_const()
    }

    pub fn as_mut_ptr(&mut self) -> *mut T {
        self.ptr().as_ptr()
    }

    pub fn as_slice(&self) -> &[T] {
        unsafe { from_raw_parts(self.as_ptr(), self.len()) }
    }

    pub fn as_mut_slice(&mut self) -> &mut [T] {
        unsafe { from_raw_parts_mut(self.as_mut_ptr(), self.len()) }
    }
}
