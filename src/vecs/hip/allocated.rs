use alloc::vec::Vec;
use core::marker::PhantomData;
use core::mem::transmute;
use core::num::NonZeroUsize;
use core::ops::{Deref, Range};
use core::ptr::NonNull;

use self::sealed::Sealed;
use crate::vecs::{Smart, SmartThinVec};
use crate::Backend;

const TAG_MASK: usize = super::super::TAG_MASK as usize;
const TAG_FAT: usize = super::super::TAG_FAT as usize;
const TAG_THIN: usize = super::super::TAG_THIN as usize;

pub type Thin<T, B> = Allocated<SmartThinVec<T, B>, T, TAG_THIN, TAG_MASK>;
pub type Fat<T, B> = Allocated<Smart<Vec<T>, B>, T, TAG_FAT, TAG_MASK>;
#[repr(C)]
pub struct Allocated<O: VecPtr<T>, T, const TAG: usize, const MASK: usize> {
    pub owner: TaggedPtr<T, O, TAG, MASK>,
    pub ptr: *const T,
    pub len: usize,
}

impl<O: VecPtr<T>, T, const TAG: usize, const MASK: usize> Allocated<O, T, TAG, MASK> {
    pub fn new(owner: O, ptr: *const T, len: usize) -> Self {
        let owner = TaggedPtr::new(owner.into_raw());
        Self { owner, ptr, len }
    }

    pub fn owner(&self) -> Ref<O> {
        self.owner.get()
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
            self.ptr = unsafe { o.data_ptr().add(range.start) };
            self.len = range.end - range.start;

            result
        })
    }
}

pub struct TaggedPtr<T, O: VecPtr<T>, const TAG: usize, const MASK: usize>(
    NonNull<()>,
    PhantomData<(O, [T])>,
);

impl<T, O: VecPtr<T>, const TAG: usize, const MASK: usize> TaggedPtr<T, O, TAG, MASK> {
    fn new(ptr: NonNull<()>) -> Self {
        Self(
            ptr.map_addr(|addr| {
                debug_assert!(addr.get() & MASK == 0);
                unsafe { NonZeroUsize::new_unchecked(addr.get() | TAG) }
            }),
            PhantomData,
        )
    }

    fn untagged(&self) -> NonNull<()> {
        self.0
            .map_addr(|addr| unsafe { NonZeroUsize::new_unchecked(addr.get() & !MASK) })
    }

    pub fn get(&self) -> Ref<'_, O> {
        Ref(self.untagged(), PhantomData)
    }

    pub fn with_mut<F: FnOnce(&mut O) -> R, R>(&mut self, f: F) -> R {
        unsafe fn to_ref<O>(ptr: &mut NonNull<()>) -> &mut O {
            unsafe { transmute(ptr) }
        }
        let mut ptr = self.untagged();
        let backup = ptr;
        let ref_mut = unsafe { to_ref(&mut ptr) };

        let result = f(ref_mut);
        if ptr != backup {
            self.0 = ptr.map_addr(|addr| {
                debug_assert!(addr.get() & MASK == 0);
                unsafe { NonZeroUsize::new_unchecked(addr.get() | TAG) }
            });
        }
        result
    }
}

impl<T, O: VecPtr<T>, const TAG: usize, const MASK: usize> Drop for TaggedPtr<T, O, TAG, MASK> {
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

pub trait VecPtr<T>: Sealed {
    fn from_raw(ptr: NonNull<()>) -> Self;
    fn into_raw(self) -> NonNull<()>;

    fn data_ptr(&self) -> *const T;
    fn data_len(&self) -> usize;

    #[inline]
    fn subslice_range(&self, slice: &[T]) -> Option<Range<usize>> {
        let data_ptr = self.data_ptr();
        let data_len = self.data_len();

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
}

impl<T, B: Backend> VecPtr<T> for Smart<Vec<T>, B> {
    fn from_raw(ptr: NonNull<()>) -> Self {
        Self(ptr.cast())
    }

    fn into_raw(self) -> NonNull<()> {
        self.0.cast()
    }

    fn data_ptr(&self) -> *const T {
        Smart::get(&self).as_ptr()
    }

    fn data_len(&self) -> usize {
        Smart::get(&self).len()
    }
}

impl<T, B: Backend> VecPtr<T> for SmartThinVec<T, B> {
    fn from_raw(ptr: NonNull<()>) -> Self {
        Self(ptr.cast())
    }

    fn into_raw(self) -> NonNull<()> {
        self.0.cast()
    }

    fn data_ptr(&self) -> *const T {
        self.as_thin_vec().as_ptr()
    }

    fn data_len(&self) -> usize {
        self.as_thin_vec().len()
    }
}

pub struct Ref<'a, O>(NonNull<()>, PhantomData<&'a O>);

impl<O> Deref for Ref<'_, O> {
    type Target = O;

    fn deref(&self) -> &Self::Target {
        unsafe { transmute::<&NonNull<()>, &O>(&self.0) }
    }
}

#[derive(Debug)]
pub struct SharedCountView<B> {
    pub(crate) tagged_ptr: NonNull<B>,
}

impl<B> Copy for SharedCountView<B> {}

impl<B> Clone for SharedCountView<B> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<B: Backend> SharedCountView<B> {
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
