use core::marker::PhantomData;
use core::ptr::{self, NonNull};
use core::slice;

use crate::vecs::{TAG_FAT, TAG_THIN};

struct Header<T, P> {
    pub prefix: P,
    pub buffer: Option<NonNull<T>>,
    pub capacity: usize,
    pub length: usize,
}

enum Kind {
    Thin = TAG_THIN as usize,
    Fat = TAG_FAT as usize,
}

pub struct Hop<
    T,
    P = (),
    const THIN: usize = { TAG_THIN as usize },
    const FAT: usize = { TAG_FAT as usize },
> {
    header: NonNull<()>,
    phantom: PhantomData<(T, P)>,
}

impl<T, P, const THIN: usize, const FAT: usize> Hop<T, P, THIN, FAT> {
    const ZST: bool = size_of::<T>() == 0;
    const DATA_OFFSET: usize = size_of::<Header<T, P>>().next_multiple_of(align_of::<T>());
    const EMPTY: Self = const {
        let header = NonNull::new(unsafe { ptr::null_mut::<()>().byte_add(THIN) }).unwrap();
        Self {
            header,
            phantom: PhantomData,
        }
    };

    const fn check_tags() {
        assert!(THIN != 0, "invalid thin tag: should be non-zero");
        assert!(
            THIN < align_of::<Header<T, P>>(),
            "invalid thin tag: should be less than the header's alignment requirement"
        );
        assert!(FAT != 0, "invalid fat tag: should be non-zero");
        assert!(
            FAT < align_of::<Header<T, P>>(),
            "invalid fat tag: should be less than the header's alignment requirement"
        );
    }

    #[must_use]
    #[inline]
    pub const fn new() -> Self {
        #[cfg(debug_assertions)]
        Self::check_tags();

        Self::EMPTY
    }

    #[must_use]
    #[inline]
    pub const fn with_prefix_and_capacity(prefix: P, capacity: usize) -> Self {
        #[cfg(debug_assertions)]
        Self::check_tags();

        let header: Header<T, P> = Header {
            prefix,
            buffer: None,
            capacity,
            length: 0,
        };
        todo!()
    }

    #[must_use]
    #[inline]
    pub const fn prefix(&self) -> Option<&P> {
        if let Some(header) = self.ptr() {
            // SAFETY: type invariant
            let header_ref = unsafe { header.as_ref() };
            Some(&header_ref.prefix)
        } else {
            None
        }
    }

    #[inline]
    const fn ptr(&self) -> Option<NonNull<Header<T, P>>> {
        // SAFETY: type invariant
        let untagged = unsafe { self.header.as_ptr().byte_sub(THIN) };
        let untagged: *mut Header<T, P> =   untagged.cast();
        // TODO: check is_aligned on untagged when const stabilized
        NonNull::new(untagged)
    }

    const fn data(&self) -> NonNull<T> {
        if let Some(header) = self.ptr() {
            // SAFETY: type invariant
            let header_ref = unsafe { header.as_ref() };
            if let Some(buffer) = header_ref.buffer {
                buffer
            } else {
                let ptr = unsafe { header.add(Self::DATA_OFFSET) };
                // TODO: check alignment when const stabilized
                ptr.cast()
            }
        } else {
            NonNull::dangling()
        }
    }

    #[must_use]
    #[inline]
    pub const fn as_non_null(&mut self) -> NonNull<T> {
        self.data()
    }

    #[must_use]
    #[inline]
    pub const fn as_ptr(&self) -> *const T {
        self.data().as_ptr()
    }

    #[must_use]
    #[inline]
    pub const fn as_mut_ptr(&mut self) -> *mut T {
        self.data().as_ptr()
    }

    #[must_use]
    #[inline]
    pub const fn capacity(&self) -> usize {
        if let Some(header) = self.ptr() {
            let header = unsafe { header.as_ref() };
            header.capacity
        } else {
            0
        }
    }

    #[must_use]
    #[inline]
    pub const fn len(&self) -> usize {
        if let Some(header) = self.ptr() {
            let header = unsafe { header.as_ref() };
            header.length
        } else {
            0
        }
    }

    #[must_use]
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[must_use]
    #[inline]
    pub const fn as_slice(&self) -> &[T] {
        // SAFETY: type invariant
        //
        // if the vec is not allocated yet, `as_ptr` is dangling but non-zero
        // and well-aligned
        unsafe { slice::from_raw_parts(self.as_ptr(), self.len()) }
    }

    #[must_use]
    #[inline]
    pub const fn as_mut_slice(&mut self) -> &mut [T] {
        // SAFETY: type invariant
        //
        // if the vec is not allocated yet, `as_mut_ptr` is dangling but non-zero
        // and well-aligned
        unsafe { slice::from_raw_parts_mut(self.as_mut_ptr(), self.len()) }
    }
}
