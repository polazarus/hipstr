use alloc::boxed::Box;
use alloc::vec::Vec;
use core::alloc::Layout;
use core::ptr::NonNull;

use const_default::ConstDefault;

use crate::backend::InitPrefix;
use crate::common::ZeroUsize;

/// Header of a heap byte buffer, with arbitrary associated data (the
/// "prefix", e.g. a reference count).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(C)]
pub struct Header<Prefix, Ptr: Copy> {
    /// Prefix.
    pub prefix: Prefix,

    /// Data pointer if any.
    pub ptr: Ptr,

    /// Capacity.
    pub cap: usize,

    /// Length.
    pub len: usize,
}

pub type ThinHeader<Prefix> = Header<Prefix, ZeroUsize>;
pub type VecHeader<Prefix> = Header<Prefix, Option<NonNull<u8>>>;

impl<Prefix> ThinHeader<Prefix> {
    /// The bytes follow the header (alignment 1: no padding).
    const DATA_OFFSET: usize = size_of::<Self>();

    pub fn with_capacity(capacity: usize) -> Self
    where
        Prefix: InitPrefix,
    {
        Self {
            prefix: Prefix::init(),
            ptr: ZeroUsize::DEFAULT,
            cap: capacity,
            len: 0,
        }
    }

    /// The allocation layout for `payload` bytes after the header, and the
    /// usable capacity (the allocation is rounded up to the header's
    /// alignment, which the bytes can use).
    #[inline]
    pub const fn layout(payload: usize) -> Option<(Layout, usize)> {
        let Some(size) = Self::DATA_OFFSET.checked_add(payload) else {
            return None;
        };
        let Ok(layout) = Layout::from_size_align(size, align_of::<Self>()) else {
            return None;
        };
        let layout = layout.pad_to_align();
        Some((layout, layout.size() - Self::DATA_OFFSET))
    }

    /// Returns a pointer to the data, given a pointer to the header.
    #[inline]
    pub const unsafe fn data(header: NonNull<Self>) -> NonNull<u8> {
        unsafe { header.byte_add(Self::DATA_OFFSET).cast() }
    }
}

impl<P: InitPrefix> Header<P, Option<NonNull<u8>>> {
    pub(crate) fn from_vec(vec: Vec<u8>) -> Box<Self> {
        let (ptr, len, cap) = vec.into_raw_parts();
        Box::new(Self {
            prefix: P::init(),
            ptr: NonNull::new(ptr),
            cap,
            len,
        })
    }
}

impl<P> ConstDefault for ThinHeader<P>
where
    P: ConstDefault,
{
    const DEFAULT: Self = Self {
        prefix: P::DEFAULT,
        ptr: ZeroUsize::DEFAULT,
        cap: 0,
        len: 0,
    };
}

impl<P> ConstDefault for VecHeader<P>
where
    P: ConstDefault,
{
    const DEFAULT: Self = Self {
        prefix: P::DEFAULT,
        ptr: None,
        cap: 0,
        len: 0,
    };
}

#[cfg(test)]
mod tests {
    use core::mem::offset_of;

    use super::*;

    #[test]
    fn thin_layout() {
        type H = ThinHeader<()>;
        assert_eq!(H::DATA_OFFSET, size_of::<H>());
        for payload in [0, 1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 100] {
            let (layout, capacity) = H::layout(payload).unwrap();
            assert!(capacity >= payload, "{payload}");
            assert_eq!(
                layout.size(),
                H::DATA_OFFSET + capacity,
                "rounding is usable"
            );
            assert!(layout.size().is_multiple_of(align_of::<H>()));
            assert_eq!(layout.align(), align_of::<H>());
        }
        assert!(H::layout(usize::MAX).is_none());
        assert!(H::layout(isize::MAX as usize).is_none());
    }

    #[test]
    fn common() {
        type THU8 = ThinHeader<()>;
        type FHU8 = VecHeader<()>;
        assert_eq!(offset_of!(THU8, prefix), offset_of!(FHU8, prefix));
        assert_eq!(offset_of!(THU8, ptr), offset_of!(FHU8, ptr));
        assert_eq!(offset_of!(THU8, len), offset_of!(FHU8, len));
        assert_eq!(offset_of!(THU8, cap), offset_of!(FHU8, cap));
    }
}
