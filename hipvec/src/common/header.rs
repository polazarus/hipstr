use core::alloc::Layout;
use core::ptr::NonNull;

use const_default::ConstDefault;

use crate::common::ZeroUsize;

/// Common vector header with arbitrary associated data, called "prefix".
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(C)]
pub struct Header<T, Prefix, Ptr: Copy> {
    /// Prefix.
    pub prefix: Prefix,

    /// Data pointer if any.
    pub ptr: Ptr,

    /// Capacity.
    pub cap: usize,

    /// Length.
    pub len: usize,

    _phantom: core::marker::PhantomData<T>,
}

pub type ThinHeader<T, Prefix> = Header<T, Prefix, ZeroUsize>;
pub type WideHeader<T, Prefix> = Header<T, Prefix, Option<NonNull<T>>>;

impl<T, Prefix> ThinHeader<T, Prefix> {
    const DATA_OFFSET: usize = {
        let layout = Layout::new::<Self>();
        let Ok(layout) = layout.align_to(align_of::<T>()) else {
            panic!("invalid alignment");
        };
        let layout = layout.pad_to_align();
        layout.size()
    };

    pub const fn with_capacity(capacity: usize) -> Self
    where
        Prefix: ConstDefault,
    {
        Self {
            prefix: Prefix::DEFAULT,
            ptr: ZeroUsize::DEFAULT,
            cap: capacity,
            len: 0,
            _phantom: core::marker::PhantomData,
        }
    }

    /// Computes a `ThinVec` layout and the effective capacity, given a required capacity.
    #[inline]
    pub const fn layout(payload: usize) -> Option<(Layout, usize)> {
        let layout = Layout::new::<Self>();

        let Ok(arr) = Layout::array::<T>(payload) else {
            return None;
        };
        let Ok((layout, offset)) = layout.extend(arr) else {
            return None;
        };
        let layout = layout.pad_to_align();

        #[cfg(not(coverage))]
        debug_assert!(offset == Self::DATA_OFFSET, "invalid offset");

        // get the payload possibly rounded up to maximize possible occupancy in
        // closely in the computed layout
        let round_up_payload = if size_of::<T>() == 0 {
            usize::MAX
        } else {
            (layout.size() - offset) / size_of::<T>()
        };

        #[cfg(not(coverage))]
        debug_assert!(payload <= round_up_payload, "invalid roundup");

        Some((layout, round_up_payload))
    }

    /// Returns a pointer to the data, given a pointer to the header.
    #[inline]
    pub const unsafe fn data(header: NonNull<Self>) -> NonNull<T> {
        unsafe { header.byte_add(Self::DATA_OFFSET).cast() }
    }
}

impl<T, P> ConstDefault for ThinHeader<T, P>
where
    P: ConstDefault,
{
    const DEFAULT: Self = Self {
        prefix: P::DEFAULT,
        ptr: ZeroUsize::DEFAULT,
        cap: 0,
        len: 0,
        _phantom: core::marker::PhantomData,
    };
}

impl<T, P> ConstDefault for WideHeader<T, P>
where
    P: ConstDefault,
{
    const DEFAULT: Self = Self {
        prefix: P::DEFAULT,
        ptr: None,
        cap: 0,
        len: 0,
        _phantom: core::marker::PhantomData,
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::mem::offset_of;

    #[test]
    fn thin_data_offset() {
        type HU8 = ThinHeader<u8, ()>;
        type HU64 = ThinHeader<u64, ()>;
        type HU128 = ThinHeader<u128, ()>;

        assert_eq!(HU8::DATA_OFFSET, size_of::<HU8>());
        assert!(HU64::DATA_OFFSET >= size_of::<HU64>());
        assert!(HU64::DATA_OFFSET.is_multiple_of(align_of::<u64>()));
        assert!(HU128::DATA_OFFSET >= size_of::<HU128>());
        assert!(HU128::DATA_OFFSET.is_multiple_of(align_of::<u128>()));
    }

    #[test]
    fn thin_layout() {
        type HU8 = ThinHeader<u8, ()>;
        type HU64 = ThinHeader<u64, ()>;
        type HU128 = ThinHeader<u128, ()>;

        for payload in [0, 1, 2, 3, 4, 7, 8, 15, 16, 31, 32] {
            let (layout, round_up_payload) = HU8::layout(payload).unwrap();
            assert!(round_up_payload >= payload);
            assert!(layout.size().is_multiple_of(align_of::<u8>()));
            assert_eq!(layout.align(), align_of::<HU8>().max(align_of::<u8>()));

            let (layout, round_up_payload) = HU64::layout(payload).unwrap();
            assert!(round_up_payload >= payload);
            assert!(layout.size().is_multiple_of(align_of::<u64>()));
            assert_eq!(layout.align(), align_of::<HU64>().max(align_of::<u64>()));

            let (layout, round_up_payload) = HU128::layout(payload).unwrap();
            assert!(round_up_payload >= payload);
            assert!(layout.size().is_multiple_of(align_of::<u128>()));
            assert_eq!(layout.align(), align_of::<HU128>().max(align_of::<u128>()));
        }
    }

    #[test]
    fn common() {
        type THU8 = ThinHeader<u8, ()>;
        type FHU8 = WideHeader<u8, ()>;
        assert_eq!(offset_of!(THU8, prefix), offset_of!(FHU8, prefix));
        assert_eq!(offset_of!(THU8, ptr), offset_of!(FHU8, ptr));
        assert_eq!(offset_of!(THU8, len), offset_of!(FHU8, len));
        assert_eq!(offset_of!(THU8, cap), offset_of!(FHU8, cap));
    }
}
