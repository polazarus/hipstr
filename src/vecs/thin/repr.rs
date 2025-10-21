//! Internal representation of thin vectors.

use core::alloc::Layout;
use core::ptr::NonNull;

use const_default::ConstDefault;

use crate::common::ZeroUsize;
use crate::vecs::reprs::MagicPointer;

/// A thin vector header with prefix.
#[derive(Debug)]
#[repr(C)]
pub struct ThinHeader<T, P> {
    /// Prefix.
    pub prefix: P,
    /// A pointer-sized zero used to ensure proper field alignment with `WideInner`
    /// and differientate between the two.
    _ptr: ZeroUsize,
    /// Capacity.
    pub cap: usize,
    /// Length.
    pub len: usize,
    /// A zero-sized array to `T` to ensure field alignment.
    data: [T; 0],
}

impl<T, P> ThinHeader<T, P> {
    /// Computes a `ThinVec` layout and the effective capacity, given a required capacity.
    #[inline]
    pub const fn layout(payload: usize) -> Option<(Layout, usize)> {
        let layout = Layout::new::<Self>();

        #[cfg(not(coverage))]
        debug_assert!(layout.align() >= align_of::<T>(), "invalid alignment");

        let Ok(arr) = Layout::array::<T>(payload) else {
            return None;
        };
        let Ok((layout, offset)) = layout.extend(arr) else {
            return None;
        };
        let layout = layout.pad_to_align();

        #[cfg(not(coverage))]
        debug_assert!(offset == size_of::<Self>(), "invalid offset");

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
    pub const fn data(header: NonNull<Self>) -> NonNull<T> {
        unsafe { header.add(1).cast() }
    }
}

impl<T, P> ConstDefault for ThinHeader<T, P>
where
    P: ConstDefault,
{
    const DEFAULT: Self = Self {
        prefix: P::DEFAULT,
        _ptr: ZeroUsize::Zero,
        cap: 0,
        len: 0,
        data: [],
    };
}

/// A thin vector representation.
pub type ThinRepr<T, P> = MagicPointer<ThinHeader<T, P>>;

impl<T, P> ThinRepr<T, P> {
    pub const fn data(self) -> NonNull<T> {
        if let Some(header) = self.get() {
            ThinHeader::data(header)
        } else {
            NonNull::dangling()
        }
    }
}
