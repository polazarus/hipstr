use core::mem::MaybeUninit;
use core::ptr::NonNull;

macro_rules! truncate_impl {
    ($self:ident, $new_len:expr) => {{
        let old_len = $self.len();
        let new_len = $new_len;
        if new_len < old_len {
            // SAFETY: strict decrease
            unsafe {
                $self.set_len(new_len);
            }

            // SAFETY: type invariant
            unsafe {
                $crate::common::drop_raw_slice($self.as_mut_ptr().add(new_len), old_len - new_len);
            }
        }
    }};
}

macro_rules! pop_impl {
    ($self:ident) => {{
        let len = $self.len();
        if len > 0 {
            // SAFETY: length is guaranteed to be greater than zero
            unsafe {
                let ptr = $self.as_mut_ptr().add(len - 1);
                let value = ptr.read();
                $self.set_len(len - 1);
                Some(value)
            }
        } else {
            None
        }
    }};
}

macro_rules! pop_if_impl {
    ($self:ident, $f:ident) => {{
        let len = $self.len();
        if len > 0 {
            // SAFETY: length is guaranteed to be greater than zero
            let ptr = unsafe { $self.as_mut_ptr().add(len - 1) };
            // SAFETY: we are reading from a valid pointer
            if $f(unsafe { &*ptr }) {
                // move out the last element

                // SAFETY: the length decreases
                unsafe {
                    $self.set_len(len - 1);
                }

                // SAFETY: length is guaranteed to be greater than zero
                let value = unsafe { ptr.read() };
                return Some(value);
            }
        }
        None
    }};
}

macro_rules! spare_capacity_mut_impl {
    ($self:ident) => {{
        let ptr = $self.as_mut_ptr();
        let len = $self.len();
        let capacity = $self.capacity();

        // SAFETY: ptr in the valid range by type invariant
        let slice_ptr: *mut core::mem::MaybeUninit<_> = unsafe { ptr.add(len).cast() };
        // do not underflow by type invariant
        let slice_len = capacity - len;
        // SAFETY: slice is valid but uninitialized by type invariant
        unsafe { core::slice::from_raw_parts_mut(slice_ptr, slice_len) }
    }};
}

macro_rules! push_within_capacity {
    ($self:ident, $value:expr) => {{
        let len = $self.len();
        if len < $self.capacity() {
            // SAFETY: capacity is guaranteed to be greater than length
            unsafe {
                let ptr = $self.as_mut_ptr().add(len);
                ptr.write($value);
                $self.set_len(len + 1);
            }
            Ok(())
        } else {
            Err($value)
        }
    }};
}

macro_rules! extend_from_array_impl {
    ($self:ident, $array:expr) => {{
        let array = $array;
        let len = $self.len();
        let new_len = len + array.len();
        assert!(new_len <= $self.capacity(), "new length exceeds capacity");
        // SAFETY: capacity ≥ new length
        unsafe {
            $self.set_len(new_len);
            $self
                .as_mut_ptr()
                .add(len)
                .copy_from_nonoverlapping(array.as_ptr().cast(), array.len());
        }
        core::mem::forget(array);
    }};
}

macro_rules! extend_from_boxed_impl {
    ($self:ident, $boxed:expr) => {{
        use alloc::boxed::Box;
        use core::mem::{transmute, MaybeUninit};

        fn into_maybe_uninit_boxed<T>(boxed: Box<[T]>) -> Box<[MaybeUninit<T>]> {
            // SAFETY: the boxed slice is valid and uninitialized
            unsafe { transmute(boxed) }
        }

        let boxed = into_maybe_uninit_boxed($boxed);
        let len = $self.len();
        let new_len = len + boxed.len();
        assert!(new_len <= $self.capacity(), "new length exceeds capacity");
        // SAFETY: capacity ≥ new length
        unsafe {
            $self.set_len(new_len);
            $self
                .as_mut_ptr()
                .add(len)
                .copy_from_nonoverlapping(boxed.as_ptr().cast(), boxed.len());
        }
        // boxed is dropped, but the content is not dropped due to the
        // transmutation to MaybeUninit
    }};
}

macro_rules! extend_from_slice_impl {
    ($self:ident, $slice:expr) => {{
        let slice = $slice;
        let len = $self.len();
        let new_len = len + slice.len();
        assert!(new_len <= $self.capacity(), "new length exceeds capacity");
        let ptr = $self.as_mut_ptr();
        for (i, e) in (len..).zip(slice) {
            let e = e.clone();
            // SAFETY: capacity ≥ new length
            unsafe {
                ptr.add(i).write(e);
            }
            // SAFETY: the length is updated after writing
            unsafe {
                $self.set_len(i + 1);
            }
        }
    }};
}

/// Swaps two elements in a slice without bounds checking.
///
/// # Panics
///
/// In debug only, it panics if the indices are out of bounds.
///
/// # Safety
///
/// The indices must be valid indices for the slice.
pub const unsafe fn const_slice_swap_unchecked<T>(slice: &mut [T], a: usize, b: usize) {
    debug_assert!(
        a < slice.len() && b < slice.len(),
        "unchecked swap is out of bounds"
    );
    unsafe {
        let ptr = slice.as_mut_ptr();
        ptr.add(a).swap(ptr.add(b));
    }
}

pub(crate) use {
    extend_from_array_impl, extend_from_boxed_impl, extend_from_slice_impl, pop_if_impl, pop_impl,
    push_within_capacity, spare_capacity_mut_impl, truncate_impl,
};
