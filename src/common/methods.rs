/// `resize_with` impl, requires `len`, `set_len`, and `as_mut_ptr`
macro_rules! resize_with_impl {
    ($self:ident, $new_len:expr, $f:expr) => {{
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
        } else if new_len > old_len {
            for i in old_len..new_len {
                // SAFETY: the length is guaranteed to be less than capacity
                unsafe {
                    let ptr = $self.as_mut_ptr().add(i);
                    ptr.write($f());
                    $self.set_len(i + 1);
                }
            }
        }
    }};
}

/// `truncate` impl, requires `len`, set_`len, and `as_mut_ptr`
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

/// `pop` impl, requires `len`, `set_len`, and `as_mut_ptr`
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

/// `pop_if` impl, requires `len`, `set_len`, and `as_mut_ptr`
macro_rules! pop_if_impl {
    ($self:ident, $f:ident) => {{
        let len = $self.len();
        if len > 0 {
            // SAFETY: length is guaranteed to be greater than zero
            if $f(unsafe { &mut *$self.as_mut_ptr().add(len - 1) }) {
                // move out the last element

                // SAFETY: the length decreases
                unsafe {
                    $self.set_len(len - 1);
                }

                // SAFETY: length is guaranteed to be greater than zero
                let value = unsafe { $self.as_mut_ptr().add(len - 1).read() };
                return Some(value);
            }
        }
        None
    }};
}

/// `spare_capacity_mut` impl, requires `as_mut_ptr`, `len`,  and `capacity`
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

/// `push_within_capacity` impl, requires `len`, `capacity` `set_len`, and `as_mut_ptr`
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

///
macro_rules! extend_from_raw_move {
    ($self:ident, $ptr:expr, $len:expr) => {{
        let len = $self.len();
        let new_len = len + $len;
        assert!(new_len <= $self.capacity(), "new length exceeds capacity");
        // SAFETY: capacity ≥ new length
        unsafe {
            $self.set_len(new_len);
            $self
                .as_mut_ptr()
                .add(len)
                .copy_from_nonoverlapping($ptr.cast(), $len);
        }
    }};
}

/// `extend_from_array` impl, requires `len`, `capacity`, `set_len`, and `as_mut_ptr`
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

/// `extend_from_boxed` impl, requires `len`, `capacity`, `set_len`, and `as_mut_ptr`
macro_rules! extend_from_boxed_impl {
    ($self:ident, $boxed:expr) => {{
        use alloc::boxed::Box;
        use alloc::vec::Vec;
        use core::mem::{transmute, MaybeUninit};

        fn into_maybe_uninit_boxed<T>(boxed: Box<[T]>) -> Box<[MaybeUninit<T>]> {
            // SAFETY: the boxed slice is valid and uninitialized
            unsafe { transmute(boxed) }
        }

        let boxed = $boxed;
        let len = $self.len();
        let new_len = len + boxed.len();
        assert!(new_len <= $self.capacity(), "new length exceeds capacity");

        let boxed = into_maybe_uninit_boxed(boxed);
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

/// `extend_from_slice` impl, requires `len`, `capacity` and `try_push`
macro_rules! extend_from_slice_impl {
    ($self:ident, $slice:expr) => {{
        let slice = $slice;
        let len = $self.len();
        let new_len = len + slice.len();
        assert!(new_len <= $self.capacity(), "new length exceeds capacity");
        for e in slice {
            let e = e.clone();
            unsafe {
                $self.try_push(e).unwrap_unchecked();
            }
        }
    }};
}

macro_rules! remove_unchecked_impl {
    ($self:ident, $index:expr) => {{
        let len = $self.len();
        let index = $index;

        // SAFETY:
        // - index checked above
        // - type invariant ensures that the element is initialized
        // - the length is decremented after the element is removed
        unsafe {
            let ptr = $self.as_mut_ptr().add(index);
            let value = ptr.read();
            ptr.copy_from(ptr.add(1), len - index - 1);
            $self.set_len(len - 1);
            value
        }
    }};
}

macro_rules! swap_remove_impl {
    ($self:ident, $index:expr) => {{
        let len = $self.len();
        let index = $index;
        assert!(index < len, "index out of bounds");

        // SAFETY:
        // - index checked above
        // - type invariant ensures that the element is initialized
        // - the length is decremented after the element is removed
        unsafe {
            let ptr = $self.as_mut_ptr();
            let value = ptr.add(index).read();
            // copy the last element into the removed slot, even if index == len - 1
            ptr.add(index).copy_from(ptr.add(len - 1), 1);
            $self.set_len(len - 1);
            value
        }
    }};
}

/// Swaps two elements in a slice without bounds checking.
///
/// `slice::swap_unchecked` is not stable as of Rust 1.88.0.
///
/// # Panics
///
/// In debug only, it panics if the indices are out of bounds.
///
/// # Safety
///
/// The indices must be valid indices for the slice.
pub const unsafe fn slice_swap_unchecked<T>(slice: &mut [T], a: usize, b: usize) {
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
    extend_from_array_impl, extend_from_boxed_impl, extend_from_raw_move, extend_from_slice_impl,
    pop_if_impl, pop_impl, push_within_capacity, remove_unchecked_impl, resize_with_impl,
    spare_capacity_mut_impl, swap_remove_impl, truncate_impl,
};
