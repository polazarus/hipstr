/// `resize_with` impl, requires `len`, `set_len` and `as_mut_ptr`
macro_rules! resize_impl {
    ($self:ident, $new_len:expr, $iter:expr) => {{
        use $crate::common::SliceWriteGuard;

        let old_len = $self.len();
        let new_len = $new_len;
        if old_len < new_len {
            let additional = new_len - old_len;
            $self.reserve(additional);
            // grow

            let base = $self.as_mut_ptr();

            // SAFETY: valid write because the reserve call ensures there is enough capacity
            let mut guard = unsafe { SliceWriteGuard::new(base.add(old_len), additional) };
            for e in $iter.take(additional) {
                unsafe {
                    guard.write(e);
                }
            }
            guard.complete();
            // SAFETY: the additioanl elements have been initialized
            unsafe {
                $self.set_len(new_len);
            }
        } else if old_len > new_len {
            // truncate

            // SAFETY: strict decrease
            unsafe {
                $self.set_len(new_len);
            }

            // SAFETY: type invariant
            unsafe {
                $crate::common::utils::drop_raw_slice(
                    $self.as_mut_ptr().add(new_len),
                    old_len - new_len,
                );
            }
        }
    }};
}

/// `truncate` impl, requires `len`, `set_len`, and `as_mut_ptr`
macro_rules! truncate {
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
                $crate::common::utils::drop_raw_slice(
                    $self.as_mut_ptr().add(new_len),
                    old_len - new_len,
                );
            }
        }
    }};
}

macro_rules! truncate_copy {
    ($self:ident, $new_len:expr) => {{
        let old_len = $self.len();
        let new_len = $new_len;

        if false {
            const fn is_copy<V, T: Copy>(_: fn(&V) -> *const T) {}
            is_copy(Self::as_ptr);
        }

        if new_len < old_len {
            // SAFETY: strict decrease
            unsafe {
                $self.set_len(new_len);
            }
        }
    }};
}

/// `pop` impl, requires `len`, `set_len`, and `as_mut_ptr`
macro_rules! pop {
    ($self:ident) => {{
        let len = $self.len();
        if len > 0 {
            // SAFETY: length is guaranteed to be greater than zero
            unsafe {
                $self.set_len(len - 1);
                let ptr = $self.as_mut_ptr().add(len - 1);
                let value = ptr.read();
                Some(value)
            }
        } else {
            None
        }
    }};
}

/// `pop_if` impl, requires `len`, `set_len`, and `as_mut_ptr`
macro_rules! pop_if {
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
macro_rules! spare_capacity_mut {
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

macro_rules! push {
    ($self:ident, $value:expr) => {{
        $self.reserve(1);
        let len = $self.len();
        // SAFETY: capacity is guaranteed to be greater than length after reserve
        unsafe {
            let ptr = $self.as_mut_ptr().add(len);
            ptr.write($value);
            $self.set_len(len + 1);
        }
    }};
}

macro_rules! push_mut {
    ($self:ident, $value:expr) => {{
        $self.reserve(1);
        let len = $self.len();
        // SAFETY: capacity is guaranteed to be greater than length after reserve
        unsafe {
            let ptr = $self.as_mut_ptr().add(len);
            ptr.write($value);
            $self.set_len(len + 1);
            &mut *ptr
        }
    }};
}

/// `insert` impl, requires `len`, `reserve`, `set_len`, and `as_mut_ptr`
macro_rules! insert {
    ($self:ident, $index:expr, $value:expr) => {{
        let index = $index;
        let value = $value;
        let len = $self.len();
        assert!(index <= len, "index out of bounds");

        $self.reserve(1);

        // SAFETY: index is checked above
        unsafe {
            let ptr = $self.as_mut_ptr().add(index);
            if index < len {
                ptr.add(1).copy_from(ptr, len - index);
            }
            ptr.write(value);
            $self.set_len(len + 1);
        }
    }};
}

/// `insert` impl, requires `len`, `reserve`, `set_len`, and `as_mut_ptr`
macro_rules! insert_mut {
    ($self:ident, $index:expr, $value:expr) => {{
        let index = $index;
        let value = $value;
        let len = $self.len();
        assert!(index <= len, "index out of bounds");

        $self.reserve(1);

        // SAFETY: index is checked above
        unsafe {
            let ptr = $self.as_mut_ptr().add(index);
            if index < len {
                ptr.add(1).copy_from(ptr, len - index);
            }
            ptr.write(value);
            $self.set_len(len + 1);
            &mut *ptr
        }
    }};
}

/// `extend_from_array` impl, requires `len`, `capacity`, `set_len`, and `as_mut_ptr`
macro_rules! extend_from_array {
    ($self:ident, $array:expr) => {{
        let array = $array;
        let array_len = array.len();
        $self.reserve(array_len);

        let len = $self.len();
        let new_len = len + array_len;
        // SAFETY: capacity ≥ new length
        unsafe {
            $self.set_len(new_len);
            $self
                .as_mut_ptr()
                .add(len)
                .copy_from_nonoverlapping(array.as_ptr().cast(), array_len);
        }
        core::mem::forget(array);
    }};
}

/// `from_array` impl, requires `with_capacity`, `set_len`, and `as_mut_ptr`
macro_rules! from_array_impl {
    ($array:expr) => {{
        let array = $array;
        let array_len = array.len();
        let mut this = Self::with_capacity(array_len);

        // SAFETY: capacity ≥ new length
        unsafe {
            this.as_mut_ptr()
                .copy_from_nonoverlapping(array.as_ptr().cast(), array_len);
            this.set_len(array_len);
        }

        core::mem::forget(array);
        this
    }};
}

/// `from_slice_clone` impl, requires `with_capacity`, `as_mut_ptr`, `set_len`
macro_rules! from_slice_clone_impl {
    ($slice:expr) => {{
        use $crate::common::guarded_slice_clone;
        let slice = $slice;
        let len = slice.len();
        let mut this = Self::with_capacity(len);
        // SAFETY: capacity ≥ new length
        unsafe {
            guarded_slice_clone(this.as_mut_ptr(), slice.as_ptr(), len);
            this.set_len(len);
        }
        this
    }};
}

/// `extend_from_slice` impl, requires `len`, `reserve`, `as_mut_ptr`, `set_len`
macro_rules! extend_from_slice {
    ($self:ident, $slice:expr) => {{
        use $crate::common::utils::guarded_slice_clone;

        let slice = $slice;
        let slice_len = slice.len();
        $self.reserve(slice_len);

        // SAFETY: capacity ≥ new length
        unsafe {
            guarded_slice_clone(
                $self.as_mut_ptr().add($self.len()),
                slice.as_ptr(),
                slice_len,
            );
            $self.set_len($self.len() + slice_len);
        }
    }};
}

macro_rules! extend_from_slice_copy {
    ($self:ident, $slice:expr) => {{
        let slice = $slice;
        let slice_len = slice.len();
        $self.reserve(slice_len);

        if false {
            const fn is_copy<V, T: Copy>(_: fn(&V) -> *const T) {}
            is_copy(Self::as_ptr);
        }

        unsafe {
            $self
                .as_mut_ptr()
                .add($self.len())
                .copy_from_nonoverlapping(slice.as_ptr(), slice_len);
            $self.set_len($self.len() + slice_len);
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

macro_rules! remove {
    ($self:ident, $index:expr) => {{
        let len = $self.len();
        let index = $index;
        assert!(index < len, "index out of bounds");

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

macro_rules! swap_remove {
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

/// `append` impl
///
/// requirements:
/// - for `self`, `len`, `reserve`, `set_len`, `as_mut_ptr`, and `reserve`
/// - for `other`, `len`, `set_len`, and `as_ptr`
macro_rules! append_impl {
    ($self:ident, $other:ident) => {{
        let other_len = $other.len();
        $self.reserve(other_len);

        let self_len = $self.len();
        // SAFETY: capacity ≥ new length by `reserve`
        unsafe {
            $other.set_len(0);
            $self
                .as_mut_ptr()
                .add(self_len)
                .copy_from_nonoverlapping($other.as_ptr(), other_len);
            $self.set_len(self_len + other_len);
        }
    }};
}

/// `split_off` impl, requires `len`, `set_len`, and `as_ptr`, `as_mut_ptr` and `with_capacity`
macro_rules! split_off_impl {
    ($self:expr, $at:expr) => {{
        let at = $at;
        let len = $self.len();
        assert!(at <= len, "index out of bounds");

        let remainder = len - at;
        let mut other = Self::with_capacity(remainder);

        // SAFETY: `at` is checked above, and `other` has enough capacity
        unsafe {
            let ptr = $self.as_ptr().add(at);
            other.as_mut_ptr().copy_from_nonoverlapping(ptr, remainder);
            $self.set_len(at);
            other.set_len(remainder);
        }

        other
    }};
}

pub(crate) use append_impl;
pub(crate) use extend_from_array;
pub(crate) use extend_from_slice;
pub(crate) use extend_from_slice_copy;
pub(crate) use from_array_impl;
pub(crate) use from_slice_clone_impl;
pub(crate) use insert;
pub(crate) use insert_mut;
pub(crate) use pop;
pub(crate) use pop_if;
pub(crate) use push;
pub(crate) use push_mut;
pub(crate) use push_within_capacity;
pub(crate) use remove;
pub(crate) use remove_unchecked_impl;
pub(crate) use resize_impl;
pub(crate) use spare_capacity_mut;
pub(crate) use split_off_impl;
pub(crate) use swap_remove;
pub(crate) use truncate;
pub(crate) use truncate_copy;
