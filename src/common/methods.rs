use core::mem::MaybeUninit;
use core::ptr::NonNull;

macro_rules! methods {
    ($( #[ $attr:meta ] )* $visibility:vis fn $($tail:tt)* ) => {
        methods!(@ [ $([$attr])* , $visibility, ,] $($tail)*);
    };

    ($( #[ $attr:meta ] )* $visibility:vis const fn $($tail:tt)* ) => {
        methods!(@ [ $([$attr])* , $visibility, const, ] $($tail)*);
    };

    ($( #[ $attr:meta ] )* $visibility:vis const unsafe fn $($tail:tt)* ) => {
        methods!(@ [ $([$attr])* , $visibility, const, unsafe ] $($tail)*);
    };

    ($( #[ $attr:meta ] )* $visibility:vis unsafe fn $($tail:tt)* ) => {
        methods!(@ [ $([$attr])* , $visibility, , unsafe ] $($tail)*);
    };


    (@ [ $([$attr:meta])*, $visibility:vis, $($const:ident)?, ] spare_capacity_mut <$T:path>) => {
        $(#[ $attr ])*
        $visibility $($const)? fn spare_capacity_mut(&mut self) -> &mut [MaybeUninit<$T>] {
            let ptr = self.as_mut_ptr();
            let len = self.len();
            let capacity = self.capacity();
            let spare_len = capacity - len;
            unsafe { core::slice::from_raw_parts_mut(ptr.add(len).cast(), spare_len) }
        }
    };

    (@ [ $([$attr:meta])*, $visibility:vis, $($const:ident)?, ] try_push) => {
        $(#[ $attr ])*
        $visibility $($const)? fn try_push(&mut self, value: T) -> Result<(), T> {
            let len = self.len();
            if len < self.capacity() {
                // SAFETY: capacity is guaranteed to be greater than length
                unsafe {
                    let ptr = self.as_mut_ptr().add(len);
                    ptr.write(value);
                    self.set_len(len + 1);
                }
                Ok(())
            } else {
                Err(value)
            }
        }
    };


    (@ [ $([$attr:meta])*, $visibility:vis, $($const:ident)?, ] pop) => {
        $(#[ $attr ])*
        $visibility $($const)? fn pop(&mut self) -> Option<T> {
            let len = self.len();
            if len > 0 {
                // SAFETY: length is guaranteed to be greater than zero
                unsafe {
                    let ptr = self.as_mut_ptr().add(len - 1);
                    let value = ptr.read();
                    self.set_len(len - 1);
                    Some(value)
                }
            } else {
                None
            }
        }
    };

    (@ [ $([$attr:meta])*, $visibility:vis, , ] pop_if) => {
        $(#[ $attr ])*
        $visibility fn pop_if(&mut self, f: impl FnOnce(&T) -> bool) -> Option<T> {
            let len = self.len();
            if len > 0 {
                // SAFETY: length is guaranteed to be greater than zero
                let ptr = unsafe { self.as_mut_ptr().add(len - 1) };
                // SAFETY: we are reading from a valid pointer
                if f(unsafe { &*ptr }) {
                    // move out the last element

                    // SAFETY: the length decreases
                    unsafe { self.set_len(len - 1); }

                    // SAFETY: length is guaranteed to be greater than zero
                    let value = unsafe { ptr.read() };
                    return Some(value);
                }
            }
            None
        }
    };

    (@ [ $([$attr:meta])*, $visibility:vis, $($const:ident)?, ] try_append) => {
        $(#[ $attr ])*
        $visibility $($const)? fn try_append(&mut self, other: &mut Self) -> bool{
            let old_len = self.len();
            let new_len = old_len + other.len();
            if new_len <= self.capacity() {
                let dst = unsafe { self.as_mut_ptr().add(old_len) };
                unsafe {
                    self.set_len(new_len);
                    other.set_len(0);
                    dst.copy_from_nonoverlapping(other.as_mut_ptr(), other.len());
                }
            }
        }
    };

    (@ [ $([$attr:meta])*, $visibility:vis, $($const:ident)?, $($unsafe:ident)?] truncate) => {
        $(#[ $attr ])*
        $visibility $($const)? $($unsafe)? fn truncate(&mut self, new_len: usize) {
            let old_len = self.len();
            if new_len < old_len {
                // SAFETY: strict decrease
                unsafe {
                    self.set_len(new_len);
                }

                // SAFETY: type invariant
                unsafe {
                    $crate::common::drop_slice(
                        self.as_mut_ptr().add(new_len),
                        old_len - new_len,
                    );
                }
            }
        }
    };

    (@ [ $([$attr:meta])*, $visibility:vis, $($const:ident)?, ] clear) => {
        $(#[ $attr ])*
        $visibility $($const)? fn clear(&mut self) {
            self.truncate(0);
        }
    };

}

pub(crate) use methods;

#[derive(Debug, Clone, Copy)]
pub struct MutableView<'a, T> {
    ptr: NonNull<T>,
    capacity: usize,
    len: usize,
    phantom: core::marker::PhantomData<&'a [T]>,
}

impl<'a, T> MutableView<'a, T> {
    pub const unsafe fn new(ptr: NonNull<T>, capacity: usize, len: usize) -> Self {
        Self {
            ptr,
            capacity,
            len,
            phantom: core::marker::PhantomData,
        }
    }

    pub const fn as_mut_slice(self) -> &'a mut [T] {
        unsafe { core::slice::from_raw_parts_mut(self.ptr.as_ptr(), self.len) }
    }

    pub const fn spare_capacity_mut(self) -> &'a mut [MaybeUninit<T>] {
        unsafe {
            let start = self.ptr.add(self.len).cast();
            core::slice::from_raw_parts_mut(start.as_ptr(), self.capacity - self.len)
        }
    }

    pub fn append(self, other: Self) -> Option<(usize, usize)> {
        if self.len + other.len <= self.capacity {
            let dst = unsafe { self.ptr.add(self.len) };
            unsafe {
                dst.copy_from_nonoverlapping(other.ptr, other.len);
            }
            Some((self.len + other.len, 0))
        } else {
            None
        }
    }
}
