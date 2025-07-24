use core::hint::unreachable_unchecked;

pub trait NZ: Copy + 'static {
    type NonZero: Copy + 'static;
}

macro_rules! non_zero_impl {
    ($($t:ty),* $(,)?) => {
        $(
            impl NZ for $t {
                type NonZero = core::num::NonZero<$t>;
            }
        )*
    };
}

non_zero_impl! {
    u8, u16, u32, u64, usize
}

pub const fn from_usize<T: NZ>(value: usize) -> Option<T::NonZero> {
    #[repr(C, packed)]
    union Tr<A: Copy, B: Copy> {
        a: A,
        b: B,
    }
    const fn transmute<A: Copy, B: Copy>(a: A) -> B {
        unsafe { Tr { a }.b }
    }

    const {
        assert!(
            size_of::<T>() <= size_of::<usize>(),
            "size of T must not exceed size of usize"
        );
    }

    unsafe {
        #[expect(
            clippy::cast_possible_truncation,
            reason = "we know the value is small enough"
        )]
        match size_of::<T>() {
            1 => transmute(value as u8),
            2 => transmute(value as u16),
            4 => transmute(value as u32),
            8 => transmute(value as u64),
            _ => unreachable_unchecked(),
        }
    }
}

pub const fn into_usize<T: NZ>(value: T::NonZero) -> usize {
    #[repr(C, packed)]
    union Tr<A: Copy, B: Copy> {
        a: A,
        b: B,
    }
    const fn transmute<A: Copy, B: Copy>(a: A) -> B {
        unsafe { Tr { a }.b }
    }

    unsafe {
        #[expect(clippy::cast_possible_truncation, reason = "may happen")]
        match size_of::<T>() {
            1 => transmute::<_, u8>(value) as usize,
            2 => transmute::<_, u16>(value) as usize,
            4 => transmute::<_, u32>(value) as usize,
            8 => transmute::<_, u64>(value) as usize,
            _ => unreachable_unchecked(),
        }
    }
}
