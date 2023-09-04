use core::mem::size_of;

use hipstr::Backend;

struct BadBackend;

unsafe impl Backend for BadBackend {
    type RawPointer = [u8; size_of::<usize>()];

    #[inline]
    fn new(_: Vec<u8>) -> Self {
        panic!()
    }

    #[inline]
    fn try_unwrap(self) -> Result<Vec<u8>, Self> {
        panic!()
    }

    #[inline]
    fn into_raw(self) -> Self::RawPointer {
        panic!()
    }

    #[inline]
    unsafe fn from_raw(_raw: Self::RawPointer) -> Self {
        panic!()
    }

    #[inline]
    unsafe fn raw_increment_count(_raw: Self::RawPointer) {
        panic!()
    }

    #[inline]
    unsafe fn raw_decrement_count(_: Self::RawPointer) {
        panic!()
    }

    #[inline]
    unsafe fn raw_is_unique(_: Self::RawPointer) -> bool {
        panic!()
    }

    #[inline]
    unsafe fn raw_as_vec<'a>(_: Self::RawPointer) -> &'a Vec<u8> {
        panic!()
    }

    #[inline]
    unsafe fn raw_get_mut_unchecked<'a>(_: Self::RawPointer) -> &'a mut Vec<u8> {
        panic!()
    }

    #[inline]
    fn raw_is_valid(_: Self::RawPointer) -> bool {
        panic!()
    }
}

const _: () = {
    hipstr::check_backend::<BadBackend>();
};

fn main() {
    let _h = hipstr::string::HipStr::<'static, BadBackend>::new();
}
