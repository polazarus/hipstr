use super::*;
use crate::alloc::vec;

#[test]
fn test_basic_rc() {
    test_backend::<Local>();
}

#[test]
fn test_basic_arc() {
    test_backend::<ThreadSafe>();
}

fn test_backend<B: Backend>() {
    private::check_backend::<B>();

    let v = vec![42; 42];
    let p = v.as_ptr();
    unsafe {
        let r = B::into_raw(B::new(v));
        assert!(B::raw_is_valid(r));
        assert!(B::raw_is_unique(r));
        {
            let v = B::raw_as_vec(r);
            assert_eq!(v.len(), 42);
        }
        {
            let v = B::raw_get_mut_unchecked(r);
            assert_eq!(p, v.as_ptr());
        }

        B::raw_increment_count(r);
        assert!(!B::raw_is_unique(r));
        B::raw_decrement_count(r);

        let v = B::raw_try_unwrap(r).unwrap_or_else(|_| panic!());
        assert_eq!(v.len(), 42);
    }
}
