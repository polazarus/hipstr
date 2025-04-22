#![allow(clippy::reversed_empty_ranges)]

use alloc::format;

use super::*;

#[test]
fn ranges() {
    assert_eq!(range(0..5, 10).unwrap(), 0..5);
    assert_eq!(range(0..=5, 10).unwrap(), 0..6);
    assert_eq!(range(..5, 10).unwrap(), 0..5);
    assert_eq!(range(..=5, 10).unwrap(), 0..6);
    assert_eq!(range(2.., 10).unwrap(), 2..10);

    let err = range(..=usize::MAX, 1).unwrap_err();
    assert_eq!(err, RangeError::EndOverflows);
    assert_eq!(format!("{err}"), "end index overflows");
    assert_eq!(err.const_message(), "end index overflows");

    let err = range((Bound::Excluded(usize::MAX), Bound::Unbounded), 10).unwrap_err();
    assert_eq!(err, RangeError::StartOverflows);
    assert_eq!(format!("{err}"), "start index overflows");
    assert_eq!(err.const_message(), "start index overflows");

    let err = range(5..2, 10).unwrap_err();
    assert_eq!(err, RangeError::StartGreaterThanEnd { start: 5, end: 2 });
    assert_eq!(
        format!("{err}"),
        "start index 5 is greater than end index 2"
    );
    assert_eq!(err.const_message(), "start index is greater than end index");

    let err = range(5..10, 5).unwrap_err();
    assert_eq!(err, RangeError::EndOutOfBounds { end: 10, len: 5 });
    assert_eq!(
        format!("{err}"),
        "end index 10 is out of bounds for slice of length 5"
    );
    assert_eq!(err.const_message(), "end index is out of bounds");

    assert_eq!(
        range(6..10, 5).unwrap_err(),
        RangeError::EndOutOfBounds { end: 10, len: 5 }
    );
    assert_eq!(
        format!("{err}"),
        "end index 10 is out of bounds for slice of length 5"
    );
    assert_eq!(err.const_message(), "end index is out of bounds");
}

#[test]
fn maybe_uninit_write_copy_of_slice_success() {
    let mut buf = [MaybeUninit::<u8>::uninit(); 4];
    let slice = [1, 2, 3, 4];
    maybe_uninit_write_copy_of_slice(&mut buf, &slice);
    unsafe {
        assert_eq!(buf[0].assume_init(), 1);
        assert_eq!(buf[1].assume_init(), 2);
        assert_eq!(buf[2].assume_init(), 3);
        assert_eq!(buf[3].assume_init(), 4);
    }
}

#[test]
#[should_panic(expected = "source slice length does not match destination slice length")]
fn maybe_uninit_write_copy_of_slice_panic() {
    let mut buf = [MaybeUninit::<u8>::uninit(); 4];
    let slice = [1, 2, 3, 4, 5];
    maybe_uninit_write_copy_of_slice(&mut buf, &slice);
}
