# Changelog

Notable changes only.

## 0.3.0

### Added

- Add support for Copy On Write for any lifetime (like `std::borrow::Cow`)
- Add opt-in `borrow_deserialize`
- More tests

### Changed

- Normalize representation of short allocated string to inlined string

### Removed

- On-demand inlining with `inline`

## 0.2.0 - 2023-07-06

### Fixed

- Fix bad assert when taking full slice

### Added

- Add mutable accessor (may clone data) `to_mut_slice` for `HipByt`, `to_mut_str` for `HipStr`
- Add forced inlining (`inline` method)
- More docs
- More CI
- Set MSRV

### Changed

- Lower `serde` version requirement

## 0.1.0 - 2023-06-01

Initial release
