# Changelog

Notable changes only.

## [0.3.2] - 2023-08-18

## Added

- Add trait impls for OsStr/Path compatibility
- Add push_str and push
- Add performance chart generation

## [0.3.1] - 2023-08-14

### Changed

- Improve overall performances
- Add more state of the art in the README

## [0.3.0] - 2023-08-12

### Added

- Add support for Copy On Write for any lifetime (like `std::borrow::Cow`)
- Add opt-in `borrow_deserialize`
- More tests

### Changed

- Normalize representation of short allocated string to inlined string

### Removed

- On-demand inlining with `inline`

## [0.2.0] - 2023-07-06

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

## [0.1.0] - 2023-06-01

Initial release

[0.3.2]: https://github.com/polazarus/hipstr/compare/0.3.1...0.3.2
[0.3.1]: https://github.com/polazarus/hipstr/compare/0.3.0...0.3.1
[0.3.0]: https://github.com/polazarus/hipstr/compare/0.2.0...0.3.0
[0.2.0]: https://github.com/polazarus/hipstr/compare/0.1.0...0.2.0
[0.1.0]: https://github.com/polazarus/hipstr/releases/tag/0.1.0