# Changelog

Notable changes only.

## [Unreleased]

A rewrite of the crate around one generic type, `Hip<E, R>` (encoding ×
representation), with the old names kept as aliases. See
[MIGRATION.md](MIGRATION.md).

### Added

- 2-word (`SmallStr`, `SmallByt`, …) and 1-word (`TinyStr`, `TinyByt`, …)
  types for every family, beside the 3-word `HipStr`, `HipByt`, …
- fixed-capacity inline types: `InlineStr`, `InlineByt`, `InlineCStr`,
  `InlineBStr`, `InlineOsStr`, `InlinePath` (`inline::InlineStr<N>` for any
  capacity up to 254 bytes): `Copy`, never allocating, with a `const` API
  (construction, accessors, `push`, `push_str`, `pop`, `insert`, `remove`,
  `truncate`, …) and `try_` versions returning `CapacityError`
- C strings: `HipCStr`, `SmallCStr`, `TinyCStr` (`no_std`), dereferencing to
  `CStr` without copy
- `bstr` byte strings: `HipBStr`, `SmallBStr`, `TinyBStr` (`bstr` feature),
  dereferencing to `bstr::BStr`
- std method parity: the `Vec<u8>` API on byte strings (`insert`, `remove`,
  `drain`, `splice`, `extract_if`, `retain`, `dedup`, `resize`, `split_off`,
  `append`, …), the `String` API on strings (`insert_str`, `replace_range`,
  `retain`, `drain`, `split_off`, `from_utf16le`, …), `try_reserve`,
  `reserve_exact`, `into_boxed_*`, `leak`, and the `CString`, `OsString`,
  `PathBuf` methods (`push`/`pop`/`set_extension` on paths, …)
- std trait parity: `DerefMut`/`AsMut`/`BorrowMut` (copy-on-write) for bytes,
  strings and `BStr`; `Add`/`AddAssign<&str>`; owning and borrowing
  `IntoIterator`; `io::Write`; more `Extend`/`FromIterator`/`From`/`TryFrom`;
  `From<_>` for `Box`/`Rc`/`Arc` slices
- faster inline construction: values are built word by word in registers
  (2–4× faster than the first rewrite, on par with 0.8 for 3 words and faster
  for 2 and 1 word)
- `const` accessors (`len`, `is_empty`, `as_ptr`, `as_str`, `as_slice`, …) on
  every type
- `compat/LEDGER.md`: every stable std method and its status, checked in CI
- differential tests against `Vec<u8>` and `String`

### Changed

- **breaking**: `into_vec`, `into_string`, `into_os_string`, `into_path_buf`
  are infallible (O(1) when the value uniquely owns an adopted buffer)
- **breaking**: `HipOsStr::to_str` returns `Option<&str>` like std (the sharing
  conversion is `into_str`)
- **breaking**: `capacity()` of a shared value is its length; heap capacities
  may be rounded up
- **breaking**: with the `bstr` feature, `HipByt` no longer dereferences to
  `BStr` (feature-dependent `Deref` was not additive): use `HipBStr`, or
  `AsRef<BStr>`
- **breaking**: public modules `vecs`, `smart`, `common` and the deprecated
  `Local`/`ThreadSafe` backend aliases removed; new public modules `bstr`,
  `cstr`, `enc`, `hip`, `repr`
- MSRV 1.100, edition 2024; no more exposed provenance (Miri strict
  provenance clean)
- `shrink_to`/`shrink_to_fit` shrink uniquely owned buffers in place
  (`realloc`) and leave shared ones alone, unless the value shows only part
  of the buffer (then copied, so that the rest can be freed)
- `split_off` on 3-word values shares the buffer (O(1)) instead of copying
  the tail
- `into_vec` (and the other `into_*`) copy only the visible bytes of a
  shortened or shared value
- `extract_if` and `String`-style `retain` unshare the value once, not per
  element

### Fixed

- `HipStr: Borrow<BStr>` and `HipPath: Borrow<OsStr>` violated `Borrow`'s
  contract (different hashes): removed
- borsh deserialization pre-allocated the untrusted length prefix
- `HipOsStr::push` (and `Extend`/`FromIterator` of OS strings) on Windows
  could build ill-formed WTF-8 from a surrogate pair split across the two
  strings: the pair is now joined, like `OsString::push`
- `reserve_exact`/`try_reserve_exact` grew geometrically

## [0.8.0] - 2025-02-10

### Added

- add `as_ptr` to strings.
- add `as_mut_ptr` and `as_mut_ptr_unchecked` to strings and bytes

### Changed

- improve feature testing in CI
- improve doc
- update some dev dependencies

### Fixed

- remove accidentally mandatory dependency to `serde`
- fix `bstr` feature in `no_std`
- fix some clippy lints

## [0.7.0] - 2025-01-10

### Added

- add new unique (non-shared) strings and byte vectors
- add `as_borrowed`
- add inline `const` constructors
- add opt-in borsh serialization support for bytes and strings
- add new comparisons with `bstr` types
- add some missing comparisons

### Changed

- refactor the backend to support unique references
- remove low-level `Raw` type
- improve deserialization for strings, bytes and paths, see [#38](https://github.com/polazarus/hipstr/pull/38) and follow-up work
- bump minimum supported Rust version (msrv) to 1.84

### Removed

- remove `serde_bytes` dependency
- remove `sptr` dependency (following provenance API stabilization in Rust 1.84)

### Fixed

- compilation with `serde` for non-Windows non-Unix targets, in particular wasm

## [0.6.0] - 2024-10-08

### Changed

- implement `core::error:Error` for custom errors, rather than
  `std::error::Error` and bump msrv

### Fixed

- fix doc issue [#28](https://github.com/polazarus/hipstr/issues/28)
- fix MIRI check due to provenance loss
  [#32](https://github.com/polazarus/hipstr/pull/32)

- fix some new clippy lints (and some future lints)

## [0.5.1] - 2024-08-02

### Added

- add optional `bstr` crate support
- add `truncate`, `pop`, and `clear`
- add `concat` and `join`
- add `with_capacity`
- add `shrink_to_fit` and `shrink`

### Fixed

- some clippy lints
- fix truncating `set_len` on borrowed
- fix truncating `set_len` on allocated

## [0.5.0] - 2024-06-24

### Added

- new conversion to `Cow`s
- a niche to make `Option<HipStr>` the same size as `HipStr`

### Changed

- update MSRV to 1.77
- backend complete overall with its own custom RC implementation

### Fixed

- fixed some clippy lints

## [0.4.0] - 2023-12-01

### Added

- add `HipPath` and `HipOsStr` (#11)
- more methods to keep working with `Hip*` types when possible (#13)
- add pattern methods on `HipStr` (#17)
- more comparisons (#15)

Most of those addition are breaking because they shadows `str`'s methods.

### Changed

- make equality more efficient (#12 then #18)
- better coverage with more tests (#14)

## [0.3.3] - 2023-10-30

### Fixed

- fix clippy lint in `bytes/cmp.rs`
- fix missing `std::error::Error` impl for `string::SliceError`

## [0.3.2] - 2023-08-18

### Added

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

- Add mutable accessor (may clone data) `to_mut_slice` for `HipByt`,
  `to_mut_str` for `HipStr`
- Add forced inlining (`inline` method)
- More docs
- More CI
- Set MSRV

### Changed

- Lower `serde` version requirement

## [0.1.0] - 2023-06-01

Initial release

<!-- [unreleased]: https://github.com/polazarus/hipstr/compare/0.8.0...HEAD -->

[0.8.0]: https://github.com/polazarus/hipstr/compare/0.7.0...0.8.0
[0.7.0]: https://github.com/polazarus/hipstr/compare/0.6.0...0.7.0
[0.6.0]: https://github.com/polazarus/hipstr/compare/0.5.1...0.6.0
[0.5.1]: https://github.com/polazarus/hipstr/compare/0.5.0...0.5.1
[0.5.0]: https://github.com/polazarus/hipstr/compare/0.4.0...0.5.0
[0.4.0]: https://github.com/polazarus/hipstr/compare/0.3.3...0.4.0
[0.3.3]: https://github.com/polazarus/hipstr/compare/0.3.2...0.3.3
[0.3.2]: https://github.com/polazarus/hipstr/compare/0.3.1...0.3.2
[0.3.1]: https://github.com/polazarus/hipstr/compare/0.3.0...0.3.1
[0.3.0]: https://github.com/polazarus/hipstr/compare/0.2.0...0.3.0
[0.2.0]: https://github.com/polazarus/hipstr/compare/0.1.0...0.2.0
[0.1.0]: https://github.com/polazarus/hipstr/releases/tag/0.1.0
