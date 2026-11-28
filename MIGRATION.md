# Migrating from hipstr 0.8

The new version keeps the type names (`HipStr`, `HipByt`, `HipOsStr`,
`HipPath`, `LocalHipStr`, …) and most of their API. They are now aliases of
one generic type, `hipstr::Hip<E, R>` (encoding × representation), which also
provides smaller sizes and std's full API.

## Things that no longer compile

| 0.8 | Now |
|---|---|
| `s.into_string()` → `Result<String, Self>` | `s.into_string()` → `String` (O(1) when possible, else copies); same for `into_vec`, `into_os_string`, `into_path_buf` |
| `os.to_str()` → `Option<HipStr>` | `os.to_str()` → `Option<&str>` (std's); `os.into_str()` → `Result<HipStr, Self>` keeps the storage |
| `hipstr::vecs`, `hipstr::smart`, `hipstr::common` | removed (internal) |
| `hipstr::Local`, `hipstr::ThreadSafe` | `hipstr::Rc`, `hipstr::Arc` |
| `HipByt` deref to `BStr` (`bstr` feature) | `HipBStr` (derefs to `BStr`), or `bytes.as_ref()` as `&BStr` |
| `HipStr: Borrow<BStr>` | `AsRef<BStr>`, comparisons with `BStr` (the `Borrow` impl broke hashing) |
| `HipPath: Borrow<OsStr>` | `AsRef<OsStr>`, comparisons (same reason) |
| backend-generic `string::HipStr<'a, B>` | unchanged; also `string::SmallStr<'a, B>`, `string::TinyStr<B>` |
| `try_reserve` on the old internal vectors | `try_reserve` on every type, returning std's `TryReserveError` |
| `HipStr::try_from(bytes)` error: `FromUtf8Error` (bytes back with `into_bytes`) | `ConvertError<HipByt, Utf8Error>` (`into_source()`, `reason()`); same for every `TryFrom` between families. `HipStr::from_utf8` keeps `FromUtf8Error` |

Writing generic code over the old types: name the generic type
`Hip<E, R>` with `E: hipstr::enc::Encoding` and `R: hipstr::Repr<'a>`. The
representations themselves are not public: name them through the aliases
(`string::HipStr<'a, B>`, `string::SmallStr<'a, B>`, …), and `Repr` is sealed.

With `default-features = false`, enable the representations (`hip`, `small`,
`tiny`) and families (`bytes`, `str`, `cstr`, `osstr`, `path`) you use: in
0.8, `default-features = false` only turned `std` off. For example,
`features = ["hip", "str"]` gives `HipStr` without `std`. `osstr` and `path`
imply `std`.

## Things that behave differently

- **Getting buffers back.** `From<String>`, `From<Vec<u8>>`, `From<PathBuf>`,
  … still take the buffer without copying for the 3-word types (`HipStr`, …);
  `into_string`/`into_vec`/… give it back in O(1) if it is still uniquely
  owned, and copy otherwise instead of failing. The new 2- and 1-word types
  (`SmallStr`, `TinyStr`, …) always copy, both ways.
- **Capacity.** `capacity()` of a shared value is its length (writing needs a
  copy first). Heap capacities may be rounded up: `with_capacity(42)` may
  report 48.
- **Mutable access.** Strings, byte strings and `HipBStr` now implement
  `DerefMut`, `AsMut` and `BorrowMut`, copy-on-write: `&mut *s`, `s[0] = b'x'`
  or `for b in &mut bytes` copy a borrowed or shared value first, exactly
  like `to_mut_str`/`to_mut_slice`.
- **MSRV** is 1.100 and the crate uses edition 2024.

## New

- Smaller sizes: `SmallStr` (2 words: inline up to 15 bytes, borrowed or
  shared, no O(1) slicing) and `TinyStr` (1 word: inline up to 7 bytes or
  shared, never borrowed), for every family; `Local*` variants use `Rc`.
- C strings (`HipCStr`, …) and, with the `bstr` feature, `HipBStr`, ….
- The std API of `String`, `Vec<u8>`, `CString`, `OsString`, `PathBuf`:
  see `compat/LEDGER.md` for the full list.
