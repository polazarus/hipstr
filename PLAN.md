# `ng` — next-generation hipstr

Breaking rewrite of `hipstr` in place (single crate).

## Decisions

| Topic | Decision |
|---|---|
| Layout | Single crate; vector machinery is internal (`vecs/`), only string/bytes types are public |
| Vectors | Ported from the `hipvec` branch, **copy-only** (`T: Copy`, used with `u8`); no `Copyness` marker, no non-copy code |
| MSRV / edition | 1.100 (latest stable at 2026-11-26) / 2024 — use it to remove `unsafe` |
| Dependencies | Small, well-known crates allowed where they cut `unsafe` or boilerplate |
| Vec heap | Kept: heap header may adopt a `Vec` buffer → O(1) `From<Vec>`/`From<String>` |
| Sizes | 3 words (today's), 2 words, 1 word — for all five families (bytes, str, CStr, OsStr, Path) |
| API shape | One generic core `Hip<'a, E: Encoding, R: Repr, B: Backend>` + aliases |
| 1-word borrowed | **None**: 1-word holds inline or heap only |
| Std compat | Full method parity + trait parity + differential test suite |

## Public names

| Family | 3 words (`Wide`) | 2 words (`Small`) | 1 word (`Tiny`) |
|---|---|---|---|
| str   | `HipStr<'a>`   | `SmallStr<'a>`   | `TinyStr`   |
| bytes | `HipByt<'a>`   | `SmallByt<'a>`   | `TinyByt`   |
| CStr  | `HipCStr<'a>`  | `SmallCStr<'a>`  | `TinyCStr`  |
| BStr (`bstr` feature) | `HipBStr<'a>` | `SmallBStr<'a>` | `TinyBStr` |
| OsStr | `HipOsStr<'a>` | `SmallOsStr<'a>` | `TinyOsStr` |
| Path  | `HipPath<'a>`  | `SmallPath<'a>`  | `TinyPath`  |

`Tiny*` types have no lifetime (they never borrow). Aliases default to `Arc`; `Local*`
variants (`LocalHipStr`, `LocalSmallStr`, `LocalTinyStr`, …) use `Rc`.

## Representations

| Repr | Size | Inline | Borrowed | Heap | Slicing |
|---|---|---|---|---|---|
| `Wide` | 3 words | ≤ 23 B | yes (`'a`) | thin + vec  | yes, O(1) shared |
| `Small` | 2 words | ≤ 15 B | yes (`'a`) | thin + vec  | no |
| `Tiny` | 1 word  | ≤ 7 B  | **no**     | thin + vec  | no |

(Byte counts for 64-bit.) The 2- and 1-word reprs convert to `Wide` in O(1) on the heap path
(`into_wide()`), then slice there.

Heap kinds: **thin** (elements right after the header) and **vec** (header pointing at
an adopted `Vec` buffer).

Layout constraints to prove with const asserts: exact size, `Option<_>` niche,
both endiannesses (Miri covers s390x / powerpc64). `Small` borrowed pointers to
`u8` are unaligned, so its tag must live in the high bits of the length word.

## Module plan

```
src/
  backend/      Rc / Arc / Unique (BackendImpl<C, PANIC_ON_OVERFLOW>), from hipvec
  vecs/         internal, copy-only
    header.rs   Header { count, ptr: Option<NonNull>, cap, len } shared by thin & vec heaps
    inline.rs   bit-packed inline buffer, capacity chosen by the repr
    thin.rs     data right after the header
    tagged.rs   tagged pointer on the strict-provenance API
    range.rs, drain.rs, splice.rs
  repr/         Repr trait + wide.rs / small.rs / tiny.rs
  enc/          Bytes / Utf8 / OsStr / Path markers: validation + std conversions
  hip.rs        Hip<'a, E, R, B> and its encoding-agnostic methods
  bytes/ string/ os_string/ path/   encoding-specific methods, generic over R, B
  compat/       ledger + trait-parity macros
```

## Phases

0. **Setup** — branch `ng` from `main`, edition 2024, MSRV 1.100, CI on `ng`. Audit
   release notes 1.86 → 1.100 for stabilizations that remove `unsafe`.
1. **Core port** from `hipvec` (copy-only): backend, header, tagged pointer, inline,
   thin, vec heap, drain, splice, with their tests.
   - *Status:* done in `src/next/` (temporary private module beside the current code,
     removed in phase 3). 107 unit tests pass, Miri-clean under `-Zmiri-strict-provenance`.
     Doc examples are `ignore`d until the items become public. The `Vec`-adopting
     path lives in `hipvec`'s `hip/base.rs` and moves over with phase 2.
2. **Three reprs** — layouts + asserts first (1-/2-word tagging is the main risk),
   then the `Repr` trait.
   - *Status:* done in `src/next/repr/` (`Wide`, `Small`, `Tiny` + shared heap `Owner`).
     The `Repr` trait has 4 raw primitives (`try_reserve`, `capacity`, `as_mut_ptr`,
     `set_len`); `push`/`extend_from_slice`/`truncate`/… are written once on top.
     Tests: one generic suite × 3 reprs × 3 backends, incl. a differential test vs
     `Vec<u8>`.
   - `Small` tag lives in the top 2 bits of the length word (`11` inline, `10` heap,
     `0x` borrowed): heap length ≤ 2^62−1 (2^30−1 on 32-bit), borrowed ≤ `isize::MAX`.
   - Inline layouts generalised (`LowLayout`, `HighLayout`); fixed a capacity bug that
     lost one inline byte (u8: 22 → 23 in 3 words).
   - Vec (adopting) heap: drop, O(1) `into_vec` and in-place growth implemented
     (was `todo!()` in `hipvec`).
   - Counters now initialise through a non-const `InitPrefix` trait, so loom's atomics
     fit; `ConstDefault` is kept only where const construction is really used.
3. **Encoding layer** — `Hip<E, R>`, aliases, port today's
   `HipByt`/`HipStr`/`HipOsStr`/`HipPath` API once, generically.
   - *Design:* `Hip<E, R>` takes the **concrete** repr (`Wide<'a, u8, B>`, …), not a
     layout marker + lifetime: a GAT projection would make the type invariant in `'a`.
     Root aliases fix the backend (`HipStr<'a>` = `Arc`, `LocalHipStr<'a>` = `Rc`);
     backend-generic aliases live in the family modules (`string::HipStr<'a, B>`),
     because alias defaults do not drive inference in expressions.
   - *API change:* `into_vec`/`into_string`/`into_os_string`/`into_path_buf` are
     infallible (O(1) when uniquely owning an adopted buffer, copy otherwise) instead
     of `Result<_, Self>`: thin heaps can never be taken without copying.
   - *Step 3a (done):* core (`hip.rs`), encodings, the 4 families' basic API,
     `Wide`-only slicing, std glue (conversions/comparisons both ways), tests per alias.
   - *Const accessors (done):* `len`, `is_empty`, `is_inline`, `is_borrowed`,
     `is_allocated`, `inline_capacity`, `new`, `borrowed`, `from_static` for every alias;
     `as_str`/`as_bytes`/`as_slice`/`as_ptr`/`as_borrowed`/`into_borrowed`/`from_utf8`/
     `from_utf8_unchecked`/`into_bytes` for str and bytes. Generated per representation
     (stable Rust cannot call trait methods in `const fn`). `tests.rs::const_accessors`
     evaluates them all at compile time. Not const: `HipOsStr`/`HipPath`
     `as_borrowed`/`into_borrowed` (std's conversions are not `const`; `main` relied on
     transmutes of std-internal layouts, dropped here).
   - *Step 3b (done):* str pattern methods (`trim*`, `split*`, `lines`, … returning
     shared slices on `HipStr`); `const` `inline`/`try_inline` for str and bytes, every
     size; serde (every family and size, `borrow_deserialize` copies for `Tiny*`),
     borsh, bstr.
     - Fixed vs `main`: `HipStr: Borrow<BStr>` broke `Borrow`'s contract (`str` and
       `BStr` hash differently) — strings now only get `AsRef<BStr>` + comparisons.
     - Fixed vs `main`: borsh decoding pre-allocated the untrusted length prefix (up to
       4 GiB); it now goes through borsh's `Vec<u8>` decoder and adopts its buffer.
   - *Step 3c (done):* swap — old modules removed, `src/next` moved to the crate root
     (vector machinery private: `common`, `inline`, `thin`, `traits`), old test suites
     and 88 doc blocks ported (139 doctests), loom tests rebuilt on the public types.
     - Old API restored where missing: the comparison grid (arrays, `Box`, `Cow`,
       cross-family OsStr↔Path, str↔OsStr), OsStr/Path conversions, `from_static`,
       `into_bytes`, `to_str_lossy`, `is_normalized`, `as_mut_ptr(_unchecked)`,
       `reserve`, `SliceError` messages, O(1) truncation of borrowed/shared views,
       in-place growth of unique sub-slices, borrowed slicing of borrowed values.
     - Bugs found by the old suites: `Header::from_vec` swapped length and capacity
       (ported from `hipvec`); `Wide` stored slice pointers derived from shared
       references and later wrote through them (UB under Stacked Borrows, found by
       Miri).
     - Intended changes (tests adapted, with comments): `into_vec`/`into_string`/…
       infallible; `capacity()` of a shared value is its length; heap capacities
       round up (`with_capacity(42)` may give 48); `HipOsStr::to_str` returns
       `Option<&str>` like std (the sharing version is `into_str`); `Borrow<BStr>`
       for strings and `Borrow<OsStr>` for paths dropped (hash mismatch).
     - Removed public modules: `vecs`, `smart`, `common`, and the deprecated
       `Local`/`ThreadSafe` backend aliases.
4. **Std compatibility** (done)
   - `compat/ledger.py` reads std's rustdoc JSON (`rust-docs-json`, nightly) and
     hipstr's, and lists every stable-at-MSRV inherent method of `Vec<u8>`, `String`,
     `CString`, `OsString`, `PathBuf` (+ `[u8]`, `str`, `CStr`, `OsStr`, `Path`; `BString`
     as `Vec<u8>`) with its status → committed `compat/LEDGER.md`. Deliberate gaps (raw
     parts, allocators, `as_mut_vec`, …) carry a reason in `compat/ledger.toml`. CI job
     `std-parity` fails on a gap or a stale ledger. `compat/UNSTABLE.md` (same script, not
     checked) keeps the std methods not stable at the MSRV — unstable, or stabilized
     later like `Vec::try_remove` / `String::into_chars` (1.101) — as candidates, marked
     done / via deref / candidate.
   - Methods: Vec API for byte strings (`vec_ops.rs`, shared by `HipByt` and `HipBStr`
     through `enc::Unconstrained`), String API (`string_ops.rs`), CString/OsString/PathBuf
     methods; `reserve*`/`try_reserve*` on every type (std's `TryReserveError`). Written
     in safe code over three repr primitives (`to_mut_slice`, `truncate`, `resize`) and
     `Hip::splice_bytes`. Values left unchanged by `retain`/`dedup`/empty ranges stay
     borrowed or shared. Iterators (`Drain`, `Splice`, `ExtractIf`) apply on drop and
     leave the value unchanged if leaked; `retain` is panic-safe.
   - Traits (`std_traits.rs`): copy-on-write `DerefMut`/`AsMut`/`BorrowMut` for bytes,
     `str`, `BStr`; `Add`/`AddAssign`; `IntoIterator` (owned, `&`, `&mut`); `io::Write`;
     the remaining `Extend`/`FromIterator`/`From`/`TryFrom`/`FromStr` impls; `From<Hip>`
     for `Box`/`Rc`/`Arc` slices. Trait parity is reviewed by hand (`ledger.py --traits`
     lists std's impls), not automated.
   - Modules renamed `bstr` / `cstr` (the crate's own `bstr` module shadows the `bstr`
     crate inside hipstr: external paths are written `::bstr::`).
5. **Differential tests** (done) — `tests/differential.rs`: `proptest` op sequences on
   `Vec<u8>`/`String` vs every size × Rc/Arc/Unique, starting owned, adopted or
   borrowed, with clones held to check copy-on-write; `PROPTEST_CASES` overrides the
   256 default; not run under Miri (too slow, half of it checks std). Panics, panic safety and leaks in
   `src/tests.rs::parity`.
3½. **C strings** (done) — `HipCStr`/`SmallCStr`/`TinyCStr` (+ `Local*`), `no_std` (`CStr` is
   in `core`, `CString` in `alloc`). Stored with the NUL terminator so they deref to
   `CStr` without copying; encodings now declare `EMPTY` and `TERMINATOR`, and `len`,
   `is_empty`, `capacity`, `inline_capacity` exclude the terminator (like
   `CStr::count_bytes`), so `TinyCStr` holds 6 bytes inline on 64-bit. `const`
   accessors (`as_c_str`, `as_bytes`, `as_bytes_with_nul`, `inline`, `borrowed`,
   `from_static` with `c"…"` literals), `CString` round trip without copy,
   `TryFrom` like `CString::new`, comparisons, serde.
3¾. **bstr byte strings** (done, `bstr` feature) — `HipBStr`/`SmallBStr`/`TinyBStr` (+ `Local*`),
   dereferencing to `bstr::BStr` (its string-like API, text `Debug`/`Display`). `bstr`
   guarantees `&BStr` ≡ `&[u8]`, so conversions are casts and the accessors are `const`
   (`as_bstr`, `as_bytes`, `borrowed_bytes` for byte literals, `inline`, …). Storage kept
   across `HipByt`/`HipStr` conversions; comparisons with `BStr`/`BString`/bytes/`str`;
   `Borrow<[u8]>` (hashes match); serde and borsh as bytes. Replaces `main`'s
   feature-dependent `Deref` of `HipByt` to `BStr` (non-additive).
6. **Finish** (done) — benches across sizes (`benches/main.rs::sizes`), crate docs,
   README, CHANGELOG (Unreleased), `MIGRATION.md`. The unused vendored `hipvec` code
   (`ThinVec`, `InlineVec`, generic drain/splice, method macros, vector traits) was
   removed: about 5,400 lines (1,200 remain: thin heap, inline layouts, header, tagged pointer).
   - Follow-ups: version number for the release; bulk byte operations (`retain`,
     `drain`) are ~3× slower than `Vec`'s (safe compaction); `reserve_exact` is
     `reserve`.

7. **Inline types** (done) — `inline::Inline<E, N>`: `N ≤ 254` data bytes and a
   `NonZeroU8` length (`len + 1`, the niche), `Copy`, data fully initialized (zeroes past
   the length, so equal values have equal bytes). Root aliases fix `N = 23`
   (`InlineStr` is 24 bytes; alias defaults do not drive inference in expressions),
   `inline::InlineStr<N>` & co are capacity-generic. `const`: construction (`new`,
   `inline`, `try_inline`), accessors, and edits for bytes/`str` (`push`, `push_str`,
   `pop`, `truncate`, `insert`, `remove`, `swap_remove`, ASCII case, `from_utf8`);
   C strings: `inline`, `as_c_str`, `truncate`; OS strings/paths only get the
   encoding-agnostic `const` core (std's conversions are not `const`). Follow-ups:
   serde/borsh, `retain` is not `const` (closures).
8. **Inline construction speed** (done) — `from_slice` split into an inlinable inline
   branch and an out-of-line heap path; byte inline values are built in registers
   (`Base::from_bytes_wordwise`: overlapping little-endian loads, shifted by the data
   offset, tag OR-ed in, whole-word stores) to avoid a store-forwarding stall. Direct
   loop timing (ns, 64-bit): `HipStr` 3.3–6.6 (was ~12; 0.8: 3.5–8.4), `SmallStr`
   1.7–3.4, `TinyStr` 1.5–2.0, `CompactString` 1.9–3.4.

## Open questions

  Repr names: `Wide` (3 words) / `Small` (2 words) / `Tiny` (1 word).
- `Unique` backend semantics on clone (deep copy, as today?). *Implemented as deep copy.*
- Vec-heap growth maps `Vec::try_reserve` errors to "capacity overflow" (the allocation
  error kind is unstable), so OOM on that path panics instead of aborting.
- O(1) shortcuts not yet taken: truncating a borrowed/shared value copies instead of
  shrinking the view.
