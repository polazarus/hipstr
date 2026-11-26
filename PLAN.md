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
| Sizes | 3 words (today's), 2 words, 1 word — for all four families (bytes, str, OsStr, Path) |
| API shape | One generic core `Hip<'a, E: Encoding, R: Repr, B: Backend>` + aliases |
| 1-word borrowed | **None**: 1-word holds inline or heap only |
| Std compat | Full method parity + trait parity + differential test suite |

## Public names

| Family | 3 words (`Wide`) | 2 words (`Small`) | 1 word (`Tiny`) |
|---|---|---|---|
| str   | `HipStr<'a>`   | `SmallStr<'a>`   | `TinyStr`   |
| bytes | `HipByt<'a>`   | `SmallByt<'a>`   | `TinyByt`   |
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
3. **Encoding layer** — `Hip<E, R, B>`, aliases, port today's
   `HipByt`/`HipStr`/`HipOsStr`/`HipPath` API once, generically.
4. **Std compatibility**
   - Ledger generated from std's rustdoc JSON (`rust-docs-json` component) listing every
     stable inherent method and trait impl of `Vec<u8>`, `String`, `OsString`, `PathBuf`
     (+ `[u8]`, `str`, `OsStr`, `Path`) → `compat/ledger.toml` with status
     (done / n/a / planned); a test fails on unlisted std items.
   - Method parity: same names and signatures, including mutating ones (COW when shared).
   - Trait parity: macro-generated `PartialEq`/`PartialOrd` grid vs. all std counterparts,
     `Extend`, `FromIterator`, `fmt::Write`/`io::Write`, `Index`, `Borrow`, `Hash`, …
5. **Differential tests** — same operations on std and on every alias
   (3 sizes × Rc/Arc/Unique), handwritten scenarios + `proptest` op sequences.
6. **Finish** — serde/bstr/borsh, benches across sizes, docs, migration guide.

## Open questions

  Repr names: `Wide` (3 words) / `Small` (2 words) / `Tiny` (1 word).
- `Unique` backend semantics on clone (deep copy, as today?). *Implemented as deep copy.*
- Vec-heap growth maps `Vec::try_reserve` errors to "capacity overflow" (the allocation
  error kind is unstable), so OOM on that path panics instead of aborting.
- O(1) shortcuts not yet taken: truncating a borrowed/shared value copies instead of
  shrinking the view.
