# `ng` — next-generation hipstr

Breaking rewrite of `hipstr` in place (single crate).

## Decisions

| Topic | Decision |
|---|---|
| Layout | Single crate; vector machinery is internal (`vecs/`), only string/bytes types are public |
| Vectors | Ported from the `hipvec` branch, **copy-only** (`T: Copy`, used with `u8`); no `Copyness` marker, no non-copy code |
| MSRV / edition | 1.100 (latest stable at 2026-11-26) / 2024 — use it to remove `unsafe` |
| Dependencies | Small, well-known crates allowed where they cut `unsafe` or boilerplate |
| Wide repr | Kept: heap header may adopt a `Vec` buffer → O(1) `From<Vec>`/`From<String>` |
| Sizes | 3 words (today's), 2 words, 1 word — for all four families (bytes, str, OsStr, Path) |
| API shape | One generic core `Hip<'a, E: Encoding, R: Repr, B: Backend>` + aliases |
| 1-word borrowed | **None**: 1-word holds inline or heap only |
| Std compat | Full method parity + trait parity + differential test suite |

## Representations

| Repr | Size | Inline | Borrowed | Heap | Slicing |
|---|---|---|---|---|---|
| `Fat`  | 3 words | ≤ 23 B | yes (`'a`) | thin + wide | yes, O(1) shared |
| `Pair` | 2 words | ≤ 15 B | yes (`'a`) | thin + wide | no |
| `Thin` | 1 word  | ≤ 7 B  | **no**     | thin + wide | no |

(Byte counts for 64-bit.) Small reprs convert to `Fat` in O(1) on the heap path
(`into_fat()`), then slice there.

Layout constraints to prove with const asserts: exact size, `Option<_>` niche,
both endiannesses (Miri covers s390x / powerpc64). `Pair` borrowed pointers to
`u8` are unaligned, so its tag must live in the high bits of the length word.

## Module plan

```
src/
  backend/      Rc / Arc / Unique (BackendImpl<C, PANIC_ON_OVERFLOW>), from hipvec
  vecs/         internal, copy-only
    header.rs   Header { count, ptr: Option<NonNull>, cap, len } shared by thin & wide
    inline.rs   bit-packed inline buffer, capacity chosen by the repr
    thin.rs     data right after the header
    tagged.rs   tagged pointer on the strict-provenance API
    range.rs, drain.rs, splice.rs
  repr/         Repr trait + fat.rs / pair.rs / thin.rs
  enc/          Bytes / Utf8 / OsStr / Path markers: validation + std conversions
  hip.rs        Hip<'a, E, R, B> and its encoding-agnostic methods
  bytes/ string/ os_string/ path/   encoding-specific methods, generic over R, B
  compat/       ledger + trait-parity macros
```

## Phases

0. **Setup** — branch `ng` from `main`, edition 2024, MSRV 1.100, CI on `ng`. Audit
   release notes 1.86 → 1.100 for stabilizations that remove `unsafe`.
1. **Core port** from `hipvec` (copy-only): backend, header, tagged pointer, inline,
   thin, wide, drain, splice, with their tests.
   - *Status:* done in `src/next/` (temporary private module beside the current code,
     removed in phase 3). 107 unit tests pass, Miri-clean under `-Zmiri-strict-provenance`.
     Doc examples are `ignore`d until the items become public. The wide (`Vec`-adopting)
     path lives in `hipvec`'s `hip/base.rs` and moves over with phase 2.
2. **Three reprs** — layouts + asserts first (1-/2-word tagging is the main risk),
   then the `Repr` trait.
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

- Alias naming: `HipStr` / `HipStr2` / `HipStr1`, or `HipStr` / `PairStr` / `ThinStr`, or other.
  Working names for reprs: `Fat` / `Pair` / `Thin`.
- Default backend for aliases (today `Arc`) and whether to keep `Local*` aliases.
- `Unique` backend semantics on clone (deep copy, as today?).
