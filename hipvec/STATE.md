# `hipvec` — state of the branch

_Snapshot: `hipvec` @ `150e9ac` ("chore: unify hip vector", 2026-06-17) vs. `main` @ `1308a5d`
(2025-04-29). Verified against stable `rustc 1.96.0`._

## TL;DR

`hipvec` is **20 commits ahead of `main`** and adds a new workspace crate (`hipvec/`, ~11.4k LOC)
that generalises hipstr's representation strategy from strings to **vectors**. `main` itself is
untouched (only a cosmetic import re-ordering in `src/macros.rs` and a `.vscode` tweak).

The crate is mid-rewrite:

- `inline` and `thin` vectors are in good shape (201 lib tests pass, `no_std` builds);
- the headline `HipVec`/`HipSlice` type is still **scaffolding** — no `Clone`, no COW sharing, a
  `todo!()` on the wide (`Vec`) drop path, and almost none of the `Vec` API;
- the new crate is not covered by CI, Miri, loom, coverage, or docs.

---

## 1. Branch mechanics

| | `main` | `hipvec` |
|---|---|---|
| Tip | `1308a5d` "chore: refine coverage" (2025-04-29) | `150e9ac` "chore: unify hip vector" (2026-06-17) |
| Crate version | `hipstr 0.9.0` | same, plus new `hipvec 0.1.0` |
| Edition / MSRV | 2021 / 1.85 | 2021 / 1.85 (root), **2024 / 1.95** (hipvec) |
| Dependencies | zero (optional serde/borsh/bstr) | `const-default` |
| Tests | 417 lib tests | 201 lib tests + 7 failing doctests |

- `git log main..hipvec` = 20 commits; `git log hipvec..main` = 0 → the branch sits cleanly on top
  of `main`.
- Substantive diff: `[workspace] members = ["./hipvec"]` + workspace-wide pedantic clippy in the
  root `Cargo.toml`, and the whole `hipvec/` tree. No change to hipstr behaviour.
- The working tree is **dirty**: an in-flight rename `HipVec` → `HipSlice` in
  `hipvec/src/hip/{generic,copy,noncopy}`, removal of `OwnerMut`, doc/clippy tweaks. Not committed.
- This is the **successor to the `wip3` branch's `src/vecs` module** (which lived inside hipstr and
  used `rules_derive`/`typenum`). The untracked `ref/` and `wip3/` directories at the repo root are
  byte-identical 1.1 MB snapshots of that old tree, kept as reference material.

## 2. Goals (as evidenced by code and history)

1. **A sibling crate of vector types**, not part of `hipstr`: `InlineVec`, `ThinVec`, `HipVec`.
2. **Reuse the hipstr trick**: one 3-word "pivot" that is either borrowed, inline, or an owned heap
   handle tagged in the low bits (`common/tagged_pointer.rs`, `hip/base.rs`: `SLICE_TAG = 0b10`,
   inline tag `0b1`).
3. **Thin heap vectors**: pointer-sized handle (`thin/base/mod.rs`) pointing at
   `Header { prefix, ptr, cap, len }` (`common/header.rs`), where `prefix` is the refcount /
   arbitrary front matter and thin/wide share the same header layout.
4. **Generic backends**: `Arc`/`Rc`/`Unique` as `BackendImpl<C, PANIC_ON_OVERFLOW>`
   (`backend/mod.rs`, `rc.rs`, `arc.rs`, `unique.rs`), plus test counters (`BoundedRc`,
   `PanickyUnique`).
5. **`Copy`/non-`Copy` specialisation unified behind a `Copyness` marker**
   (`common/markers.rs`) instead of duplicated modules — done for thin and hip, **not yet for
   inline**.
6. **`std`-compatible API surface**, tracked in `features.csv` (47 rows × 4 type variants).
7. **`no_std + alloc`** (currently `default = ["alloc", "std"]`, where `std` does essentially
   nothing), and **`const fn` wherever possible**.
8. Longer term, the analogue of `HipStr`: cheap `Clone`/slicing/COW over borrowed/inline/thin/wide.

## 3. What actually works

- **`inline`** — two full implementations (`inline/copy`, `inline/noncopy`, ~2.3k LOC + tests),
  3-word `BasicLayout` with the length bit-packed in a `NonZeroUsize`, per-element-type capacity
  computation, ZST handling, `drain`, `splice`, `pop_if`, `push_within_capacity`, `const` append.
- **`thin`** — unified `GenericThinVec<T, Copyness>`, 61 tests, `Drain`/`Splice` iterators,
  fallible reserve, `try_with_capacity`, OOM handling, shrink/rounding heuristics.
- **`common`** — shared `Vector`/`MutableVector`/`GrowableVector` traits (implemented for
  inline/thin and `Vec`), `Drain`, `Splice`, range simplification, `Header`, tagged pointers,
  `ZeroUsize`.
- **Backends** — `Count` (`Cell`), `AtomicCount` (loom-aware `arc.rs`), `One` (unique), all
  `Counter` impls with release/acquire semantics.
- **Builds** on stable 1.96, on `--no-default-features`, and on `--features alloc`;
  `cargo fmt --all --check` passes; `cargo doc -D warnings` passes; **201/201 lib tests pass**.

Coverage of `features.csv`: **32/47 inline-copy, 32/47 inline-noncopy, 31/47 thin-copy,
31/47 thin-noncopy**. The ledger also omits `remove`, `swap_remove` and `capacity`, which *are*
implemented. `hip` is not in the matrix at all.

Per-module lib test counts: `inline` 121, `thin` 61, `common` 17, `hip` **2**.

## 4. What is missing

### 4.1 The `hip` layer is a skeleton (biggest gap)

`hipvec/src/hip/generic.rs` exposes only: `new`, `borrowed`, `with_capacity`, `as_ptr`, `len`,
`as_slice`, `is_empty`, `as_mut_slice`, `repr`, `mutate()`, `to_mut_slice`,
`From<ThinVec>`, `From<Vec<T>>`, and `RefMut::{as_mut_slice, push}`. Concretely missing:

- **`Clone` (and `Copy`) — the whole point of a hip vector.** There is no `Clone` impl at all, and
  `Counter::incr` is **never called outside tests**, so refcounted COW sharing cannot happen yet.
  `Backend::PANIC_ON_OVERFLOW` is also unused so far.
- **Wide (`Vec`-backed) representation is unimplemented.** `OwnedRepr::Wide` exists, but
  `Owner::drop` / `drop_container` call `todo!()` (`hip/base.rs:98`, `hip/base.rs:119`). Verified:
  `HipVec::from(vec![1, 2, 3])` **panics on drop** ("not yet implemented"). `Mut::try_reserve`'s
  wide→thin migration copies elements and then overwrites the old owner without dropping the boxed
  header/refcount (latent leak, currently unreachable because there is no `Clone`).
- **Mutation API**: only `push` (via `RefMut`). No `insert`, `pop`, `remove`, `truncate`, `clear`,
  `extend`, `append`, `reserve`, `drain`, `splice`, `split_off`, `resize`, …
- **Trait impls**: no `Deref`/`DerefMut`, `AsRef`, `Debug`, `PartialEq`/`Eq`/`Hash`/`Ord`,
  `IntoIterator`, `FromIterator`, `From<[T; N]>`, `From<&[T]>`, `From<InlineVec>`; no
  `unsafe impl Send/Sync` (the raw `NonNull` in `Pivot` makes the type `!Send`/`!Sync`
  automatically). Compare with the shipped `HipStr`/`HipByt`.
- **Ergonomics**: no default-backend aliases (`HipVec<'a, T>` = `Arc` backend) at crate root;
  users must spell `hip::noncopy::HipVec<'a, T, Rc>`.
- **Tests**: `hip` has **2 tests**, both named `miri_test`, and one has its main body commented
  out (`hip/copy/tests.rs`, `hip/noncopy/tests.rs`).
- Dead scaffolding: `Either` (`hip/base.rs:165`), `OwnerMut` (just deleted), and the whole
  `Sliced::from_wide`/`Owner` wide half.

### 4.2 Missing `Vec` surface (per `features.csv`)

Not implemented on **any** type: `cmp`, `cmp_array`, `cmp_slice`, `dedup`, `dedup_by`,
`dedup_by_key`, `extend_from_within`, `extract_if`, `from_array_ref`, `into_chunks`,
`into_flattened`, `retain`, `retain_mut`, `shrink_to`, `shrink_to_fit`. `const_append` exists only
for inline.

No `PartialEq`/`Hash`/`AsRef`/`IntoIterator`/`FromIterator` impls anywhere; only `Deref`, `Debug`,
`Extend`, `Clone`, `From`.

### 4.3 Leftovers of the old design (won't compile if re-enabled)

- `hipvec/src/smart/` (untracked) is the old `Smart<T, C>` pointer; it references
  `PanicOnOverflow`, `CloneOnOverflow`, `BackendImpl<C, bool>` aliases that no longer exist, and
  its doctests point at `hipstr::`.
- `hipvec/src/backend/atomic.rs` (untracked) is a stale duplicate of `backend/arc.rs` with the
  same dead identifiers.
- `hipvec/src/backend/tests.rs` contains **zero `#[test]`** functions and a dangling
  `PanickyUnique = BackendImpl<Unique, true>` alias (tolerated only because type aliases do not
  check bounds). No concurrency tests for `Arc`.
- `⚠ 8 dead-code / unused clippy warnings` totalling methods such as `inline_mut`,
  `drop_container`, `truncate_copy`, `clear_copy`, `as_mut_slice`.

### 4.4 Testing / CI / release gaps vs. `main`

- **Doctests fail: 7** (`cargo test -p hipvec --doc`):
  - `common/splice/mod.rs` — needs `PartialEq` on `ThinVec`;
  - 6 × `try_reserve`/`try_reserve_exact` doctests use `hipvec::common::TryReserveError` and
    `::CapacityOverflow`; the type actually lives in `hipvec::thin` (kindful) and
    `hipvec::inline` (unit struct). The two `TryReserveError` types are inconsistent.
- **CI does not test the new crate.** `basic.yml` runs `cargo hack check/build/test`, `cargo test`,
  Miri (`--all-features`), coverage, `cargo nono` and minimal-versions — all at the root package,
  not `--workspace`. Only `cargo fmt --all --check` reaches `hipvec`. No loom wiring in
  `hipvec/Cargo.toml` (no `loom` dependency even though `arc.rs` has `#[cfg(loom)]` branches).
- **MSRV mismatch**: `hipvec` claims 1.95 / edition 2024 while CI installs the root's 1.85
  toolchain. Any workspace-wide CI step will either skip it or fail.
- **Docs**: `hipvec/src/lib.rs` has no crate-level docs, no `README.md`, no CHANGELOG entry, no
  `release.toml`/publish wiring, no docs.rs metadata; `TODO.md` covers only inline/thin.
- **Feature parity**: no `serde`, `borsh`, `std`-only trait impls, no benches (`divan` in main),
  no fuzz targets, no coverage measurement.

### 4.5 Refactor still in flight

Thin (`d1dc949`) and hip (`150e9ac`) were unified via `Copyness`, but **`inline` is still
duplicated** (`inline/copy` 1162 LOC vs `inline/noncopy` 1149 LOC + ~1.4k LOC of duplicated tests).
The uncommitted `HipVec → HipSlice` rename suggests the intended split is an owned/growable
`HipVec` vs. a borrowed/sliced view `HipSlice` (mirroring hipstr's `HipStr`/slices), but so far
only the generic type is renamed and the aliases still say `HipVec`.

### 4.6 Repo hygiene

Untracked and un-ignored at the repo root: `ref/` and `wip3/` (identical 1.1 MB copies of the old
`wip3` source tree) and an unrelated npm `package-lock.json`. The dirty rename should be committed
or reverted.

## 5. Suggested order of attack

1. Commit/revert the `HipSlice` rename; delete or `.gitignore` `ref/`, `wip3/`,
   `package-lock.json`.
2. Finish `hip`: wide drop (`todo!`), `Clone` via `Counter::incr` / `Backend::PANIC_ON_OVERFLOW`,
   `unsafe impl Send/Sync`, then the basic `Vec` API plus `Deref`/`PartialEq`/`Debug`/
   `IntoIterator`.
3. Fix the 7 doctests (single shared `TryReserveError`, or corrected paths) and the 8 dead-code
   warnings; remove `smart/` + `backend/atomic.rs` or port them onto the new `Backend` API.
4. Wire CI: `--workspace`, a separate MSRV (1.95) job, and miri/loom/coverage/doc jobs for
   `hipvec`.
5. Fill the `features.csv` gaps (`retain`, `dedup`, `extract_if`, `shrink_to`, comparison/hash
   traits), then rewrite the ledger to include `hip` + `remove`/`swap_remove`/`capacity`.
6. Unify `inline/copy` + `inline/noncopy` with the `Copyness` marker as done for thin/hip; add
   crate docs/README before publishing `0.1.0`.
