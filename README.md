# `hipstr`

[![Rust](https://github.com/polazarus/hipstr/actions/workflows/basic.yml/badge.svg)](https://github.com/polazarus/hipstr/actions/workflows/basic.yml)
[![Clippy & Miri](https://github.com/polazarus/hipstr/actions/workflows/analysis.yml/badge.svg)](https://github.com/polazarus/hipstr/actions/workflows/analysis.yml)
[![codecov](https://codecov.io/gh/polazarus/hipstr/branch/main/graph/badge.svg?token=Z7YUHB4YUD)](https://codecov.io/gh/polazarus/hipstr)
[![Docs](https://img.shields.io/docsrs/hipstr)](https://docs.rs/hipstr)
![MIT OR Apache-2.0](https://img.shields.io/crates/l/hipstr)

Yet another string type for Rust 🦀

- no copy **borrow** via `borrowed` (a `const` constructor) or `from_static`
- no alloc **small strings** (_23 bytes_ on 64-bit platform)
- no copy **owned slices**
- a niche: `Option<HipStr>` and `HipStr` have the same size
- **zero dependency** and compatible `no_std` with `alloc`

Also byte strings, OS strings, and paths!

## ⚡ Examples

```rust
use hipstr::HipStr;

let simple_greetings = HipStr::from_static("Hello world");
let _clone = simple_greetings.clone(); // no copy

let user = "John";
let greetings = HipStr::from(format!("Hello {}", user));
let user = greetings.slice(6..): // no copy
drop(greetings); // the slice is owned, it exists even if greetings disappear

let chars = user.chars().count(); // "inherits" `&str` methods
```

## ✏️ Features

- `std` (default): uses `std` rather than `core` and `alloc`, and also provides more trait implementations (for comparison and conversions)
- `serde`: provides serialization/deserialization support with [`serde`](https://serde.rs)
- `borsh`: provides serialization/deserialization support with [`borsh`](https://borsh.io)
- `bstr`: provides compatibility with [BurntSushi's `bstr` crate](https://github.com/BurntSushi/bstr) - `unstable`: do nothing, used to reveal unstable implementation details

## ☣️ Safety of `hipstr`

This crate makes extensive use of `unsafe` code blocks. 🤷

It leverages the 2-bit alignment niche present in pointers across most platforms (all platforms currently supported by the Rust compiler?) to discriminate between the three possible representations.

To make things safer, Rust is tested thoroughly on multiple platforms, normally and with [Miri] (the MIR interpreter).

## 🧪 Testing and Verification Strategy

To ensure safety and reliability, this crate undergoes thorough testing:

- Near 100% test coverage
- Cross-platform validation:
  - 32-bit and 64-bit architectures
  - little and big endian

In addition, this crate is checked with advanced dynamic verification methods:

- Concurrency testing using the [Tokio's loom crate][loom]
- Undefined behavior detection using [Miri] (the MIR interpreter)

### ☔ Coverage

This crate has **near full line coverage**:

```bash
cargo llvm-cov --all-features --html
# or
cargo tarpaulin --all-features --out html --engine llvm
```

Check out the current coverage on [Codecov]:

![Coverage grid](https://codecov.io/gh/polazarus/hipstr/branch/main/graphs/tree.svg?token=Z7YUHB4YUD)

### 🖥️ Cross-platform testing

In the Github-provided CI, `hipstr` is tested under:

- Linux
- Windows
- MacOS (ARM 64-bit LE)

You can easily run the test on various platforms with [`cross`]:

```bash
cross test --target s390x-unknown-linux-gnu         # 32-bit BE
cross test --target powerpc64-unknown-linux-gnu     # 64-bit BE
cross test --target i686-unknown-linux-gnu          # 32-bit LE
cross test --target x86_64-unknown-linux-gnu        # 64-bit LE
```

NB: previously I used MIPS targets for big endian, but due to some LLVM-related issue they are not working anymore… see [Rust issue #113065](https://github.com/rust-lang/rust/issues/113065)

### 🧵 [Loom]

This crates uses the `loom` crate to check the custom "Arc" implementation. To run the tests:

```bash
RUSTFLAGS='--cfg loom' cargo test --release loom
```

### 🔍 [Miri]

This crate runs successfully with Miri:

```bash
MIRIFLAGS=-Zmiri-symbolic-alignment-check cargo +nightly miri test

for SEED in $(seq 0 10); do
  echo "Trying seed: $SEED"
  MIRIFLAGS="-Zmiri-seed=$SEED" cargo +nightly miri test || { echo "Failing seed: $SEED"; break; };
done
```

To check with different word size and endianness:

```bash
# Big endian, 64-bit
cargo +nightly miri test --target mips64-unknown-linux-gnuabi64
# Little endian, 32-bit
cargo +nightly miri test --target i686-unknown-linux-gnu
```

Note: this crate leverages the "exposed provenance" semantics.

## 📦 Similar crates

`#[non_exhaustive]`

| Name                                                           | TS cheap-clone | Local cheap-clone | Inline | Cheap slice | Bytes | Borrow `'static` | Borrow any `'a` | Comment                                                                                            |
| -------------------------------------------------------------- | -------------- | ----------------- | ------ | ----------- | ----- | ---------------- | :-------------- | -------------------------------------------------------------------------------------------------- |
| `hipstr`                                                       | ✓              | ✓                 | ✓      | ✓           | ✓     | ✓                | ✓               | obviously!                                                                                         |
| [`arcstr`](https://github.com/thomcc/arcstr)                   | ✓\*            | -                 | -      | -\*\*       | -     | ✓                | -               | \*use a custom thin `Arc`, \*\*heavy slice (with dedicated substring type)                         |
| [`flexstr`](https://github.com/nu11ptr/flexstr)                | ✓\*            | ✓                 | ✓      | -           | -     | ✓                | -               | \*use `(A)rc<str>` instead of `(A)rc<String>` (remove a level of indirection but use fat pointers) |
| [`imstr`](https://github.com/xfbs/imstr)                       | ✓              | ✓                 | -      | ✓           | -     | -                | -               |                                                                                                    |
| [`faststr`](https://github.com/volo-rs/faststr)                | ✓              | -                 | ✓      | ✓           | -     | ✓                | -               | zero-doc with complex API                                                                          |
| [`fast-str`](https://github.com/xxXyh1908/rust-fast-str)       | ✓              | -                 | ✓      | ✓           | -     | ✓                | -               | inline repr is opt-in                                                                              |
| [`ecow`](https://github.com/typst/ecow)                        | ✓\*            | -                 | ✓      | -           | ✓\*\* | ✓                | -               | \*on two words only 🤤, \*\*even any `T`                                                           |
| [`cowstr`](https://git.pipapo.org/cehteh/cowstr.git)           | ✓              | -                 | -      | -\*         | -     | ✓                | -\*\*           | \*heavy slice, \*\*contrary to its name                                                            |
| [`compact_str`](https://github.com/parkmycar/compact_str)      | -              | -                 | ✓      | -           | ✓\*   | -                | -               | \*opt-in via `smallvec`                                                                            |
| [`inline_string`](https://github.com/fitzgen/inlinable_string) | -              | -                 | ✓      | -           | -     | -                | -               |                                                                                                    |
| [`kstring`](https://docs.rs/kstring/latest/kstring/)           | ✓              | ✓                 | ✓      | -           | -     | ✓                | ✓\*             | safe mode, use boxed strings; \* with second type                                                  |
| [`smartstring`](https://github.com/bodil/smartstring)          | -              | -                 | ✓      | -           | -     | -                | -               |                                                                                                    |
| [`smallstr`](https://github.com/murarth/smallstr)              | -              | -                 | ✓      | -           | -     | -                | -               |                                                                                                    |
| [`smol_str`](https://github.com/rust-analyzer/smol_str)        | -              | -                 | ✓\*    | -           | -     | ✓                | -               | \*but only inline string, here for reference                                                       |

skipping specialized string types like
[`tinystr`](https://github.com/unicode-org/icu4x) (ASCII-only, bounded), or
`bstr`, or `bytestring`, or...

In short, `HipStr`, one string type to rule them all 😉

[![How standards proliferate](https://imgs.xkcd.com/comics/standards.png)](https://xkcd.com/927/)

## 🏎️ Performances

While speed is not the main motivator for `hipstr`, it seems to be doing OK on that front.

See some actual benchmarks on [Rust's String Rosetta].

## 📖 Author and licenses

For now, just me PoLazarus 👻 \
Help welcome! 🚨

MIT + Apache

[codecov]: https://app.codecov.io/gh/polazarus/hipstr
[miri]: https://github.com/rust-lang/miri
[`cross`]: https://github.com/cross-rs/cross
[loom]: https://github.com/tokio-rs/loom
[Rust's String Rosetta]: https://github.com/rosetta-rs/string-rosetta-rs
