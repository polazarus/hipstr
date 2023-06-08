# `hipstr`

[![Rust](https://github.com/polazarus/hipstr/actions/workflows/basic.yml/badge.svg)](https://github.com/polazarus/hipstr/actions/workflows/basic.yml)
[![Clippy](https://github.com/polazarus/hipstr/actions/workflows/clippy.yml/badge.svg)](https://github.com/polazarus/hipstr/actions/workflows/clippy.yml)
[![Miri](https://github.com/polazarus/hipstr/actions/workflows/miri.yml/badge.svg)](https://github.com/polazarus/hipstr/actions/workflows/miri.yml)
[![codecov](https://codecov.io/gh/polazarus/hipstr/branch/main/graph/badge.svg?token=Z7YUHB4YUD)](https://codecov.io/gh/polazarus/hipstr)
[![Docs](https://img.shields.io/docsrs/hipstr)](https://docs.rs/hipstr)
![MIT OR Apache-2.0](https://img.shields.io/crates/l/hipstr)

Yet another string for Rust 🦀

* no copy **literal wrapping** via `from_static` (a `const`ructor!)
* no alloc **small strings** (23 bytes on 64-bit platform)
* no copy **owned slices**
* **zero dependency**

And **bytes** too!

## ⚡ Examples

```rust
use hipstr::HipStr;

let simple_greetings = HipStr::from_static("Hello world");
let _clone = simple_greetings.clone(); // no copy

let user = "John";
let greetings = HipStr::from(format!("Hello {}", user));
let _user = greetings.slice(6..): // no copy
```

## ✏️ Features

* `serde`: serialization/deserialization support with `serde` crate
* `unstable`: exposes internal `Backend` trait that may change at any moment

## ☣️ Safety of `hipstr`

This crate uses `unsafe` extensively. 🤷

It exploits a 1-bit alignment niche in pointers existing on most platform
(I think all Rustc supported platform) to distinguish the inline representation
from the other representations.

To make things safer, Rust is tested thoroughly on multiple platforms, normally
and with Miri (MIR interpreter).

## 🧪 Testing

### ☔ Coverage

This crate has near full line coverage:

```bash
cargo llvm-cov --all-features --html
# or
cargo tarpaulin --all-features --out html --engine llvm
```

Check out the current coverage on [Codecov](https://app.codecov.io/gh/polazarus/hipstr):

![Coverage grid](https://codecov.io/gh/polazarus/hipstr/branch/main/graphs/tree.svg?token=Z7YUHB4YUD)

### 🖥️ Cross-platform testing

With [`cross`](https://github.com/cross-rs/cross):

```bash
cross test --target mips-unknown-linux-gnu          # 32-bit BE
cross test --target mips64-unknown-linux-gnuabi64   # 64-bit BE
cross test --target i686-unknown-linux-gnu          # 32-bit LE
cross test --target x86_64-unknown-linux-gnu        # 64-bit LE
```

### 🔍 Miri

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

## 📦 Similar crates

* [`arcstr`](https://github.com/thomcc/arcstr): no inline repr, heavy slice (with dedicated `Substr` type) and custom `Arc`.
* [`flexstr`](https://github.com/nu11ptr/flexstr): no slice, very similar but use an `Arc<str>` instead of an `Arc<String>` (remove one level of indirection but use fat pointers).
* [`imstr`](https://github.com/xfbs/imstr): no inline repr, otherwise very similar.
* and many more.

In short, `HipStr`, one string type to rule them all…

[![How standards proliferate](https://imgs.xkcd.com/comics/standards.png)](https://xkcd.com/927/)

## 🚀 TODOs

* More copy on write API (like `imstr`)?

## 📖 Author and licenses

For now, just me PoLazarus 👻 \
Help welcome! 🚨

MIT + Apache
