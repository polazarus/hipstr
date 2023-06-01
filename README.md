# `HipStr`

Yet another string:

* no copy literal via `from_static` (a `const`ructor!)
* no alloc small string (23 bytes on 64-bit platform)
* no copy owned slice
* and bytes too!

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

## ☣️ Unsafety in Hipstr

This crate uses `unsafe` extensively. 🤷

It exploits a 1-bit alignment niche in pointer existing on most platform (I think all Rustc supported platform) to distinguish the inline representation from the other representations.

To make things safer, Rust is tested thoroughly on multiple platforms, normally and with Miri (MIR interpreter).

## 🧪 Testing

### :☔ Coverage

This crate has near full line coverage:

```bash
cargo llvm-cov --all-features --html
# or
cargo tarpaulin --all-features --out html --engine llvm
```

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
cargo +nightly miri test  --target mips64-unknown-linux-gnuabi64
# Little endian, 32-bit
cargo +nightly miri test  --target i686-unknown-linux-gnu
```

## 📦 Similar crates

* [`arcstr`](https://github.com/thomcc/arcstr), no inline repr, otherwise very similar except that their slice are heavy (with dedicated `Substr` type) and they uses a custom `Arc`.
* [`flexstr`](https://github.com/nu11ptr/flexstr), no slice, very similar but use an `Arc<str>` instead of an `Arc<String>` (remove level of indirection but use fat pointers).
* [`imstr`](https://github.com/xfbs/imstr): no inline repr, otherwise very similar
* many more

## 🚀 TODOs

* More copy on write API (like `imstr`)?

## 📖 Author and licenses

For now, just me PoLazarus 👻 \
Help welcome! 🚨

MIT + APACHE
