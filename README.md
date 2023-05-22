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
* `unstable`: exposes internal trait that may change at any moment

## ☣️ Unsafety in Hipstr

This crate use `unsafe` extensively. 🤷

It exploits a 1-bit alignment niche in pointer existing on most platform (I think all Rustc supported platform) to distinguish the inline representation from the other representations.

To make things safer, Rust is tested (but for now mostly on x86_64) and tested under Miri (MIR interpreter).

## 🧪 Testing

### ☔ Coverage

This crate has near full line coverage:

```bash
cargo llvm-cov --all-features --html
# or
cargo tarpaulin --all-features --out html --engine llvm
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

## 📦 Similar crates

* `arcstr`, no inline repr, otherwise very similar except that their `Substr` are heavy and they uses a custom `Arc`.
* `flexstr`, no slice, very similar but use an `Arc<str>` instead of an `Arc<String>` remove one level of indirection
* `imstr`: no inline repr, otherwise very similar

## 🚀 TODOs

* More copy on write API (like `imstr`)?

## 📖 Author and licenses

For now, just me PoLazarus 👻 \
Help welcome! 🚨

MIT + APACHE
