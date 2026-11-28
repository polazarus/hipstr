//! Read and construction costs per representation (`cargo bench --bench repr`).
//!
//! Reads go over many values (distinct allocations), so that the loop is not
//! hoisted and each read pays its own pointer chase.

use divan::{Bencher, black_box};
use hipstr::{HipStr, SmallStr, TinyStr};

fn main() {
    divan::main();
}

const N: usize = 1024;
const LONG: &str = "a string long enough for the heap of every representation, 64 B";

fn heap_strings() -> Vec<String> {
    (0..N).map(|i| format!("{LONG}{i}")).collect()
}

/// Touches the length and the last byte of each value (through the slice).
#[inline]
fn read_all<'a, S: AsRef<str> + 'a>(values: impl IntoIterator<Item = &'a S>) -> usize {
    values.into_iter().fold(0, |acc, s| {
        let b = s.as_ref().as_bytes();
        acc + b.len() + usize::from(b[b.len() - 1])
    })
}

mod read {
    use super::*;

    #[divan::bench]
    fn small_heap(bencher: Bencher) {
        let values: Vec<SmallStr> = heap_strings()
            .iter()
            .map(|s| SmallStr::from(s.as_str()))
            .collect();
        bencher.bench(|| read_all(black_box(&values)));
    }

    #[divan::bench]
    fn small_borrowed(bencher: Bencher) {
        let strings = heap_strings();
        let values: Vec<SmallStr> = strings
            .iter()
            .map(|s| SmallStr::borrowed(s.as_str()))
            .collect();
        bencher.bench(|| read_all(black_box(&values)));
    }

    #[divan::bench]
    fn small_inline(bencher: Bencher) {
        let values: Vec<SmallStr> = (0..N).map(|i| SmallStr::from(format!("s{i}"))).collect();
        bencher.bench(|| read_all(black_box(&values)));
    }

    #[divan::bench]
    fn tiny_heap(bencher: Bencher) {
        let values: Vec<TinyStr> = heap_strings()
            .iter()
            .map(|s| TinyStr::from(s.as_str()))
            .collect();
        bencher.bench(|| read_all(black_box(&values)));
    }

    #[divan::bench]
    fn tiny_inline(bencher: Bencher) {
        let values: Vec<TinyStr> = (0..N).map(|i| TinyStr::from(format!("s{i}"))).collect();
        bencher.bench(|| read_all(black_box(&values)));
    }

    /// Control: the 3-word representation is not changed.
    #[divan::bench]
    fn hip_heap(bencher: Bencher) {
        let values: Vec<HipStr> = heap_strings()
            .iter()
            .map(|s| HipStr::from(s.as_str()))
            .collect();
        bencher.bench(|| read_all(black_box(&values)));
    }
}

/// Mixed kinds in pseudo-random order, over more values than a branch
/// predictor can memorize (a short repeated pattern would be learned, which
/// favors branchy reads unrealistically).
mod read_mixed {
    use super::*;

    const M: usize = 16 * 1024;

    fn kinds() -> Vec<u64> {
        let mut x = 0x2545_F491_4F6C_DD1D_u64;
        (0..M)
            .map(|_| {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                x % 3
            })
            .collect()
    }

    fn long(i: usize) -> String {
        format!("{LONG}{i}")
    }

    #[divan::bench]
    fn small_inline_heap_borrowed(bencher: Bencher) {
        let strings: Vec<String> = (0..M).map(long).collect();
        let values: Vec<SmallStr> = kinds()
            .iter()
            .enumerate()
            .map(|(i, k)| match k {
                0 => SmallStr::from(format!("s{i}")),
                1 => SmallStr::from(strings[i].as_str()),
                _ => SmallStr::borrowed(strings[i].as_str()),
            })
            .collect();
        bencher.bench(|| read_all(black_box(&values)));
    }

    #[divan::bench]
    fn tiny_inline_heap(bencher: Bencher) {
        let values: Vec<TinyStr> = kinds()
            .iter()
            .enumerate()
            .map(|(i, k)| {
                if *k == 0 {
                    TinyStr::from(format!("s{i}"))
                } else {
                    TinyStr::from(long(i))
                }
            })
            .collect();
        bencher.bench(|| read_all(black_box(&values)));
    }
}

mod from_string {
    use super::*;

    #[divan::bench]
    fn small(bencher: Bencher) {
        bencher
            .with_inputs(|| String::from(LONG))
            .bench_values(SmallStr::from);
    }

    #[divan::bench]
    fn tiny(bencher: Bencher) {
        bencher
            .with_inputs(|| String::from(LONG))
            .bench_values(TinyStr::from);
    }

    /// Control: adopts the buffer on both branches.
    #[divan::bench]
    fn hip(bencher: Bencher) {
        bencher
            .with_inputs(|| String::from(LONG))
            .bench_values(HipStr::from);
    }
}
