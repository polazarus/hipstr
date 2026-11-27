use arcstr::ArcStr;
use divan::Bencher;
use ecow::EcoString;
use hipstr::HipStr;
use kstring::KString;

fn main() {
    divan::main();
}

const S: &[u8] = &[42; 42];
const S2: &str = unsafe { std::str::from_utf8_unchecked(S) };

#[divan::bench_group(sample_count = 10_000)]
mod from_slice {
    use super::*;

    #[divan::bench(args = [0, 1, 16, 23, 32, 42])]
    fn bench_hipstr_from_slice(n: usize) -> HipStr<'static> {
        HipStr::from(&S2[0..n])
    }

    #[divan::bench(args = [0, 1, 16, 23, 32, 42])]
    fn bench_arcstr_from_slice(n: usize) -> ArcStr {
        ArcStr::from(&S2[0..n])
    }

    #[divan::bench(args = [0, 1, 16, 23, 32, 42])]
    fn bench_ecow_from_slice(n: usize) -> EcoString {
        EcoString::from(&S2[0..n])
    }

    #[divan::bench(args = [0, 1, 16, 23, 32, 42])]
    fn bench_kstring_from_slice(n: usize) -> KString {
        KString::from_ref(&S2[0..n])
    }
}

#[divan::bench_group(sample_count = 10_000)]
mod from_string {
    use super::*;

    #[divan::bench(args = [0, 1, 16, 23, 32, 42])]
    fn bench_hipstr_from_string(b: Bencher, n: usize) {
        b.with_inputs(|| String::from(&S2[0..n]))
            .bench_local_values(|s| HipStr::from(s));
    }

    #[divan::bench(args = [0, 1, 16, 23, 32, 42])]
    fn bench_arcstr_from_string(b: Bencher, n: usize) {
        b.with_inputs(|| String::from(&S2[0..n]))
            .bench_local_values(|s| ArcStr::from(s));
    }

    #[divan::bench(args = [0, 1, 16, 23, 32, 42])]
    fn bench_ecow_from_string(b: Bencher, n: usize) {
        b.with_inputs(|| String::from(&S2[0..n]))
            .bench_local_values(|s| EcoString::from(s));
    }

    #[divan::bench(args = [0, 1, 16, 23, 32, 42])]
    fn bench_kstring_from_string(b: Bencher, n: usize) {
        b.with_inputs(|| String::from(&S2[0..n]))
            .bench_local_values(|s| KString::from_string(s));
    }
}

/// The three sizes against `String`, on the operations their layouts change:
/// construction, clone, read access and growth.
mod sizes {
    use std::ops::Deref;

    use divan::black_box;
    use hipstr::{SmallStr, TinyStr};

    use super::*;

    const LENS: &[usize] = &[0, 7, 15, 23, 42];

    /// What the benches need, implemented by all the compared types.
    trait Text: for<'s> From<&'s str> + Clone + Deref<Target = str> {
        fn push_str(&mut self, s: &str);
    }

    impl Text for String {
        fn push_str(&mut self, s: &str) {
            String::push_str(self, s);
        }
    }

    macro_rules! text {
        ($($t:ty),*) => {$(
            impl Text for $t {
                fn push_str(&mut self, s: &str) {
                    <$t>::push_str(self, s);
                }
            }
        )*};
    }

    text!(HipStr<'static>, SmallStr<'static>, TinyStr);

    #[divan::bench(types = [String, HipStr<'static>, SmallStr<'static>, TinyStr], args = LENS)]
    fn from_slice<T: Text>(n: usize) -> T {
        T::from(black_box(&S2[..n]))
    }

    #[divan::bench(types = [String, HipStr<'static>, SmallStr<'static>, TinyStr], args = LENS)]
    fn clone<T: Text>(b: Bencher, n: usize) {
        let s = T::from(&S2[..n]);
        b.bench_local(|| black_box(&s).clone());
    }

    #[divan::bench(types = [String, HipStr<'static>, SmallStr<'static>, TinyStr], args = LENS)]
    fn read<T: Text>(b: Bencher, n: usize) {
        let s = T::from(&S2[..n]);
        b.bench_local(|| black_box(&s).len() + black_box(&s).as_bytes().first().map_or(0, |&b| b as usize));
    }

    #[divan::bench(types = [String, HipStr<'static>, SmallStr<'static>, TinyStr], args = [1, 8, 64])]
    fn push_grow<T: Text>(n: usize) -> T {
        let mut s = T::from("");
        for _ in 0..n {
            s.push_str(black_box("abcd"));
        }
        s
    }

    #[divan::bench(types = [Vec<u8>, hipstr::HipByt<'static>, hipstr::SmallByt<'static>, hipstr::TinyByt], args = [16, 256])]
    fn retain_drain<T: From<Vec<u8>> + Extend<u8>>(b: Bencher, n: usize)
    where
        T: VecLike,
    {
        b.with_inputs(|| T::from((0..n).map(|i| i as u8).collect::<Vec<u8>>()))
            .bench_local_values(|mut v| {
                v.retain_odd();
                v.drain_half();
                v
            });
    }

    trait VecLike {
        fn retain_odd(&mut self);
        fn drain_half(&mut self);
    }

    macro_rules! vec_like {
        ($($t:ty),*) => {$(
            impl VecLike for $t {
                fn retain_odd(&mut self) {
                    self.retain(|b| b % 2 == 1);
                }
                fn drain_half(&mut self) {
                    let n = self.len() / 2;
                    self.drain(..n);
                }
            }
        )*};
    }

    vec_like!(Vec<u8>, hipstr::HipByt<'static>, hipstr::SmallByt<'static>, hipstr::TinyByt);
}
