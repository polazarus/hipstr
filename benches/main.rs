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
