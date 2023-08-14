// cSpell:ignore arcstr flexstr imstr

use std::fmt;
use std::hint::black_box;
use std::sync::Arc;

use arcstr::ArcStr;
use hipstr::{HipByt, HipStr};

const TEXT: &str = "The General Assembly, Proclaims this Universal Declaration of Human Rights as a common standard of achievement for all peoples and all nations, to the end that every individual and every organ of society, keeping this Declaration constantly in mind, shall strive by teaching and education to promote respect for these rights and freedoms and by progressive measures, national and international, to secure their universal and effective recognition and observance, both among the peoples of Member States themselves and among the peoples of territories under their jurisdiction.";

// pub fn criterion_benchmark(c: &mut Criterion) {
//     c.bench_function("from_static_short", |b| b.iter(|| drop(black_box(HipStr::from_static("hello")))));
//     c.bench_function("from_static_long", |b| b.iter(|| drop(black_box(HipStr::from_static(TEXT)))));
// }

#[inline(never)]
fn bench_string_from_slice(input: &str) {
    let s = black_box(String::from(input));
    assert_eq!(s.as_str(), input);
}

#[inline(never)]
fn bench_arc_string_from_slice(input: &str) {
    let s = black_box(Arc::new(String::from(input)));
    assert_eq!(s.as_str(), input);
}

#[inline(never)]
fn bench_arc_box_str_from_slice(input: &str) {
    let arc: Arc<str> = input.into();
    let s = black_box(arc);
    assert_eq!(&*s, input);
}

#[inline(never)]
fn bench_hipstr_from_slice(input: &str) {
    let s = black_box(HipStr::from(input));
    assert_eq!(s.as_str(), input);
}

#[inline(never)]
fn bench_hipbyt_from_slice(input: &str) {
    let s = black_box(HipByt::from(input.as_bytes()));
    assert_eq!(s.as_slice(), input.as_bytes());
}

#[inline(never)]
fn bench_fast_str_from_slice(input: &str) {
    let s = black_box(fast_str::FastStr::from_ref(input));
    assert_eq!(s.as_str(), input);
}

#[inline(never)]
fn bench_faststr_from_slice(input: &str) {
    let s = black_box(faststr::FastStr::from_string(input.to_string()));
    assert_eq!(s.as_str(), input);
}

#[inline(never)]
fn bench_arcstr_from_slice(input: &str) {
    let s = black_box(ArcStr::from(input));
    assert_eq!(s.as_str(), input);
}

#[inline(never)]
fn bench_flexstr_from_slice(input: &str) {
    let s = black_box(flexstr::SharedStr::from(input));
    assert_eq!(s.as_str(), input);
}

#[inline(never)]
fn bench_imstr_from_slice(input: &str) {
    let s = black_box(imstr::ImString::from(input));
    assert_eq!(s.as_str(), input);
}

#[inline(never)]
fn bench_hipstr_from_slice_via_to_string(input: &str) {
    let s = black_box(HipStr::from(input.to_owned()));
    assert_eq!(s.as_str(), input);
}

fn bench<I, O>(name: impl fmt::Display, input: I, f: impl Fn(I) -> O)
where
    I: Clone,
{
    let samples = 50_000;
    let samples: Vec<_> = (0..samples)
        .map(|_| {
            let batch = 1_000_u32;

            let inputs: Vec<I> = vec![input.clone(); batch as usize];
            let mut outputs = Vec::with_capacity(batch as usize);

            let start = std::time::Instant::now();
            for input in inputs {
                outputs.push(f(input));
            }
            let timing = start.elapsed();
            drop(outputs);

            (timing / batch).as_secs_f64()
        })
        .collect();
    let samples = &samples[10_000..];
    let (count, av, stddev) = average_stddev(samples.iter().copied());
    let (new_count, av_no_outliers) = average(
        samples
            .iter()
            .copied()
            .filter(|e| (e - av).abs() < 2. * stddev),
    );

    println!(
        "{name:<20} {:>10.2}ns ({} outliers)",
        av_no_outliers * 1e9,
        count - new_count
    );
}

fn main() {
    println!("64 bytes");
    bench("String", &TEXT[..64], bench_string_from_slice);
    bench("Arc<String>", &TEXT[..64], bench_arc_string_from_slice);
    bench("Arc<Box<str>>", &TEXT[..64], bench_arc_box_str_from_slice);
    bench("HipByt", &TEXT[..64], bench_hipbyt_from_slice);
    bench("HipStr", &TEXT[..64], bench_hipstr_from_slice);
    bench("fast_str", &TEXT[..64], bench_fast_str_from_slice);
    bench("faststr", &TEXT[..64], bench_faststr_from_slice);
    bench("flexstr::SharedStr", &TEXT[..64], bench_flexstr_from_slice);
    bench("ArcStr", &TEXT[..64], bench_arcstr_from_slice);
    bench("imstr::ImString", &TEXT[..64], bench_imstr_from_slice);
    bench(
        "HipStr via to_string",
        &TEXT[..64],
        bench_hipstr_from_slice_via_to_string,
    );
    println!("10bytes");
    bench("String", &TEXT[..10], bench_string_from_slice);
    bench("Arc<String>", &TEXT[..10], bench_arc_string_from_slice);
    bench("Arc<Box<str>>", &TEXT[..10], bench_arc_box_str_from_slice);
    bench("HipStr", &TEXT[..10], bench_hipstr_from_slice);
    bench("HipByt", &TEXT[..10], bench_hipbyt_from_slice);
    bench("fast_str", &TEXT[..10], bench_fast_str_from_slice);
    bench("faststr", &TEXT[..10], bench_faststr_from_slice);
    bench("flexstr::SharedStr", &TEXT[..10], bench_flexstr_from_slice);
    bench("ArcStr", &TEXT[..10], bench_arcstr_from_slice);
    bench("imstr::ImString", &TEXT[..10], bench_imstr_from_slice);
    bench(
        "HipStr via to_string",
        &TEXT[..10],
        bench_hipstr_from_slice_via_to_string,
    );
}

fn average(iter: impl Iterator<Item = f64>) -> (u64, f64) {
    let (sum, count) = iter.fold((0., 0), |(sum, count), e| (sum + e, count + 1));
    (count, sum / (count as f64))
}

fn average_stddev(iter: impl Iterator<Item = f64> + Clone) -> (u64, f64, f64) {
    let (count, mu) = average(iter.clone());
    let (_, var) = average(iter.map(|e| (e - mu).powi(2)));
    (count, mu, var.sqrt())
}
