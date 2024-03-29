// cSpell:ignore arcstr flexstr imstr

use std::hint::black_box;
use std::sync::Arc;

const TEXT: &str = "The General Assembly, Proclaims this Universal Declaration of Human Rights as a common standard of achievement for all peoples and all nations, to the end that every individual and every organ of society, keeping this Declaration constantly in mind, shall strive by teaching and education to promote respect for these rights and freedoms and by progressive measures, national and international, to secure their universal and effective recognition and observance, both among the peoples of Member States themselves and among the peoples of territories under their jurisdiction.";

// pub fn criterion_benchmark(c: &mut Criterion) {
//     c.bench_function("from_static_short", |b| b.iter(|| drop(black_box(HipStr::from_static("hello")))));
//     c.bench_function("from_static_long", |b| b.iter(|| drop(black_box(HipStr::from_static(TEXT)))));
// }

#[inline(never)]
fn bench_string_from_slice(input: &str) {
    let _ = black_box(String::from(input));
}

#[inline(never)]
fn bench_arc_string_from_slice(input: &str) {
    let _ = black_box(Arc::new(String::from(input)));
}

#[inline(never)]
fn bench_arc_box_str_from_slice(input: &str) {
    let arc: Arc<str> = input.into();
    let _ = black_box(arc);
}

#[inline(never)]
fn bench_hipstr_from_slice(input: &str) {
    let _ = black_box(hipstr::HipStr::from(input));
}

#[inline(never)]
fn bench_hipbyt_from_slice(input: &str) {
    let _ = black_box(hipstr::HipByt::from(input.as_bytes()));
}

#[inline(never)]
fn bench_fast_str_from_slice(input: &str) {
    let _ = black_box(fast_str::FastStr::from_ref(input));
}

#[inline(never)]
fn bench_faststr_from_slice(input: &str) {
    let _ = black_box(faststr::FastStr::from_string(input.to_string()));
}

#[inline(never)]
fn bench_arcstr_from_slice(input: &str) {
    let _ = black_box(arcstr::ArcStr::from(input));
}

#[inline(never)]
fn bench_flexstr_from_slice(input: &str) {
    let _ = black_box(flexstr::SharedStr::from(input));
}

#[inline(never)]
fn bench_imstr_from_slice(input: &str) {
    let _ = black_box(imstr::ImString::from(input));
}

fn bench<I, O>(input: I, f: impl Fn(I) -> O) -> f64
where
    I: Clone,
{
    let samples = 10_000;
    let samples: Vec<_> = (0..samples)
        .map(|_| {
            let batch = 10_000_u32;

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
    let samples = &samples[1_000..];
    let (_count, av, stddev) = average_stddev(samples.iter().copied());
    let (_new_count, av_no_outliers) = average(
        samples
            .iter()
            .copied()
            .filter(|e| (e - av).abs() < 2. * stddev),
    );

    av_no_outliers * 1e9
}

fn main() {
    let ns = [0, 1, 2, 4, 8, 12, 15, 16, 17, 20, 23, 24, 32, 48, 64, 128];
    let benches: &[(&str, fn(&str))] = &[
        ("std(String)", bench_string_from_slice),
        ("std(Arc<String>)", bench_arc_string_from_slice),
        ("std(Arc<Box<str>>)", bench_arc_box_str_from_slice),
        ("hipstr::HipStr", bench_hipstr_from_slice),
        ("fast_str", bench_fast_str_from_slice),
        ("faststr", bench_faststr_from_slice),
        ("flexstr::SharedStr", bench_flexstr_from_slice),
        ("ArcStr", bench_arcstr_from_slice),
        ("imstr::ImString", bench_imstr_from_slice),
        ("hipstr::HipByt", bench_hipbyt_from_slice),
    ];
    print!("");
    for &(name, _) in benches {
        print!(",{name}");
    }
    println!();
    for &n in &ns {
        print!("{n}");
        for &(name, f) in benches {
            eprintln!("{name} {n}");
            let input = &TEXT[..n];
            let avg = bench(input, f);
            print!(",{avg}");
        }
        println!();
    }
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
