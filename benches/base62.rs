use base62::{
    decode, decode_alternative, encode, encode_alternative, encode_alternative_buf,
    encode_alternative_bytes, encode_buf, encode_bytes,
};
use criterion::{black_box, criterion_group, criterion_main, BatchSize, Criterion};
use rand::distributions::Standard;
use rand::{thread_rng, Rng};

pub fn criterion_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("decode");

    // Fixed input benchmark
    group.bench_function("standard_fixed", |b| {
        b.iter(|| decode(black_box("7n42DGM5Tflk9n8mt7Fhc7")))
    });

    // Random input benchmark using iter_batched for setup
    group.bench_function("standard_random", |b| {
        b.iter_batched(
            || {
                // Setup (runs outside measured time)
                let random_num: u128 = thread_rng().sample(Standard);
                encode(random_num)
            },
            decode, // Measured function
            BatchSize::SmallInput,
        )
    });

    group.bench_function("alternative_fixed", |b| {
        b.iter(|| decode_alternative(black_box("7N42dgm5tFLK9N8MT7fHC7")))
    });

    group.bench_function("alternative_random", |b| {
        b.iter_batched(
            || {
                // Setup (runs outside measured time)
                let random_num: u128 = thread_rng().sample(Standard);
                encode_alternative(random_num)
            },
            decode_alternative,
            BatchSize::SmallInput,
        )
    });
    group.finish();

    let mut group = c.benchmark_group("encode");

    group.bench_function("standard_new_fixed", |b| {
        b.iter(|| encode(black_box(u128::MAX)))
    });

    group.bench_function("standard_new_random", |b| {
        b.iter_batched(
            || thread_rng().sample(Standard),
            |num: u128| encode(black_box(num)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("standard_bytes_fixed", |b| {
        let mut buf = [0; 22];
        b.iter(|| encode_bytes(black_box(u128::MAX), black_box(&mut buf)))
    });

    group.bench_function("standard_bytes_random", |b| {
        b.iter_batched(
            || thread_rng().sample(Standard),
            |num: u128| {
                let mut buf = [0; 22];
                encode_bytes(black_box(num), black_box(&mut buf))
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("standard_buf_fixed", |b| {
        b.iter(|| encode_buf(black_box(u128::MAX), black_box(&mut String::new())))
    });

    group.bench_function("standard_buf_random", |b| {
        b.iter_batched_ref(
            || {
                let num: u128 = thread_rng().sample(Standard);
                (num, String::with_capacity(22))
            },
            |(num, buf)| {
                buf.clear();
                encode_buf(black_box(*num), black_box(buf))
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("alternative_new_fixed", |b| {
        b.iter(|| encode_alternative(black_box(u128::MAX)))
    });

    group.bench_function("alternative_new_random", |b| {
        b.iter_batched(
            || thread_rng().sample(Standard),
            |num: u128| encode_alternative(black_box(num)),
            BatchSize::SmallInput,
        )
    });

    group.bench_function("alternative_bytes_fixed", |b| {
        let mut buf = [0; 22];
        b.iter(|| encode_alternative_bytes(black_box(u128::MAX), black_box(&mut buf)))
    });

    group.bench_function("alternative_bytes_random", |b| {
        b.iter_batched(
            || thread_rng().sample(Standard),
            |num: u128| {
                let mut buf = [0; 22];
                encode_alternative_bytes(black_box(num), black_box(&mut buf))
            },
            BatchSize::SmallInput,
        )
    });

    group.bench_function("alternative_buf_fixed", |b| {
        b.iter(|| encode_alternative_buf(black_box(u128::MAX), black_box(&mut String::new())))
    });

    group.bench_function("alternative_buf_random", |b| {
        b.iter_batched_ref(
            || {
                let num: u128 = thread_rng().sample(Standard);
                (num, String::with_capacity(22))
            },
            |(num, buf)| {
                buf.clear();
                encode_alternative_buf(black_box(*num), black_box(buf))
            },
            BatchSize::SmallInput,
        )
    });

    group.finish();
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
