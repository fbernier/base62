use criterion::{black_box, criterion_group, criterion_main, Criterion};

pub fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("encode", |b| {
        b.iter(|| base62::encode(black_box(u128::MAX)))
    });

    c.bench_function("decode", |b| {
        b.iter(|| base62::decode(black_box("7n42DGM5Tflk9n8mt7Fhc7")))
    });

    c.bench_function("encode_reversed", |b| {
        b.iter(|| base62::encode_config(black_box(u128::MAX), base62::REVERSED))
    });

    c.bench_function("decode_reversed", |b| {
        b.iter(|| base62::decode_config(black_box("7N42dgm5tFLK9N8MT7fHC7"), base62::REVERSED))
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
