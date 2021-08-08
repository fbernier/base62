use criterion::{black_box, criterion_group, criterion_main, Criterion};

pub fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("encode", |b| {
        b.iter(|| base62::encode(black_box(u128::MAX)))
    });

    c.bench_function("decode", |b| {
        b.iter(|| base62::decode(black_box("7n42DGM5Tflk9n8mt7Fhc7")))
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
