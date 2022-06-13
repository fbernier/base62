use base62::{decode, decode_alternative, encode, encode_alternative};
use criterion::{black_box, criterion_group, criterion_main, Criterion};

pub fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("encode", |b| b.iter(|| encode(black_box(u128::MAX))));

    c.bench_function("encode_alternative", |b| {
        b.iter(|| encode_alternative(black_box(u128::MAX)))
    });

    c.bench_function("decode", |b| {
        b.iter(|| decode(black_box("7n42DGM5Tflk9n8mt7Fhc7")))
    });

    c.bench_function("decode_alternative", |b| {
        b.iter(|| decode_alternative(black_box("7N42dgm5tFLK9N8MT7fHC7")))
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
