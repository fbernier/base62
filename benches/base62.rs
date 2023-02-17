use base62::{
    decode, decode_alternative, /*digit_count,*/ encode, encode_alternative,
    encode_alternative_buf, encode_alternative_bytes, encode_buf, encode_bytes,
};
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use rand::distributions::Standard;
use rand::{thread_rng, Rng};

pub fn criterion_benchmark(c: &mut Criterion) {
    let mut random_u128s = thread_rng().sample_iter::<u128, Standard>(Standard);

    c.bench_function("decode_standard", |b| {
        b.iter(|| decode(black_box("7n42DGM5Tflk9n8mt7Fhc7")))
    });

    c.bench_function("decode_standard_random", |b| {
        b.iter(|| decode(black_box(encode(random_u128s.next().unwrap()))))
    });

    c.bench_function("decode_alternative", |b| {
        b.iter(|| decode_alternative(black_box("7N42dgm5tFLK9N8MT7fHC7")))
    });

    c.bench_function("decode_alternative_random", |b| {
        b.iter(|| decode_alternative(black_box(encode_alternative(random_u128s.next().unwrap()))))
    });

    /*
    c.bench_function("digit_count", |b| {
        b.iter(|| digit_count(black_box(random_u128s.next().unwrap())))
    });
    */

    c.bench_function("encode_standard_new", |b| {
        b.iter(|| encode(black_box(u128::MAX)))
    });

    c.bench_function("encode_standard_new_random", |b| {
        b.iter(|| encode(black_box(random_u128s.next().unwrap())))
    });

    c.bench_function("encode_standard_bytes", |b| {
        let mut buf = [0; 22];
        b.iter(|| encode_bytes(black_box(u128::MAX), black_box(&mut buf)))
    });

    c.bench_function("encode_standard_bytes_random", |b| {
        let mut buf = [0; 22];
        b.iter(|| encode_bytes(black_box(random_u128s.next().unwrap()), black_box(&mut buf)))
    });

    c.bench_function("encode_standard_buf", |b| {
        b.iter(|| encode_buf(black_box(u128::MAX), black_box(&mut String::new())))
    });

    c.bench_function("encode_standard_buf_random", |b| {
        b.iter(|| {
            encode_buf(
                black_box(random_u128s.next().unwrap()),
                black_box(&mut String::new()),
            )
        })
    });

    c.bench_function("encode_alternative_new", |b| {
        b.iter(|| encode_alternative(black_box(u128::MAX)))
    });

    c.bench_function("encode_alternative_new_random", |b| {
        b.iter(|| encode_alternative(black_box(random_u128s.next().unwrap())))
    });

    c.bench_function("encode_alternative_bytes", |b| {
        let mut buf = [0; 22];
        b.iter(|| encode_alternative_bytes(black_box(u128::MAX), black_box(&mut buf)))
    });

    c.bench_function("encode_alternative_bytes_random", |b| {
        let mut buf = [0; 22];
        b.iter(|| {
            encode_alternative_bytes(black_box(random_u128s.next().unwrap()), black_box(&mut buf))
        })
    });

    c.bench_function("encode_alternative_buf", |b| {
        b.iter(|| encode_alternative_buf(black_box(u128::MAX), black_box(&mut String::new())))
    });

    c.bench_function("encode_alternative_buf_random", |b| {
        b.iter(|| {
            encode_alternative_buf(
                black_box(random_u128s.next().unwrap()),
                black_box(&mut String::new()),
            )
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
