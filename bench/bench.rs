use criterion::measurement::Measurement;
use criterion::{criterion_group, criterion_main, BenchmarkGroup, Criterion};

use dark_integers::MLUInt;

fn bench_mluint_mul<'a, M: Measurement>(group: &mut BenchmarkGroup<'a, M>) {
    let x = MLUInt::<u64, 4>::new([
        0x6c26106662c892a7,
        0x45aa5d894a1a80b6,
        0x060a4869481b26a4,
        0xe5f25e3a708f7a20,
    ]);
    let y = MLUInt::<u64, 4>::new([
        0x664f71040649d38d,
        0xa3e4920bd6b13afc,
        0xadb5ced2d89e0550,
        0x811f0dd5524bf83d,
    ]);
    group.bench_function("MLUInt::<u64, 4>::mul", |b| b.iter(|| x * y));

    let x = MLUInt::<u32, 8>::new([
        0x6c261066, 0x62c892a7, 0x45aa5d89, 0x4a1a80b6, 0x060a4869, 0x481b26a4, 0xe5f25e3a,
        0x708f7a20,
    ]);
    let y = MLUInt::<u32, 8>::new([
        0x664f7104, 0x0649d38d, 0xa3e4920b, 0xd6b13afc, 0xadb5ced2, 0xd89e0550, 0x811f0dd5,
        0x524bf83d,
    ]);
    group.bench_function("MLUInt::<u32, 8>::mul", |b| b.iter(|| x * y));
}

fn bench_mluint(c: &mut Criterion) {
    let mut group = c.benchmark_group("MLUInt");
    bench_mluint_mul(&mut group);
    group.finish();
}

criterion_group!(benches, bench_mluint);
criterion_main!(benches);
