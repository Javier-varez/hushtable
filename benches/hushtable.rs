use std::hash::{BuildHasherDefault, DefaultHasher};

use criterion::{black_box, criterion_group, criterion_main, Criterion};

pub fn criterion_benchmark(c: &mut Criterion) {
    const MAP_SIZE: usize = 2 * 1024;
    const NUM_ELEMS: u32 = 1024;

    let mut insertion = c.benchmark_group("insertion");
    insertion.bench_function("Hushtable", |b| {
        b.iter_batched_ref(
            || -> hushtable::collections::HashMap<u32, u32, BuildHasherDefault<DefaultHasher>, MAP_SIZE> {
                hushtable::collections::HashMap::with_capacity::<MAP_SIZE>()
            },
            |map| {
                for i in 0..NUM_ELEMS {
                    map.insert(black_box(i), black_box(i + 1)).unwrap();
                }
            },
            criterion::BatchSize::LargeInput,
        );
    });

    insertion.bench_function("std", |b| {
        b.iter_batched_ref(
            || std::collections::HashMap::with_capacity(MAP_SIZE),
            |map| {
                for i in 0..NUM_ELEMS {
                    map.insert(black_box(i), black_box(i + 1));
                }
            },
            criterion::BatchSize::LargeInput,
        );
    });

    insertion.finish();

    let mut removal = c.benchmark_group("removal");
    removal.bench_function("Hushtable", |b| {
        b.iter_batched_ref(
            || -> hushtable::collections::HashMap<u32, u32, BuildHasherDefault<DefaultHasher>, MAP_SIZE> {
                let mut map = hushtable::collections::HashMap::with_capacity::<MAP_SIZE>();
                for i in 0..NUM_ELEMS {
                    map.insert(black_box(i), black_box(i + 1)).unwrap();
                }
                map
            },
            |map| {
                for i in 0..NUM_ELEMS {
                    map.remove(black_box(&i)).unwrap();
                }
            },
            criterion::BatchSize::LargeInput,
        );
    });

    removal.bench_function("std", |b| {
        b.iter_batched_ref(
            || {
                let mut map = std::collections::HashMap::with_capacity(MAP_SIZE);
                for i in 0..NUM_ELEMS {
                    map.insert(black_box(i), black_box(i + 1));
                }
                map
            },
            |map| {
                for i in 0..NUM_ELEMS {
                    map.remove(black_box(&i)).unwrap();
                }
            },
            criterion::BatchSize::LargeInput,
        );
    });

    removal.finish();

    let mut lookup = c.benchmark_group("lookup");
    lookup.bench_function("Hushtable", |b| {
        b.iter_batched_ref(
            || -> hushtable::collections::HashMap<u32, u32, BuildHasherDefault<DefaultHasher>, MAP_SIZE> {
                let mut map = hushtable::collections::HashMap::with_capacity::<MAP_SIZE>();
                for i in 0..NUM_ELEMS {
                    map.insert(black_box(i), black_box(i + 1)).unwrap();
                }
                map
            },
            |map| {
                for i in 0..NUM_ELEMS {
                    map.get(black_box(&i)).unwrap();
                }
            },
            criterion::BatchSize::LargeInput,
        );
    });

    lookup.bench_function("std", |b| {
        b.iter_batched_ref(
            || {
                let mut map = std::collections::HashMap::with_capacity(MAP_SIZE);
                for i in 0..NUM_ELEMS {
                    map.insert(black_box(i), black_box(i + 1));
                }
                map
            },
            |map| {
                for i in 0..NUM_ELEMS {
                    map.get(black_box(&i)).unwrap();
                }
            },
            criterion::BatchSize::LargeInput,
        );
    });

    lookup.finish();
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
