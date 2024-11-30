use std::hash::{BuildHasherDefault, DefaultHasher};

use criterion::{black_box, criterion_group, criterion_main, Criterion};

pub fn generate_dataset() -> Vec<(String, usize)> {
    let book = include_str!("./book.txt");
    book.split_whitespace()
        .map(|word| word.to_lowercase())
        .fold(
            std::collections::HashMap::<String, usize>::new(),
            |mut map: std::collections::HashMap<String, usize>, word: String| {
                if let Some(count) = map.get_mut(&word) {
                    *count += 1;
                } else {
                    map.insert(word, 1);
                }
                map
            },
        )
        .into_iter()
        .collect()
}

pub fn criterion_benchmark(c: &mut Criterion) {
    const MAP_SIZE: usize = 2 * 1024;
    const NUM_ELEMS: usize = 1024;

    let dataset = generate_dataset();
    let dataset = &dataset[0..NUM_ELEMS];

    let mut insert = c.benchmark_group("insert_dataset");
    insert.bench_function("Hushtable", |b| {
        b.iter_batched_ref(
            || -> hushtable::collections::HashMap<String, usize, BuildHasherDefault<DefaultHasher>, MAP_SIZE> {
                hushtable::collections::HashMap::with_capacity::<MAP_SIZE>()
            },
            |map| {
                for (k,v) in dataset{
                    map.insert(black_box(k.clone()), *v).unwrap();
                }
            },
            criterion::BatchSize::LargeInput,
        );
    });

    insert.bench_function("std", |b| {
        b.iter_batched_ref(
            || std::collections::HashMap::with_capacity(MAP_SIZE),
            |map| {
                for (k, v) in dataset {
                    map.insert(black_box(k.clone()), black_box(*v));
                }
            },
            criterion::BatchSize::LargeInput,
        );
    });

    insert.finish();

    let mut remove = c.benchmark_group("remove_dataset");
    remove.bench_function("Hushtable", |b| {
        b.iter_batched_ref(
            || -> hushtable::collections::HashMap<String, usize, BuildHasherDefault<DefaultHasher>, MAP_SIZE> {
                let mut map = hushtable::collections::HashMap::with_capacity::<MAP_SIZE>();
                for (k,v) in dataset {
                    map.insert(k.clone(), *v).unwrap();
                }
                map
            },
            |map| {
                for (k, _) in dataset {
                    map.remove(black_box(k)).unwrap();
                }
            },
            criterion::BatchSize::LargeInput,
        );
    });

    remove.bench_function("std", |b| {
        b.iter_batched_ref(
            || {
                let mut map = std::collections::HashMap::with_capacity(MAP_SIZE);
                for (k, v) in dataset {
                    map.insert(k.clone(), *v);
                }
                map
            },
            |map| {
                for (k, _) in dataset.iter().take(NUM_ELEMS as usize) {
                    map.remove(black_box(k)).unwrap();
                }
            },
            criterion::BatchSize::LargeInput,
        );
    });

    remove.finish();

    let mut lookup = c.benchmark_group("lookup_dataset");
    lookup.bench_function("Hushtable", |b| {
        b.iter_batched_ref(
            || -> hushtable::collections::HashMap<String, usize, BuildHasherDefault<DefaultHasher>, MAP_SIZE> {
                let mut map = hushtable::collections::HashMap::with_capacity::<MAP_SIZE>();
                for (k,v) in dataset {
                    map.insert(k.clone(), *v).unwrap();
                }
                map
            },
            |map| {
                for (k, _) in dataset {
                    map.get(black_box(k)).unwrap();
                }
            },
            criterion::BatchSize::LargeInput,
        );
    });

    lookup.bench_function("std", |b| {
        b.iter_batched_ref(
            || {
                let mut map = std::collections::HashMap::with_capacity(MAP_SIZE);
                for (k, v) in dataset {
                    map.insert(k.clone(), *v);
                }
                map
            },
            |map| {
                for (k, _) in dataset.iter().take(NUM_ELEMS as usize) {
                    map.get(black_box(k)).unwrap();
                }
            },
            criterion::BatchSize::LargeInput,
        );
    });

    lookup.finish();
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
