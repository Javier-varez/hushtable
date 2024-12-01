# Hushtable

## Overview

Implements a HashMap with the following characteristics:
- Open addressing with linear probing,
- Keeps temporal information about the order of added/updated entries.
- Fixed size, determined at compile-time using Rust's const-generics.
- Generic over keys and value types.
- Allows to select the hashing algorithm, creating it with `with_hasher_and_capacity`.
- Allows to select the static size, creating it with `with_capacity`.

It has been optimized for performance by:
- Distribution of key, value, status metadata (empty, full, deleted) and 
  time metadata (prev and next entries) in separate contiguous arrays, to benefit from 
  cache locality.
- Only allocates memory once during construction with a single Box:new() call.
- All operations are implemented with O(1) best case performance.
- Adding prefetching of data that would be used soon (like the values array) 
  where it showed performance benefits.

Additional optimizations that could be performed:
- Linear probing could be optimized by using SSE instructions and embedding 
  a part of the hash into the metadata. This would be a similar concept to swisstables
  and allow to paralellize the lookup across 16 or more entries at a time.

## Building and running

All the code has been kept with 0 clippy lints and formatted with rustfmt.

Build the library with:
```shell
cargo build --release
```

Run tests:
```shell
# if you have cargo-nextest
cargo nextest run
# otherwise
cargo test
```

Run benchmarks:
```shell
# if needed, install criterion
cargo binstall cargo-criterion
# then run the benchmarks
cargo criterion
```
  
## Benchmark results

Benchmarking on a Ryzen 3900X CPU with 32 GiB of RAM.

```
insertion/Hushtable     time:   [9.1546 µs 9.3686 µs 9.5452 µs]
insertion/std           time:   [14.966 µs 14.984 µs 15.003 µs]

removal/Hushtable       time:   [7.5918 µs 7.6005 µs 7.6107 µs]
removal/std             time:   [14.716 µs 14.748 µs 14.788 µs]

lookup/Hushtable        time:   [6.5004 µs 6.5051 µs 6.5113 µs]
lookup/std              time:   [10.716 µs 10.735 µs 10.753 µs]

insert_dataset/Hushtable
                        time:   [62.557 µs 63.112 µs 63.586 µs]
insert_dataset/std      time:   [49.631 µs 49.754 µs 49.901 µs]

remove_dataset/Hushtable
                        time:   [34.089 µs 34.495 µs 34.884 µs]
remove_dataset/std      time:   [37.891 µs 37.942 µs 37.999 µs]

lookup_dataset/Hushtable
                        time:   [22.393 µs 22.507 µs 22.640 µs]
lookup_dataset/std      time:   [22.397 µs 22.478 µs 22.574 µs]
```
