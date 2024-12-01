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
```
cargo build --release
```

Run tests:
```
# if you have cargo-nextest
cargo nextest run
# otherwise
cargo test
```

Run benchmarks:
```
cargo bench
```
  
## Benchmark results

Benchmarking on a Ryzen 3900X CPU with 32 GiB of RAM.

```
     Running benches/hushtable.rs (target/release/deps/hushtable-66baac9cc39eaa1b)
insertion/Hushtable     time:   [7.6673 µs 7.6786 µs 7.6918 µs]                                 
insertion/std           time:   [15.404 µs 15.417 µs 15.429 µs]                           

removal/Hushtable       time:   [7.6766 µs 7.7025 µs 7.7332 µs]                               
Found 2 outliers among 100 measurements (2.00%)
  2 (2.00%) high mild
removal/std             time:   [14.910 µs 14.933 µs 14.967 µs]                         

lookup/Hushtable        time:   [6.4002 µs 6.4332 µs 6.4647 µs]                              
lookup/std              time:   [10.593 µs 10.598 µs 10.604 µs]                        
Found 3 outliers among 100 measurements (3.00%)
  1 (1.00%) low severe
  1 (1.00%) low mild
  1 (1.00%) high mild

     Running benches/realistic.rs (target/release/deps/realistic-daa41d96750f48dd)
insert_dataset/Hushtable                                                                            
                        time:   [62.116 µs 62.513 µs 62.845 µs]
Found 3 outliers among 100 measurements (3.00%)
  3 (3.00%) low severe
insert_dataset/std      time:   [50.877 µs 50.980 µs 51.104 µs]                               

remove_dataset/Hushtable                                                                            
                        time:   [35.303 µs 35.367 µs 35.438 µs]
Found 3 outliers among 100 measurements (3.00%)
  3 (3.00%) high mild
remove_dataset/std      time:   [39.869 µs 39.907 µs 39.950 µs]                               
Found 5 outliers among 100 measurements (5.00%)
  2 (2.00%) high mild
  3 (3.00%) high severe

lookup_dataset/Hushtable                                                                            
                        time:   [21.820 µs 21.900 µs 21.996 µs]
Found 3 outliers among 100 measurements (3.00%)
  2 (2.00%) high mild
  1 (1.00%) high severe
lookup_dataset/std      time:   [25.469 µs 25.576 µs 25.691 µs]                               
Found 2 outliers among 100 measurements (2.00%)
  2 (2.00%) high mild
```
