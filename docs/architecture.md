# Experiment architecture

- `rust/src/lib.rs` borrows a packed slice and reads words with `u64::from_le_bytes`. Decode materializes a contiguous `Vec<(u64, u64)>`.
- `lean/Block.lean` retains an immutable packed `ByteArray`. Both variants search packed data directly. Decode materializes an `Array (UInt64 × UInt64)`. The checked variant assembles words with eight checked reads and uses a loop to append bytes. The second variant checks the word extent once, uses proof-carrying byte reads, and unrolls the eight writes per word. The native harness selects it with `ALVOKI_FAST=1`.
- `lean/Proofs.lean` reasons about the executable lower-bound function through its predicate interface and proves selected properties of the packed byte operations. `verus/search.rs` implements the same search algorithm over a sorted key slice.
- `fixtures/generate.py` independently constructs binary fixtures using Python's fixed-width `struct` operations. The test oracle uses `bisect_left` for bounds, a dictionary for point answers, and Python integer arithmetic for range checksums.
- `benchmarks/run.py` runs the native executables against shared inputs, consumes query results, compares checksums, and records trial times and peak memory. `benchmarks/summarize.py` summarizes batch averages and throughput.
