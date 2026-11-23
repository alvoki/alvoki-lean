# Native SIMD scans and output builders

Clang auto-vectorized the Lean fixed-stride scan after we moved the extent check out of the loop and supplied a Lean proof for each byte read. The resulting native scan reached the performance of the vectorized Rust control. Output construction remains slower, especially when the algorithm must emit individual records.

## SIMD scan

One million interleaved version-1 records, median of nine timed batches on the VM.

| Scan variant | Time |
|---|---:|
| Lean, prior guarded reader | 0.868 ms |
| Lean, one extent check and a simple reduction | 0.220 ms |
| Lean, four independent accumulators and a scalar tail | 0.287 ms |
| Rust, vectorization disabled | 0.336 ms |
| Rust, default release | 0.237 ms |

Clang reported vectorization width 2 and interleave count 2 for the simple reduction. Disassembly shows packed loads, XOR, and 64-bit lane adds. The four-accumulator loop compiled to an unrolled scalar loop in the inspected entry point. The Rust controls use the same source and were built separately with loop and SLP vectorization disabled for the scalar control. We inspected both binaries. At 1,000 records, the vectorized Lean and Rust scans measured 241 and 240 ns per block. At 100,000 records they measured 22.3 and 21.3 µs. The small differences at these scales are VM observations. [Code generation evidence](../benchmarks/results/packed/native-codegen.txt)

The Lean loop borrows the input, performs a fixed-stride XOR and wrapping-add reduction, and passes erased bounds proofs to the byte-load primitive. The generated hot loop has no per-word extent branches. The earlier gap included the effect of those branches, as well as the benefit Rust was getting from SIMD. Vectorization is a result of this loop shape and compiler configuration.

## Merge

Both implementations compare the same packed inputs and write a new version-1 block. Span lengths are consecutive winners from one input before switching sides. The span variant probes the eighth record. If that record still wins, it finds the end of the winning span by binary search and emits it with one slice copy. Equal keys still select the right value. The indexed variant pre-sizes the output and writes one pair per winner with one extent check.

| Pattern at 1M total input records | Lean per-record copy | Lean span copy | Lean indexed | Rust per-record copy |
|---|---:|---:|---:|---:|
| 1, perfect alternation | 7.80 ms | 9.75 ms | 10.54 ms | 2.36 ms |
| 4 | 8.33 ms | 10.13 ms | 9.66 ms | 2.27 ms |
| 16 | 8.91 ms | 4.03 ms | 10.28 ms | 2.21 ms |
| 64 | 7.94 ms | 3.00 ms | 9.16 ms | 2.29 ms |
| 256 | 8.68 ms | 2.07 ms | 9.87 ms | 2.48 ms |
| Overlap with collisions | 3.92 ms | 2.65 ms | 6.31 ms | 1.31 ms |
| Disjoint | 4.17 ms | 0.75 ms | 5.75 ms | 1.32 ms |

The Rust column uses the Rust per-record implementation throughout. The prior Rust disjoint fast path took 0.75 ms. Short spans pay for probes that rarely succeed. Perfect alternation still needs a cheap way to emit individual records. A next merge experiment can enable probing only after observing longer spans, and compare against a more direct bulk output API.

## Fresh encoding

All variants read a packed block, flip the low bit of every value, and produce a new byte-for-byte equivalent version-1 block. This packed-to-packed transform exercises reading and writing fresh buffers without materializing records. It is a different workload from the earlier scalar-array encoder benchmark.

| Variant at 1M records | Time |
|---|---:|
| Lean direct indexed writes, one extent check per word | 10.75 ms |
| Lean direct indexed writes, one extent check per pair | 7.78 ms |
| Lean reusable 4 KiB staging buffer | 15.59 ms |
| Rust packed transform | 1.33 ms |

Sharing the extent check helped. The staging buffer still performs individual byte stores before adding a copy, and was the slowest variant. The compiled Lean writer retains per-byte copy-on-write handling. A native bulk store needs a compiler or runtime path that makes ownership and access checks once per span or record. The C prototype from the previous experiment remains a separate reference.

## Verification and reproduction

The native experiment links the generated Lean code and standard runtime. It has no dependency on the experimental C object. Lean checks read bounds, store bounds, and recursive loop termination. The existing in-bounds word theorem still checks. Thirteen scan and encode fixtures cover full-width records, empty blocks, scan tails, and staging boundaries. Twenty exact merge fixtures exercise duplicate keys and all measured span lengths. Full scan, merge, and encoder refinement remain open.

The harness pins one CPU, uses deterministic inputs and variant order, discards one warm-up run, and records nine repeats at 1,000, 100,000, and 1,000,000 records. Input loading and parsing are outside the timers. The original, optimization, and packed experiment fixture suites also passed.

```sh
bash scripts/native.sh --out /tmp/alvoki-native.csv
python3 benchmarks/native.py --summarize /tmp/alvoki-native.csv
objdump -d --disassemble=lp_alvoki_Alvoki_NativeTune_scanScalar lean/.lake/build/bin/alvoki-native
```

- [Raw trials](../benchmarks/results/packed/native-trials.csv)
- [Summary](../benchmarks/results/packed/native-summary.csv)
- [VM environment](../benchmarks/results/packed/native-environment.txt)
