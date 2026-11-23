# Native single-record emission and packed updates

Copying a packed block once and mutating its changed bytes brought a narrow transform close to Rust. General value-word updates and alternating merge still have significant gaps. All the Lean variants in this round use the standard Lean runtime without a custom C object.

## Fresh packed output

Medians at one million version-1 records, with nine timed trials on the VM. Each variant returns a fresh block. The input is already validated and loaded. The low-bit workload flips one bit in each value. The dense workload applies a mask that changes all eight bytes of each value. Keys and headers stay the same.

| Workload and output strategy | Lean | Rust |
|---|---:|---:|
| Low bit, rebuild records | 7.56 ms | 1.20 ms |
| Low bit, bulk copy then update one byte per record | 1.20 ms | 1.01 ms |
| Dense mask, rebuild records | 7.61 ms | 1.26 ms |
| Dense mask, bulk copy then update one word per record | 4.93 ms | 1.01 ms |

Copying unchanged bytes through the standard slice primitive removes per-byte stores for keys and headers. The low-bit variant also avoids rewriting the seven unchanged bytes in each value. Generated x86-64 code retains one copy-on-write slow-path call site in the byte-patch loop, eight in the word writer, and sixteen in the record writer. These are branch destinations, so the counts do not imply that the runtime copied the buffer at every store. [Disassembly counts](../benchmarks/emission-codegen.txt)

The low-bit result supports preserving known-unchanged packed bytes for transformations. The dense result leaves about a 4.9× gap against the equivalent Rust copy-and-patch path. The experiment starts from packed bytes and measures production of a new block. Encoding from an array of owned records is a separate workload.

## Merge

Both implementations produce the same right-biased union for duplicate keys. The simple Lean merge copies one whole packed record per winner. The cached variant keeps both head keys and reloads only the advancing side. The adaptive variants also gate span probes on consecutive wins. The pre-sized copy variant initializes the destination and overwrites packed records by offset.

| Input pattern at 1M total records | Simple Lean | Best adaptive Lean | Eager span Lean | Rust |
|---|---:|---:|---:|---:|
| Perfect alternation | 7.71 ms | 7.85 ms | 9.74 ms | 1.95 ms |
| Four consecutive wins | 8.23 ms | 7.90 ms | 9.82 ms | 2.15 ms |
| Sixteen consecutive wins | 7.74 ms | 5.73 ms | 4.40 ms | 2.19 ms |
| Mixed winner spans | 9.27 ms | 2.63 ms | 2.63 ms | 2.68 ms |
| Overlap with collisions | 4.34 ms | 2.39 ms | 2.91 ms | 1.38 ms |
| Disjoint | 4.11 ms | 0.72 ms | 0.77 ms | 1.36 ms |

Mixed spans cycle through lengths 1, 1, 4, 16, 64, 256, 16 and 4. The early adaptive variant probes after one preceding win. The later variant waits for seven preceding wins. Both use an eight-record lookahead before searching for the span boundary. Adaptive gating avoids most of the eager probe penalty on alternating data and preserves the benefit on mixed data. The Rust column uses per-record merge throughout, including disjoint data.

Caching alone took 7.80 ms on alternating inputs, and pre-sizing and overwriting took 9.20 ms. In this workload neither reduced the dominant cost of emitting one record via the generic slice-copy operation. The useful merge change was to make span probing selective. The single-record path still warrants a smaller primitive or compiler optimization.

## Checks and reproduction

The native and Rust controls passed 13 scan/encode fixtures and 21 exact merge fixtures. The encoders are compared against an independent expected block byte for byte. The merge oracle covers collision precedence, full-width keys, empty inputs, and short, long and mixed spans. The original, optimization, and packed suites also passed. Lean checks termination and byte bounds for the low-bit patch loop. Full encoder and merge refinement remain open.

The runner uses the existing native suite, pinned toolchains and CPU affinity, one discarded warm-up per process, and nine trials across 1,000, 100,000 and 1,000,000 records. The first timing round remains in its original files.

```sh
bash scripts/native.sh --out /tmp/alvoki-emission.csv
python3 benchmarks/native.py --summarize /tmp/alvoki-emission.csv
```

- [Raw trials](../benchmarks/emission-trials.csv)
- [Summary](../benchmarks/emission-summary.csv)
- [VM environment](../benchmarks/emission-environment.txt)
