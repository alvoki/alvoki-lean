# Fused span emission and direct merged scans

This round tests two stock-Lean alternatives. The first emits each winning extent directly into the proved packed builder. The second consumes the merged records into a checksum and skips creating a third packed block. Both preserve right-hand values on duplicate keys.

## Fused span emission

After consecutive wins from one source, the new emitter checks the eighth record and searches inside a window of at most 256 records. If the last record in the window wins, the whole window can be emitted with one copy. It caches the losing head and emits immediately. There is no winner trace or separately allocated span plan. The existing adaptive baseline also selects and emits in one pass and searches a wider range for long spans.

Medians at one million input records, nine trials on the pinned VM. Times are milliseconds. The pipeline adds output validation, a full packed scan, and 20,000 mixed lookups. The Rust column uses the faster of the existing per-record and scoped controls for that workload.

| Profile | Plain Lean merge | Adaptive Lean merge | Fused Lean merge | Best Rust merge | Adaptive Lean pipeline | Fused Lean pipeline |
|---|---:|---:|---:|---:|---:|---:|
| Alternating | 7.92 | 8.17 | 9.80 | 2.55 | 14.24 | 15.41 |
| Clustered ranges | 8.78 | 1.23 | 1.07 | 2.90 | 5.70 | 6.21 |
| Shuffled interleave | 13.65 | 12.97 | 13.56 | 2.69 | 17.80 | 17.98 |
| Update-heavy | 6.21 | 5.44 | 6.17 | 1.65 | 9.10 | 9.05 |

Bounded search gave a 13% lower clustered merge median than the adaptive path. The clustered pipeline medians overlap in their observed ranges, with the adaptive median lower. The other merge profiles favor the existing implementations. The faster Rust merge is per-record for alternation and scoped for the other rows. Rust's clustered pipeline took 7.06 ms. These profiles are synthetic, and the small differences are VM measurements.

## Direct merged scans

The direct scan advances through both source runs and accumulates the same wrapping XOR-and-sum checksum as the materialized scan. It needs the input runs until the scan finishes. The materialized path has both inputs live during the merge and also allocates the output. Both paths decode the same surviving records. Materialized paths include validation of the new block.

| Profile | Best materialized Lean scan | Direct Lean scan | Direct Rust scan | Lean peak RSS, materialized → direct |
|---|---:|---:|---:|---:|
| Alternating | 8.91 ms | 2.09 ms | 1.70 ms | 40.4 → 24.3 MiB |
| Clustered ranges | 2.00 ms | 2.17 ms | 2.00 ms | 40.4 → 24.3 MiB |
| Shuffled interleave | 13.69 ms | 6.17 ms | 4.72 ms | 40.4 → 24.3 MiB |
| Update-heavy | 5.76 ms | 2.17 ms | 2.15 ms | 34.4 → 24.3 MiB |

Peak RSS is the process's Linux high-water mark across warm-up and timed trials, including runtime and both input files. At this scale, the input payload is about 15.26 MiB total. The contiguous output holds another 15.26 MiB on non-overlapping profiles and about 9.54 MiB for update-heavy inputs. RSS includes allocator and runtime overhead.

Direct scan is the stronger stock-Lean improvement for a single-pass consumer. It is about 4.3× faster on alternation, 2.2× on shuffled interleave, and 2.7× on update-heavy inputs versus the fastest materialized Lean path. Clustered merge can copy long spans and then scan the result with SIMD, so it remains competitive for time. The direct path saves memory there. Rust's scoped materialize-and-scan was faster than either direct implementation on shuffled data at 3.45 ms. The direct scan does not provide a durable block or a sorted index for later random reads.

A second direct variant selects a source and advances both cursors via comparisons. Generated Lean assembly shows conditional moves alongside branches. It was slower than the simple branching scan in all four profiles at one million records. The benchmark includes corresponding Rust controls.

## Verification and reproduction

The fused emitter uses the proved `Builder.copyToTail` byte contract. Lean checks recursion termination. Independent fixtures check the merge output byte for byte and compare both scan forms and the pipeline query result against the same right-biased union. The suite covers empty runs, full-width keys, duplicates, and edges around the lookahead and window sizes. Every measured merge output is also checked against the oracle. The full fused merge and direct scan refinement proofs remain open.

The benchmark uses stock Lean 4.36.0, a pinned CPU, fixed workloads, and one discarded warm-up per process. Input loading is excluded from time. All 22 fixtures passed, along with the earlier reproduction, merge-phase, and stock-builder checks.

```sh
bash scripts/fused-merge.sh --out /tmp/alvoki-fused-merge.csv
python3 benchmarks/fused_merge.py --summarize /tmp/alvoki-fused-merge.csv
```

- [Raw trials](../../benchmarks/results/packed/fused-merge-trials.csv)
- [Summary](../../benchmarks/results/packed/fused-merge-summary.csv)
- [VM environment](../../benchmarks/results/packed/fused-merge-environment.txt)
