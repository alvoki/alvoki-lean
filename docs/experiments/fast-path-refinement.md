# Stock Lean fast-path refinement

The adaptive and bounded-window emitters now share a span writer. A span carries erased evidence of progress, its source extent, and strict preference over the competing head key. The worker appends exactly the logical prefix belonging to that source. The kernel checks that both policies serialize the same right-biased union as the stock per-record merge. The accepted replay trace likewise determines the same payload and row count, and checked streaming replay outputs the same block. [Span implementation](../../lean/SpanMerge.lean) · [Merge audit](../../lean/MergeProofs.lean) · [Replay validation and proof](../../lean/MergePhases.lean)

The v1 codec has both round trips. For a strictly ordered record array whose encoding fits the format and machine bounds, the executable parser accepts `encodeV1` and `decodeV1` returns the exact array. Any accepted v1 block decodes and re-encodes to its exact original bytes. The codec is available in `BlockCodec`. The packed kernel loads now check record bounds before computing offsets and use a proof-carrying word read. `PackedRun` exposes the existing per-record merge and the proved branching direct scan. [Codec and audit](../../lean/BlockCodec.lean) · [Packed run API](../../lean/PackedRun.lean)

## Performance checks

The before-and-after comparison interleaved binaries built from the previous revision and the candidate on identical v1 inputs. It took 12 randomized process rounds per build on one pinned CPU, retaining three timings after one warm-up in each process. At one million rows the paired medians were:

| Workload | Before, ms | After, ms |
|---|---:|---:|
| Alternating direct scan | 1.969 | 1.083 |
| Shuffled direct scan | 6.059 | 5.337 |
| Alternating adaptive merge | 8.128 | 8.903 |
| Alternating bounded-window merge | 8.654 | 8.671 |
| Clustered bounded-window merge | 1.038 | 1.118 |
| Update-heavy bounded-window merge | 6.041 | 5.298 |
| Validate interleaved | 0.320 | 0.321 |

The direct scans benefited from using record bounds instead of repeated byte-extent tests. The measured writer changes vary by profile, including a 9.5% increase for alternating adaptive merge. In the separate matched Rust run, the clustered bounded-window pipeline took 5.50 ms in Lean and 5.52 ms in Rust. Shuffled materialization remained around 4.8× Rust time for the fastest tested stock variants. [Paired trials](../../benchmarks/followups/paired-trials.csv) · [Matched Rust trials](../../benchmarks/followups/fused-merge-trials.csv)

The current verification status records the audited paths and the remaining prepared-plan and online coalescing proofs. [Verification status](../verification-status.md#packed-output-and-merge) · [Versioned compaction results](compaction.md)
