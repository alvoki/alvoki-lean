# Versioned compaction experiment

This experiment merges two immutable runs in memory. A caller supplies the oldest snapshot that must remain readable and a snapshot at or above it. It measures producing persistent-format bytes, reading a snapshot directly over the input runs, and scanning a materialized output. [Lean kernel](../lean/Compaction.lean) · [Rust control](../rust/src/bin/alvoki-compaction.rs)

## Format and visibility

The experimental format uses little-endian unsigned 64-bit words. Its 16-byte header contains the entry count and version 3. Each 32-byte entry contains key, sequence, kind, and value. Kind 0 is a put. Kind 1 is a tombstone and has a zero value field. Entries sort by key ascending and sequence descending. The parser requires exact length and strict order within that composite key. If both inputs contain the same key and sequence, the right input supplies the entry.

A snapshot sees the highest sequence at or below its sequence for each key. A tombstone at that sequence masks all earlier values of the key. During compaction, retain all versions newer than the floor and the newest version at or below the floor. For any snapshot at or above the floor, the visible version is either above the floor or is that retained boundary version. Retain boundary tombstones so they can mask older runs at other levels. The CLI rejects reads below the floor. A full LSM would choose the floor from its active snapshots and coordinate publication of compacted runs.

The independent Python oracle stores the exact versions in a dictionary, applies right-hand precedence, and groups the ordered history by key. Fixtures cover empty runs, sequence and key extrema, older snapshots, tombstones, reinsertion, equal-sequence conflicts, malformed headers and rows, and requests outside the supported snapshot bounds. Each timed dataset is also checked byte for byte for both writers. Snapshot folds are checked against the oracle. [Oracle and fixtures](../benchmarks/compaction.py)

The Lean proofs connect the stock parser, per-row and span writers, and both scans to the logical history. A reparsed compaction preserves the winning entry and the full ordered visible row list at every supported snapshot. The sequential model extends that replacement theorem to arbitrary older and newer runs. [Proof inventory](verification-status.md) · [Executable refinements](../lean/CompactionProofs.lean)

## Workloads and timing

The seeded workload proxies start with a sorted base run comprising two thirds of the input rows. The other run models range ingestion in batches, repeated updates to a hot set, deletion and reinsertion in that hot set, or a uniform mix of inserts and updates. The snapshot floor is one quarter of the update window behind the latest sequence. The delete–reinsert case reads at that older floor. The other cases read at the latest sequence.

Timers start after input loading and validation. Row and span modes write a packed output. Spans merge contiguous retained entries from a single input into one copy. Pipeline time includes span materialization, output validation, and a snapshot scan. The read mode starts with a prevalidated compacted run so it estimates the cost of another consumer. Direct scans consume the same visible records over both input runs. The benchmark uses one pinned CPU, one discarded warm-up and nine retained trials per process. [Harness](../benchmarks/compaction.py) · [Reproduction script](../scripts/compaction.sh)

## Results

Medians in milliseconds at one million total input rows. The materialization column uses the faster of row and span emission for each implementation. The pipeline uses span emission and includes one scan.

| Workload | Retained rows | Visible rows | Contiguous spans | Singleton spans | Direct Lean / Rust | Materialize Lean / Rust | Pipeline Lean / Rust |
|---|---:|---:|---:|---:|---:|---:|---:|
| Range ingest | 937,536 | 917,056 | 165,890 | 83,125 | 2.05 / 2.39 | 6.23 / 3.42 | 9.12 / 6.52 |
| Hot updates | 749,999 | 666,666 | 102,392 | 44,789 | 2.85 / 3.13 | 6.27 / 3.67 | 8.73 / 6.75 |
| Delete and reinsert | 749,999 | 649,452 | 102,548 | 44,936 | 3.21 / 3.79 | 6.09 / 4.06 | 9.10 / 7.17 |
| Uniform mix | 864,112 | 814,401 | 441,305 | 247,201 | 5.88 / 5.83 | 14.17 / 7.00 | 17.81 / 11.97 |

Direct scans were approximately at parity or ahead in this run. Stock Lean materialization was 1.50–2.02× Rust time. Contiguous runs averaged seven entries in the hot-key cases and two in the uniform mix. A proof-carrying machine-index reader removes per-field bounds checks in the merge selector. The versioned parser uses the same bounded reader in a scalar loop, which matters when output validation is in the timer. [Raw compaction trials](../benchmarks/followups/compaction-trials.csv)

If the bytes are optional, one consumer was faster on the direct path in every profile. At the same snapshot, estimate the cost for K consumers by comparing K direct scans with one pipeline plus K−1 scans of the already validated output. On the measured Lean medians, materializing first becomes faster at about six scans for hot updates and five scans for delete–reinsert or uniform mix. Range ingest has only a 0.29 ms per-scan advantage from reuse and the estimate is about 26 scans. A write required by compaction or persistence is a separate requirement. These are synthetic inputs and CPU-time estimates. Actual runs will depend on snapshot lifetimes, output reuse, caching, and I/O. [Raw compaction trials](../benchmarks/followups/compaction-trials.csv)

## Fixed-width write candidate

The opt-in build inlines the existing guarded `ByteArray.copySlice` specialization into the generated compaction C. It uses a constant-width copy for a disjoint source and exclusive destination with enough capacity. Shared, aliased, clipped, and capacity-growing cases use the stock fallback. This exercises a possible standard runtime optimization through the existing Lean builder API. The proof states the source-level byte contract and the native prototype is checked by differential tests. [Copy candidate](../lean/runtime-experiment/fixed-copy.h) · [Builder contract](../lean/ScopedBytes.lean) · [Copy contract fixtures](../lean/MergePhases.lean)

| Workload | Stock rows | Fixed-copy rows | Stock spans | Fixed-copy spans | Best Rust materialization |
|---|---:|---:|---:|---:|---:|
| Range ingest | 7.39 | 4.27 | 6.23 | 5.96 | 3.42 |
| Hot updates | 7.33 | 5.09 | 6.27 | 6.24 | 3.67 |
| Delete and reinsert | 7.48 | 5.43 | 6.09 | 5.97 | 4.06 |
| Uniform mix | 14.59 | 10.22 | 14.17 | 12.99 | 7.00 |

The fixed-width candidate cut row emission by 27–42%, with the fastest candidate 1.25–1.46× the best Rust writer. Its effect on coalesced writes was smaller. Singleton spans represented 44–56% of copies after coalescing and 6–29% of retained rows. The span pipeline results varied in both directions, within about 5%. This supports a targeted write optimization for four-word rows when materialization is required. It also gives a concrete reason to compare any new lowering with stock coalescing and the full pipeline. [Raw compaction trials](../benchmarks/followups/compaction-trials.csv)

## Reproduce

```sh
bash scripts/check.sh
bash scripts/check.sh --runtime
bash scripts/compaction.sh --fixed-copy --out /tmp/alvoki-compaction.csv
python3 benchmarks/compaction.py --summarize /tmp/alvoki-compaction.csv
```

[Environment and build commands](../benchmarks/followups/environment.txt) · [Version-1 regressions and proof results](fast-path-refinement.md)
