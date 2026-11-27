# Versioned compaction experiment

This experiment merges two immutable runs in memory. A caller supplies the oldest snapshot that must remain readable and a snapshot at or above it. It measures producing persistent-format bytes, reading a snapshot directly over the input runs, and scanning a materialized output. [Lean kernel](../../lean/Alvoki/Compaction/Core.lean) · [Rust control](../../rust/src/bin/alvoki-compaction.rs)

## Format and visibility

Both benchmark implementations use the engine's v3 run layout and select rows according to the same snapshot and retention rules. The benchmark passes the floor explicitly and rejects reads below it. [Versioned run format and visibility](../specifications.md#versioned-runs-version-3)

The independent Python oracle stores the exact versions in a dictionary, applies right-hand precedence, and groups the ordered history by key. Fixtures cover empty runs, sequence and key extrema, older snapshots, tombstones, reinsertion, equal-sequence conflicts, malformed headers and rows, and requests outside the supported snapshot bounds. Each timed dataset is also checked byte for byte for both writers. Snapshot folds are checked against the oracle. [Oracle and fixtures](../../benchmarks/compaction.py)

The Lean proofs connect the stock parser, per-row and span writers, and both scans to the logical history. A reparsed compaction preserves the winning entry and the full ordered visible row list at every supported snapshot. The sequential model extends that replacement theorem to arbitrary older and newer runs. [Proof inventory](../verification-status.md) · [Executable refinements](../../lean/Alvoki/Storage/Proofs/Table/Compaction.lean)

## Workloads and timing

The seeded workload proxies start with a sorted base run comprising two thirds of the input rows. The other run models range ingestion in batches, repeated updates to a hot set, deletion and reinsertion in that hot set, or a uniform mix of inserts and updates. The snapshot floor is one quarter of the update window behind the latest sequence. The delete–reinsert case reads at that older floor. The other cases read at the latest sequence.

Timers start after input loading and validation. Row and span modes write a packed output. Spans merge contiguous retained entries from a single input into one copy. Pipeline time includes span materialization, output validation, and a snapshot scan. The read mode starts with a prevalidated compacted run so it estimates the cost of another consumer. Direct scans consume the same visible records over both input runs. The benchmark uses one pinned CPU, one discarded warm-up and nine retained trials per process. [Harness](../../benchmarks/compaction.py) · [Reproduction script](../../scripts/compaction.sh)

## Results

Medians in milliseconds at one million total input rows. The materialization column uses the faster of row and span emission for each implementation. The pipeline uses span emission and includes one scan.

| Workload | Retained rows | Visible rows | Contiguous spans | Singleton spans | Direct Lean / Rust | Materialize Lean / Rust | Pipeline Lean / Rust |
|---|---:|---:|---:|---:|---:|---:|---:|
| Range ingest | 937,536 | 917,056 | 165,890 | 83,125 | 2.05 / 2.39 | 6.23 / 3.42 | 9.12 / 6.52 |
| Hot updates | 749,999 | 666,666 | 102,392 | 44,789 | 2.85 / 3.13 | 6.27 / 3.67 | 8.73 / 6.75 |
| Delete and reinsert | 749,999 | 649,452 | 102,548 | 44,936 | 3.21 / 3.79 | 6.09 / 4.06 | 9.10 / 7.17 |
| Uniform mix | 864,112 | 814,401 | 441,305 | 247,201 | 5.88 / 5.83 | 14.17 / 7.00 | 17.81 / 11.97 |

Direct scans were approximately at parity or ahead in this run. Stock Lean materialization was 1.50–2.02× Rust time. Contiguous runs averaged seven entries in the hot-key cases and two in the uniform mix. A proof-carrying machine-index reader removes per-field bounds checks in the merge selector. The versioned parser uses the same bounded reader in a scalar loop, which matters when output validation is in the timer. [Raw compaction trials](../../benchmarks/followups/compaction-trials.csv)

If the bytes are optional, one consumer was faster on the direct path in every profile. At the same snapshot, estimate the cost for K consumers by comparing K direct scans with one pipeline plus K−1 scans of the already validated output. On the measured Lean medians, materializing first becomes faster at about six scans for hot updates and five scans for delete–reinsert or uniform mix. Range ingest has only a 0.29 ms per-scan advantage from reuse and the estimate is about 26 scans. A write required by compaction or persistence is a separate requirement. These are synthetic inputs and CPU-time estimates. Actual runs will depend on snapshot lifetimes, output reuse, caching, and I/O. [Raw compaction trials](../../benchmarks/followups/compaction-trials.csv)

## Fixed-width write candidate

The opt-in build inlines the existing guarded `ByteArray.copySlice` specialization into the generated compaction C. It uses a constant-width copy for a disjoint source and exclusive destination with enough capacity. Shared, aliased, clipped, and capacity-growing cases use the stock fallback. This exercises a possible standard runtime optimization through the existing Lean builder API. The proof states the source-level byte contract and the native prototype is checked by differential tests. [Copy candidate](../../lean/runtime-experiment/fixed-copy.h) · [Builder contract](../../lean/ScopedBytes.lean) · [Copy contract fixtures](../../lean/MergePhases.lean)

| Workload | Stock rows | Fixed-copy rows | Stock spans | Fixed-copy spans | Best Rust materialization |
|---|---:|---:|---:|---:|---:|
| Range ingest | 7.39 | 4.27 | 6.23 | 5.96 | 3.42 |
| Hot updates | 7.33 | 5.09 | 6.27 | 6.24 | 3.67 |
| Delete and reinsert | 7.48 | 5.43 | 6.09 | 5.97 | 4.06 |
| Uniform mix | 14.59 | 10.22 | 14.17 | 12.99 | 7.00 |

The fixed-width candidate cut row emission by 27–42%, with the fastest candidate 1.25–1.46× the best Rust writer. Its effect on coalesced writes was smaller. Singleton spans represented 44–56% of copies after coalescing and 6–29% of retained rows. The span pipeline results varied in both directions, within about 5%. This supports a targeted write optimization for four-word rows when materialization is required. It also gives a concrete reason to compare any new lowering with stock coalescing and the full pipeline. [Raw compaction trials](../../benchmarks/followups/compaction-trials.csv)

## Whole-loop v3 writer

The opt-in v3 lowering borrows the validated runs and reserves one private destination. It selects and emits retained rows in one pass, then writes the count and publishes the initialized length. The branching row writer beat both the span writer in the prototype and the existing Rust materialization control in all five profiles in the comparison cohort. At one million inputs, alternating compaction took 2.70 ms with the scoped row writer, 5.17 ms with guarded fixed copies and 3.52 ms with the fastest Rust writer. The row pipeline took 6.00 ms with the scoped writer and 7.08 ms with Rust. The generated row loop uses fixed 32-byte copies. The conditional-move variant traded away performance on regular alternation. [Comparison cohort and commands](../../benchmarks/results/packed/scoped-v3) · [Opt-in build](../../scripts/scoped-compaction.sh)

The stock Lean writer and scan theorems give the byte and snapshot contract. Exact fixtures exercise matching run order, equal-sequence ties, tombstones, floors and malformed inputs. The native implementation relies on the checked generated ABI, validated input extents, and correct native selection and copy behavior. A formal refinement of that implementation remains open. [Lean reference proofs](../../lean/Alvoki/Storage/Proofs/Table/Compaction.lean) · [ABI check](../../lean/runtime-experiment/check-compaction-abi.py)

## Stock exact-size cursor

Encoding 666,666 owned records into an initialized destination on stock Lean took 8.33–8.59 ms across the four datasets. The append codec took 38.51–45.26 ms and the Rust control 1.85–3.02 ms. The cursor carries bounds proofs for all 32 stores per row. It still pays for per-byte stores and dynamic ownership checks. [Exact-size encoder](../../benchmarks/results/packed/stock-v3-cursor)

Using a prebuilt `List` of rows, like the list traversed during flush, the cursor took 9.52–10.34 ms versus 34.71–35.40 ms for append. Both timers include counting the list and building the bytes. This isolates encoding from the other work in a table flush. An executable refinement to the existing codec and a native flush benchmark would establish whether the win carries to the engine. [List comparison](../../benchmarks/results/packed/stock-v3-cursor/README.md#encoding-from-a-list)

An exact-size cursor was slower for compaction. Counting retained rows requires a second traversal, and copying from an existing packed run requires initializing the destination before overwriting it. In the mixed-order comparison, the cursor copy took 14.85–25.51 ms at one million inputs, the best one-pass stock writer took 6.03–11.90 ms, and the scoped row writer took 1.98–4.78 ms. The scoped row pipeline also beat the existing Rust row pipeline in all four profiles in that run. [Mixed-order comparison](../../benchmarks/results/packed/v3-writer-comparison)

## Resuming write-path optimization

Keep stock Lean's row and span writers as materialization controls and use the direct fold when a consumer can work over both inputs. The v1 phase study put selection with a checksum within 18% of Rust while replaying the same winners into bytes took 4.2–4.6× Rust time. The separate v1 scoped writer was at most 8% slower than the fastest matched Rust control across its measured workloads. The v3 result adds a whole-loop control for 32-byte versioned rows. [Phase isolation](merge-phases.md) · [V1 scoped results](scoped-builder.md) · [Stock builder](stock-builder.md)

1. **Use the measured whole-loop v3 candidate as a control.** A validated-plan emitter puts fewer decisions in C. Include plan construction and validation in its full-pipeline time. For a standard Lean integration, establish the visibility and byte contract for each retained row and the exact initialized length. [Scoped v3 control](../../lean/runtime-experiment/scoped-compaction.c)
2. **Compare smaller toolchain changes.** The guarded copy in `fixed-copy.h` is a starting point for a runtime fast path in a local Lean build. A compiler lowering can inline known-width appends and use machine-sized offsets. Measure the remaining per-append guards and calls before attempting to hoist exclusivity and capacity checks across the loop. A standard scoped builder could provide those guarantees by construction. Its lowering still needs to fill the destination without repeated generic copies. [Fixed-width sweep and implementation](fixed-copy.md) · [Copy fast path](../../lean/runtime-experiment/fixed-copy.h)
3. **Establish the byte and snapshot contract before timing.** Compare complete output bytes against stock Lean and the independent oracle, including empty inputs, equal key-and-sequence ties, tombstones, and snapshots at the floor. Check capacity, offset arithmetic, and the exact initialized length. For a generic copy specialization, exercise shared and aliased buffers, unaligned offsets, clipping, and growth. The Lean theorems `compactSpans_eq_encode` and `compact_scan_eq` specify the behavior. Native implementations carry their own memory-safety and refinement obligations. [Lean reference proofs](../../lean/Alvoki/Storage/Proofs/Table/Compaction.lean) · [Fixture oracle](../../benchmarks/compaction.py)
4. **Decide from matched pipelines.** Run stock row and span compaction, fixed-copy, the new candidate, and matched Rust on the same inputs and pinned toolchains. Record materialization separately and compare the best complete pipeline including output parse and scan. Keep the raw trials and generated code. Use the synthetic profiles for repeatability, then check real flush and compaction traces when the packed table produces them. [Reproduction environment](../../benchmarks/followups/environment.txt) · [Raw v3 trials](../../benchmarks/followups/compaction-trials.csv)

## Reproduce

```sh
bash scripts/check.sh
bash scripts/check.sh --runtime
bash scripts/compaction.sh --fixed-copy --out /tmp/alvoki-compaction.csv
bash scripts/scoped-compaction.sh --pipeline-rows --alternating --out /tmp/alvoki-scoped-v3.csv
python3 benchmarks/compaction.py --summarize /tmp/alvoki-compaction.csv
```

[Environment and build commands](../../benchmarks/followups/environment.txt) · [Version-1 regressions and proof results](fast-path-refinement.md)
