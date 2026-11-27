# Benchmarks

These measurements are research results, not throughput guarantees. Compare runs only when workloads, durability protocol, compiler settings and hardware match. The [current end-to-end baseline](performance-baseline.md) describes the native engine workloads; the historical reports preserve the original numbers, commands, raw data and limitations.

## Packed storage experiments

The reports give workload definitions, release commands, raw trials, and proof scope. Compare each result with controls from its original run.

| Workload | Reports |
|---|---|
| Point lookup, scans, layout and scalar records | [Optimization results](../experiments/optimizations.md) · [Native SIMD](../experiments/native-experiments.md) · [Packed ownership](../experiments/packed-experiments.md) |
| Merge, replay and packed transforms | [Emission and updates](../experiments/emission-experiments.md) · [Selection and replay phases](../experiments/merge-phases.md) · [Fused emission and direct scans](../experiments/fused-merge.md) · [Proved fast paths](../experiments/fast-path-refinement.md) |
| Output builders and toolchain changes | [Fixed-width copy](../experiments/fixed-copy.md) · [Stock builder](../experiments/stock-builder.md) · [Scoped runtime experiment](../experiments/scoped-builder.md) · [Wide-accessor ablation](../../benchmarks/results/packed/wide-accessors) |
| Versioned compaction and materialization | [V3 compaction](../experiments/compaction.md) · [Stock cursor](../../benchmarks/results/packed/stock-v3-cursor) · [Whole-loop writer comparison](../../benchmarks/results/packed/v3-writer-comparison) |

### Method

The packed experiments use deterministic inputs, pinned CPU affinity, release builds and retained trials after warmup. Workload scope and comparisons vary by experiment. The [original VM method](packed-benchmarks.md#method) records the environment, timed boundaries and unmeasured costs; [later packed reports](../experiments/optimizations.md) use their own controls.

| Historical packed result | Details |
|---|---|
| <a id="first-vm-measurements"></a><a id="one-million-records"></a>First VM measurements | [One-million-record table and raw data](packed-benchmarks.md#one-million-records) |
| <a id="code-generation-findings"></a>Code generation | [Generated code findings](packed-benchmarks.md#code-generation-findings) |
| <a id="code-size-and-tool-timings"></a>Code and verification costs | [Code size and tool timings](packed-benchmarks.md#code-size-and-tool-timings) |
| <a id="review-follow-up-measurements"></a><a id="stock-lean-comparison"></a><a id="matched-rust-span-control"></a><a id="reproduce-the-measured-revisions"></a>Review follow-up | [Paired Lean measurements, Rust control and reproduction](packed-benchmarks.md#review-follow-up-measurements) |

## Disk replay

The native replay benchmark times `DiskTable.open` on independently generated segmented WAL fixtures. Timed work includes validation, replay and the required durability operations; fixture generation, process startup, result validation and close are outside the timer. Its warmup makes this a warm-cache measurement. For a current paired protocol and broader engine workloads, see the [performance baseline](performance-baseline.md).

```sh
bash scripts/disk-replay.sh --out /tmp/alvoki-replay-before.csv
bash scripts/disk-replay.sh --out /tmp/alvoki-replay-after.csv \
  --baseline /tmp/alvoki-replay-before.csv --max-slowdown 1.25
```

The original list-memtable replay was strongly order-sensitive; a later tree-memtable comparison reduced the 20,000-record ascending median from 1,352.29 ms to 7.90 ms on the same VM. These are historical measurements, not current service-level targets. [Replay method, original baseline and tree comparison](disk-benchmarks.md#disk-replay)

| Historical disk topic | Details and reproduction |
|---|---|
| <a id="verified-tree-memtable"></a>Tree memtable | [Replay comparison](disk-benchmarks.md#verified-tree-memtable) |
| <a id="native-segmented-wal"></a><a id="wal-reopen-memory-and-bytes-read"></a>Segmented WAL | [Reopen timings, memory and bytes read](disk-benchmarks.md#native-segmented-wal) |
| <a id="canonical-database-path-at-open"></a><a id="wal-sync-on-successful-reopen"></a><a id="torn-wal-repair"></a><a id="durable-wal-boundary"></a>Open and durability | [Path, sync, tail repair and marker measurements](disk-benchmarks.md#canonical-database-path-at-open) |
| <a id="shared-checkpoint-publication-schedule"></a><a id="shared-reopen-durability-branch"></a><a id="shared-checkpoint-preparation"></a><a id="typed-disk-write-outcomes"></a><a id="shared-marked-open"></a><a id="shared-publication-file-and-sync-targets"></a>Shared protocol operations | [Checkpoint, reopen and write-outcome comparisons](disk-benchmarks.md#shared-checkpoint-publication-schedule) |
| <a id="selected-wal-frame-ordinals"></a><a id="disk-snapshot-session-identity"></a>Read guards | [Ordinal and snapshot identity measurements](disk-benchmarks.md#selected-wal-frame-ordinals) |
| <a id="wal-sync-process-overhead"></a><a id="native-descriptor-sync"></a><a id="exclusive-staging-creation"></a><a id="lean-readability-review"></a>Sync and staging | [Process overhead, descriptor sync and staging reports](disk-benchmarks.md#wal-sync-process-overhead) |
