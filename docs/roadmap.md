# Storage engine roadmap

Alvoki is a pre-release sequential key-value engine. The Lean `DiskTable` API supports writes and deletes, snapshot lookup and range reads, WAL rotation, checkpoint publication, reopen and explicit maintenance. The packed table and shared recovery schedules have Lean proofs, with native fault fixtures for the Linux adapter. [Engine architecture](architecture.md#sequential-storage) · [Verification status](verification-status.md#storage-engine-guarantees)

## Next milestones

1. **Connect native execution to the crash proof.** The mixed segmented trace already carries one installed writer into the next session. Derive its file reads, namespace changes, descriptor identity and lock reports from the native adapter under a small, explicit Linux contract. The public guarantee is that acknowledged writes survive admitted crashes in order and `DiskTable.open` installs the exact table selected by the surviving checkpoint and WAL. [Disk proof obligations](proof-roadmap.md#disk-guarantees-to-prove)
2. **Prove recovery progress and bound recovery work.** Show that after failures stop, a healthy reopen of a reachable state succeeds and remains recoverable through later crashes. A request-count bound already covers the cached marked worker. Bound directory enumeration, manifest acquisition, sorting, validation and replay separately, along with allocation under the resource contract. [Recovery guarantees](proof-roadmap.md#end-to-end-storage-guarantees)
3. **Complete reclamation.** `collectObsoleteRuns`, `collectCoveredWal` and `retainRunVersions` already provide explicit maintenance. Finish the native identity and crash refinement of these paths. Prove eventual reclamation and space bounds for old run generations, covered WAL and obsolete row versions. The WAL payload bound after a healthy complete collection requires a segment-width cap. A retained-space guarantee also needs a rotation policy and bounds for physical allocation and unlinked files still held open. [Garbage collection contract](proof-roadmap.md#garbage-collection-contract)
4. **Extend the database interface.** Grow the `UInt64` key and value interface as requirements become concrete. Extend atomic batches with request retry semantics. Specify isolation before adding concurrent transactions, and use the same publication contract for backups. [End-to-end storage guarantees](proof-roadmap.md#end-to-end-storage-guarantees)
5. **Explore additional storage modes.** Study object storage and reactive materialization once the sequential local engine supports repeatable correctness and performance experiments.

During pre-release development, keep one active encoding per artifact. Remove superseded compatibility paths as their proof dependencies are replaced. Review executable entry points, proof assumptions, fault coverage and native performance at each milestone. [Formats](specifications.md#wal-and-checkpoint-manifest) · [Progress](progress.md)

## Release performance

The [first native baseline](performance-baseline.md) identifies durable write publication as the first bottleneck to investigate.

Make Alvoki a verified embedded LSM that is competitive with an established engine on sustained durable workloads with one foreground thread. Start with RocksDB. Fjall or another established engine is acceptable when it supports a simpler, like-for-like comparison. Pin the reference engine and version before collecting the baseline.

The initial target is at least 50% of the reference's durable throughput and at most twice its read and acknowledged-write p99 on the primary workload at a common offered load. Recovery work must be bounded by the selected checkpoint, required WAL suffix, and required repair actions. Check all three scenarios and record resource tradeoffs when judging whether the goal is met.

| Scenario | Starting workload | Measurements |
|---|---|---|
| Durable mixed load | Deterministic, YCSB-inspired 50/50 point reads and writes with 64-bit keys and values. Start with individually durable writes. Measure batches separately with matched size, acknowledgement and atomicity. | Sustained throughput and per-operation read and acknowledged-write p99 at a common load. |
| Maintenance and an old snapshot | Run the same mix through several maintenance cycles. Hold a snapshot across cycles, then release it. Exercise checkpoint, compaction and reclamation with equivalent maintenance pressure. | Foreground p99 during maintenance, physical and retained bytes per live byte, write amplification and time to reclaim space after release. |
| Crash reopen | Exercise aligned reopen and torn-tail repair. Vary required WAL suffix, segment count and bytes outside the selected range independently where the formats allow it. | Time to the first successful read, bytes read, peak RSS and sync time separate from replay. |

Use native release builds on the same Linux machine and storage. Match input, operation mix, durability and foreground thread count. Record background thread budgets, cache state, configuration, seeds, warm-ups, raw samples and differences the engines cannot match. Keep codec, merge, checkpoint and replay microbenchmarks for diagnosis and release comparisons.

1. Run the three baseline scenarios before choosing the first optimization.
2. Rank repeatable gaps by their impact on the primary workload. Split costs by phase and test a concrete explanation with a controlled experiment. Profile when phase timing and byte or syscall counts leave the gap unexplained.
3. Apply one focused change and rerun the same scenario against the same baseline. Independent hypotheses can be explored in parallel on isolated worktrees. Run decisive timed comparisons without concurrent benchmarks.
4. Verify the affected contracts, differential fixtures and crash cases. Record the commit, hypothesis, before-and-after samples, tradeoffs and next experiment. Add a scenario when it answers an open diagnostic question or guards against an observed regression.
5. Repeat while the target is unmet. When comparable, repeatable measurements satisfy the primary target and the recovery and correctness checks pass, record the final comparison and close the optimization loop.

[YCSB](https://github.com/brianfrankcooper/YCSB) · [RocksDB](https://github.com/facebook/rocksdb) · [Fjall](https://github.com/fjall-rs/fjall) · [Benchmark method](high-performance-lean.md#reproduce-before-generalizing) · [Proof and runtime performance requirements](proof-roadmap.md#performance-requirements-for-verified-paths)

### Map the engine before choosing the next optimization

Keep the three release scenarios as controls. The next priority is to measure
where else Alvoki spends time and I/O. Use the durable-write baseline to locate
publication costs, then sample read-heavy and read-only workloads, point hits
and misses, and short and long scans. Include a workload that spans several
checkpoints and compactions with a held snapshot. Vary working-set size and
access skew, and record when data fits in cache. Attribute latency to lookup,
replay, checkpoint, compaction, or reclamation where phase measurements allow.

Rank repeatable gaps by their cost in representative workloads. Record the
test configuration, performance and resource tradeoffs for each candidate.
A strategy can be worth keeping as an option when a workload or deployment has
a measurable advantage and its correctness contract is supported there.
Use a common offered load where possible and keep the three release scenarios
comparable across iterations.

### WAL strategies and storage contracts

Maintain a comparison of WAL strategies as evidence becomes available.
For each strategy, record its on-disk layout, sync order and count, acknowledged
durability, batch atomicity, treatment of incomplete writes and corruption,
recovery scan bounds, and performance on the measured storage stack. State
the assumptions about filesystem sync, directory persistence, write ordering,
torn writes, failure isolation and corruption detection. A deployment can
choose among independently validated strategies according to its storage
contract and measured workload costs.

Study the log formats and recovery paths of LevelDB, RocksDB, Pebble and
TigerBeetle at pinned revisions. Compare framing, fragmentation, checksums,
sequence and generation identifiers, sync and recycling, and the handling
of gaps and damaged tails. Include checkpoint and replication dependencies
when they change the meaning of a local log write or acknowledgement.
[LevelDB](https://github.com/google/leveldb/blob/main/doc/log_format.md) ·
[RocksDB](https://github.com/facebook/rocksdb/wiki/Write-Ahead-Log-File-Format) ·
[Pebble](https://github.com/cockroachdb/pebble/tree/master/record) ·
[TigerBeetle](https://github.com/tigerbeetle/tigerbeetle)

One candidate uses a single log with independently validated fixed-size
frames, starting with 4 KiB as an experimental format size. Give each frame
a checksum and block ordinal, plus a generation when recycling is in scope.
Include batch identifiers and fragment boundaries so recovery can tell whether
the entire batch is present. A later valid frame from the same generation can
expose a damaged interior frame. At the tail, where there may be no later
witness, define how recovery distinguishes an allowable incomplete append
from loss of acknowledged data. Frame size and alignment alone do not establish
atomic writes or independent physical failure units. A candidate with fewer
barriers must prove that its exact sync and storage contract still preserves
every acknowledged batch and admits only complete batches on recovery.

### Small durable writes

Matched batch sizes 1, 8 and 32 keep a per-commit gap. Alvoki syncs the WAL, staged marker and directory for each batch, while the RocksDB control syncs its WAL once per batch. Keep size 1 as a separate target and distinguish batching gains from reducing the number of barriers for that same submission.

Evaluate in-segment commit records as a candidate protocol. It could append the batch and its boundary together and sync the active file once, with directory barriers on segment creation or rotation. First specify crash cuts, including a visible commit record with missing or torn payload, incomplete final records, interrupted rotation and retries. Derive that every acknowledged batch survives, no strictly partial batch becomes visible, and previous acknowledged data survives rejected tails. Specify exact decoder and corruption assumptions. Compare a proof-backed candidate on the same small-batch cells and run the native fault suite before adoption. [Sampled sync counts](performance-baseline.md#durable-batch-experiment)

### Striped reusable WAL experiment

Prototype a markerless WAL that assigns each commit ordinal to one of a fixed
set of reusable segments, starting with eight and a single writer. Give each
record a generation, ordinal, batch boundary and checksum. Reopen would merge
the validated segment streams from the checkpoint and select the longest
contiguous sequence of complete batches. Neighboring segments can expose a
hole or stale generation. Establish what recovery may infer at the global
tail, where no later record may witness a missing write.

Compare one ordered sync per commit in this prototype against the two-slot
marker path. Before adoption, model interrupted overwrite, rotation, and
recycling, and prove that the recoverable prefix includes every acknowledged
batch and excludes partial batches. Recycling must preserve the only copy of
each required record until the durable checkpoint covers it. Define the
failure isolation and checksum assumptions. Measure steady-state writes,
sync and physical write counts, and reopen work over different stripe counts,
batch sizes, and checkpoint distances.

### Workload coverage and toolchain experiments

Use the baseline as the starting point for a performance map of Alvoki. Keep the three core scenarios stable for release comparisons. Add representative points as a use case or bottleneck calls for them. Vary read/write mix, uniform versus Zipfian access, working-set size, key and value size, batch size, snapshot lifetime, cache state and maintenance pressure. When diagnosing a difference, vary one dimension at a time. Retain an established-engine control where semantics match, and keep Alvoki's absolute timings and resource use for cases with a different contract.

Profile the native engine before choosing a toolchain change. When the evidence points to a compiler or runtime limitation, compare the latest released Lean with the same revision plus one pinned patch, using identical Alvoki source, flags, inputs and release builds. Include the best available source-level alternative and inspect generated code to explain the difference. For a patch that introduces a new primitive, measure adoption separately from the toolchain upgrade. Use both the affected kernel and the end-to-end workload. Adopt a patched toolchain only when the end-to-end gain is material and the available stock-Lean alternative cannot capture it. Record patch provenance, correctness and proof checks, support cost and a route back to an upstream release. [Existing Lean experiments](high-performance-lean.md#reproduce-before-generalizing)

## Repository review follow-ups

| Work | Completion check |
|---|---|
| Segmented startup performance | Compare paired peak RSS and elapsed time for aligned and repair workloads. Before adopting a per-segment replay fold, prove it preserves file-read and span diagnostics as well as decoder output, replay and the exact keeper passed to repair. [Resource measurements](../benchmarks/results/disk/bounded-keeper-replay) · [Per-segment experiment](../benchmarks/results/disk/segmented-replay-lifetimes) · [Serial replay proof](../lean/Alvoki/Storage/Disk/Proofs/WAL/WalSegmentSerialReplay.lean) |
| Checkpoint proof cleanup | Share the strict checkpoint read witness and exact manifest publication model so the old raw proof branches can be retired. Preserve the strict v2 guarantees and rejection fixtures. [Checkpoint lineage](../lean/Alvoki/Storage/Disk/VersionedCheckpointLineage.lean) · [Publication model](../lean/Alvoki/Storage/Publication/CheckpointPublicationModel.lean) |
| Native fixture organization | Group segmented WAL scenarios and share filesystem setup. Preserve the ordered read plan, independent format oracles, sparse prune, append preflight, lock, sync and process-death cases. [Disk fixtures](../lean/Alvoki/Checks/DiskTableChecks.lean) · [Process-death fixtures](../scripts/check-disk-process-death.py) |
