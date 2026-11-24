# Roadmap

The stock correctness command, validated v1 run API, standalone byte proofs, and shared refinement model for the per-record merge and branching direct scan are in place. [Architecture](architecture.md) · [Verification status](verification-status.md)

The v1 round trips, the adaptive and bounded-window emitter refinements, and checked streaming replay are complete. Versioned workload proxies now exercise compaction and snapshot visibility and compare a fixed-width copy candidate against the stock builder. [Fast-path refinement](fast-path-refinement.md) · [Compaction experiment](compaction.md)

The [proof roadmap](proof-roadmap.md) records the completed codec and snapshot preservation theorems and the outstanding engine refinements.

The sequential multi-run engine now includes packed v3 reads, writes, flush, compaction, a WAL, checkpoint publication, and reopen. Differential traces cover the packed table and filesystem fixtures exercise recovery. [Sequential storage](architecture.md#sequential-storage)

The long-term proof target is end-to-end refinement of the storage engine across crashes. It includes recovery progress, maintenance and reclamation, atomic batches and retries, resource bounds, and backup. While the engine is pre-release, adopt one active encoding per artifact and remove obsolete compatibility paths as their proof dependencies are replaced. [End-to-end storage guarantees](proof-roadmap.md#end-to-end-storage-guarantees)

1. Complete the native primitive and live-session contracts for the locked mixed recovery proof. [Disk proof obligations](proof-roadmap.md#disk-guarantees-to-prove)
2. Extend opt-in native collection beyond strictly older run generations. Add covered WAL segment and obsolete version collection. Measure retained space, replay work, and foreground latency during sustained collection. [Garbage collection contract](proof-roadmap.md#garbage-collection-contract)
3. Prove conditional recovery progress and bound the work by the retained checkpoint, required WAL and repair actions. Keep using the native replay baseline for changes to this path. [Performance requirements](proof-roadmap.md#performance-requirements-for-verified-paths) · [WAL sync measurements](benchmarks.md#wal-sync-on-successful-reopen)
4. Extend the current unsigned 64-bit key and value API as product requirements become concrete. Evaluate concurrency and transaction semantics after the sequential LSM model stabilizes.
5. Study object storage and reactive materialization once the local engine supports repeatable correctness and performance experiments.

Review each milestone before starting its successor. Check the executable entry points, theorem assumptions, fault fixtures, and native timings. During larger milestones, review at natural checkpoints. Record confirmed issues and new obligations here or in the proof roadmap, with dependencies and clear completion criteria.

The Linux adapter now calls `fsync` on open descriptors. Evaluate durable batches to amortize the remaining sync costs while preserving acknowledgement ordering and the database lock around publication. [WAL sync process experiment](benchmarks.md#wal-sync-process-overhead)

## Release performance

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

## Repository review follow-ups

The 24 November 2026 review covered the source, proof and fixture paths, the benchmark drivers and all 21 documents at `ddf033b`. The segmented follow-up reviewed `a8a32a6..9ec816c`.

| Priority | Work | Completion check |
|---|---|---|
| Segmented protocol refinement | Compose the native bootstrap, append, rotation, checkpoint and reopen schedules in a single mixed trace. Connect lock and descriptor observations to it. [Disk proof obligations](proof-roadmap.md#disk-guarantees-to-prove) | Every confirmed write survives an admitted crash. A healthy public reopen installs the exact recovered table and active segment and is ready for the next append. |
| Before activating WAL collection | Derive exact durable run availability for every crash-selectable checkpoint and marker pair. The segment eligibility model already uses the strict v2 decoder. [Effectful retry](../lean/Alvoki/Storage/Disk/WalSegmentRetryReadEffects.lean) · [Collection model](../lean/Alvoki/Storage/Disk/WalSegmentCollection.lean) | A collector cannot delete on the strength of a legacy or unverified checkpoint. |
| Medium · Segmented startup performance | Bounded keeper reads remove the large-tail read and allocation cost. The per-segment prototype reduces peak memory for many required segments. Lean proves exact decoder and replay equality for checked aligned spans and an exact keeper prefix. [Resource measurements](../benchmarks/results/disk/bounded-keeper-replay) · [Per-segment experiment](../benchmarks/results/disk/segmented-replay-lifetimes) · [Serial replay proof](../lean/Alvoki/Storage/Disk/WalSegmentSerialReplay.lean) | Prove that the ordered I/O fold preserves raw read errors and global span diagnostics ahead of decoder and replay errors. It must pass the exact keeper and physical size to the current repair worker. Compare paired peak RSS and elapsed time on native aligned and repair workloads before adoption. |
| Parallel proof cleanup | Reuse a strict-only checkpoint read witness and make the shared publication model take the actual manifest bytes. These changes make it possible to remove the remaining raw v1 proof branches. Reuse the strict lock/read reports and give frequently used snapshot facts names. [Checkpoint lineage](../lean/Alvoki/Storage/Disk/VersionedCheckpointLineage.lean) · [Publication model](../lean/Alvoki/Storage/Publication/CheckpointPublicationModel.lean) · [Strict trace](../lean/Alvoki/Storage/Disk/IntegrityDatabaseTrace.lean) | Keep the exact strict v2 guarantees and native rejection fixtures. Move related modules together with qualified imports when this exposes a simpler dependency graph. |
| Medium · Native fixture organization | Separate the segmented WAL fixtures from other disk scenarios and share native file operations. [Disk fixtures](../lean/Alvoki/Checks/DiskTableChecks.lean) · [Process-death fixtures](../scripts/check-disk-process-death.py) | The same fixture entry point checks the ordered read plan and independent format oracles. Preserve the public sparse-prune, append preflight, lock-file, directory-sync and process-death cases. |
