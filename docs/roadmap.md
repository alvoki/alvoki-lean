# Roadmap

The stock correctness command, validated v1 run API, standalone byte proofs, and shared refinement model for the per-record merge and branching direct scan are in place. [Architecture](architecture.md) · [Verification status](verification-status.md)

The v1 round trips, the adaptive and bounded-window emitter refinements, and checked streaming replay are complete. Versioned workload proxies now exercise compaction and snapshot visibility and compare a fixed-width copy candidate against the stock builder. [Fast-path refinement](fast-path-refinement.md) · [Compaction experiment](compaction.md)

The [proof roadmap](proof-roadmap.md) records the completed codec and snapshot preservation theorems and the outstanding engine refinements.

The sequential multi-run engine now includes packed v3 reads, writes, flush, compaction, a WAL, checkpoint publication, and reopen. Differential traces cover the packed table and filesystem fixtures exercise recovery. [Sequential storage](architecture.md#sequential-storage)

The long-term proof target is end-to-end refinement of the storage engine across crashes. It includes recovery progress, maintenance and reclamation, atomic batches and retries, resource bounds, and backup and format migration. [End-to-end storage guarantees](proof-roadmap.md#end-to-end-storage-guarantees)

1. Complete the native primitive and live-session contracts for the locked mixed recovery proof. [Disk proof obligations](proof-roadmap.md#disk-guarantees-to-prove)
2. Extend opt-in native collection beyond strictly older run generations. Add covered WAL segment and obsolete version collection. Measure retained space, replay work, and foreground latency during sustained collection. [Garbage collection contract](proof-roadmap.md#garbage-collection-contract)
3. Use the native replay baseline when changing the memtable or WAL protocol. Extend engine measurements to report sync time separately from replay so startup cost stays visible. Measure compaction and checkpoint write amplification. [Performance requirements](proof-roadmap.md#performance-requirements-for-verified-paths) · [WAL sync measurements](benchmarks.md#wal-sync-on-successful-reopen)
4. Evaluate MVCC, concurrency, and transaction semantics after a sequential LSM model stabilizes.
5. Study object storage and reactive materialization once the local engine supports repeatable correctness and performance experiments.

Review each milestone before starting its successor. Check the executable entry points, theorem assumptions, fault fixtures, and native timings. During larger milestones, review at natural checkpoints. Record confirmed issues and new obligations here or in the proof roadmap, with dependencies and clear completion criteria.

For single-write latency, evaluate a persistent sync-only helper against the current adapter and its failure fixtures. Preserve acknowledgement ordering, keep rename under the database lock, and measure the supported native path. Evaluate durable batches to amortize the remaining sync costs. [WAL sync process experiment](benchmarks.md#wal-sync-process-overhead)

## Repository review follow-ups

The 24 November 2026 review covered the source, proof and fixture paths, the benchmark drivers and all 21 documents at `ddf033b`.

| Priority | Work | Completion check |
|---|---|---|
| Before segmented activation | Select one WAL layout under the lock and use the same Linux file primitives from the adapter and fault fixtures. Guard reserved run and staging paths before reading or truncating them. [Disk adapter](../lean/Alvoki/Storage/Disk/DiskTable.lean) · [Segmented worker](../lean/Alvoki/Storage/Disk/WalSegmentRepairOpen.lean) | Ambiguous layouts fail before mutation. Replacement stages are fresh regular files created exclusively, including on retry. Native tests exercise the public adapter through bootstrap, rotation, a cut, reopen and the next append. |
| Before activating WAL collection | Use the same strict v2 run availability and coverage that the exact retry proof uses. [Effectful retry](../lean/Alvoki/Storage/Disk/WalSegmentRetryReadEffects.lean) · [Collection model](../lean/Alvoki/Storage/Disk/WalSegmentCollection.lean) | A collector cannot delete on the strength of a legacy or unverified checkpoint. |
| Before making segmentation the default | Measure the startup cost of the native segmented route. The reader currently reads the whole keeper before checking the selected span, and an aligned reopen can issue three sync callbacks. [Segment reader](../lean/Alvoki/Storage/Disk/WalSegmentReadIO.lean) · [Repair dispatcher](../lean/Alvoki/Storage/Disk/WalSegmentRepairIO.lean) | Compare aligned and repair time, bytes read, peak memory and sync counts against the repaired baseline with varied segment counts. If optimizing the aligned branch, retain the directory barrier and check partial sync effects. |
| Parallel proof cleanup | Reuse a strict-only checkpoint read witness and make the shared publication model take the actual manifest bytes. These changes make it possible to remove the remaining raw v1 proof branches. Reuse the strict lock/read reports and give frequently used snapshot facts names. [Checkpoint lineage](../lean/Alvoki/Storage/Disk/VersionedCheckpointLineage.lean) · [Publication model](../lean/Alvoki/Storage/Publication/CheckpointPublicationModel.lean) · [Strict trace](../lean/Alvoki/Storage/Disk/IntegrityDatabaseTrace.lean) | Keep the exact strict v2 guarantees and native rejection fixtures. Move related modules together with qualified imports when this exposes a simpler dependency graph. |
| Parallel check cleanup | Start by separating the segmented WAL fixtures from the other disk scenarios. Share native file operations and keep expectations and independent format oracles in the tests. [Disk fixtures](../lean/Alvoki/Checks/DiskTableChecks.lean) | The same fixture entry point runs all cases. The segmented fixture checks the ordered required reads and rejects payload reads from segment files outside the plan. |
