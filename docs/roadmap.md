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
| Segmented protocol refinement | Compose the native bootstrap, append, rotation, checkpoint and reopen schedules in a single mixed trace. Connect lock and descriptor observations to it. [Disk proof obligations](proof-roadmap.md#disk-guarantees-to-prove) | Every confirmed write survives an admitted crash. A healthy public reopen installs the exact recovered table and active segment and is ready for the next append. |
| Before activating WAL collection | Derive exact durable run availability for every crash-selectable checkpoint and marker pair. The segment eligibility model already uses the strict v2 decoder. [Effectful retry](../lean/Alvoki/Storage/Disk/WalSegmentRetryReadEffects.lean) · [Collection model](../lean/Alvoki/Storage/Disk/WalSegmentCollection.lean) | A collector cannot delete on the strength of a legacy or unverified checkpoint. |
| Segmented startup performance | Measure and reduce the cost of native reopen. Aligned reopen uses separate directory and keeper barriers. The reader also reads whole keeper payloads before checking their required span. [Segment reader](../lean/Alvoki/Storage/Disk/WalSegmentReadIO.lean) · [Aligned route](../lean/Alvoki/Storage/Disk/WalSegmentOpenFast.lean) | Use matched aligned and repair workloads at varied segment counts. Preserve the effect contract for failure at either durability barrier. |
| Parallel proof cleanup | Reuse a strict-only checkpoint read witness and make the shared publication model take the actual manifest bytes. These changes make it possible to remove the remaining raw v1 proof branches. Reuse the strict lock/read reports and give frequently used snapshot facts names. [Checkpoint lineage](../lean/Alvoki/Storage/Disk/VersionedCheckpointLineage.lean) · [Publication model](../lean/Alvoki/Storage/Publication/CheckpointPublicationModel.lean) · [Strict trace](../lean/Alvoki/Storage/Disk/IntegrityDatabaseTrace.lean) | Keep the exact strict v2 guarantees and native rejection fixtures. Move related modules together with qualified imports when this exposes a simpler dependency graph. |
| Parallel check cleanup | Start by separating the segmented WAL fixtures from the other disk scenarios. Share native file operations and keep expectations and independent format oracles in the tests. [Disk fixtures](../lean/Alvoki/Checks/DiskTableChecks.lean) | The same fixture entry point runs all cases. The segmented fixture checks the ordered required reads and rejects payload reads from segment files outside the plan. |
