# Storage engine roadmap

Alvoki is a pre-release sequential key-value engine. The Lean `DiskTable` API supports writes and deletes, snapshot lookup and range reads, WAL rotation, checkpoint publication, reopen and explicit maintenance. The packed table and shared recovery schedules have Lean proofs, with native fault fixtures for the Linux adapter. [Engine architecture](architecture.md#sequential-storage) · [Verification status](verification-status.md#storage-engine-guarantees)

## Next milestones

1. **Connect native execution to the crash proof.** The mixed segmented trace already carries one installed writer into the next session. Derive its file reads, namespace changes, descriptor identity and lock reports from the native adapter under a small, explicit Linux contract. The public guarantee is that acknowledged writes survive admitted crashes in order and `DiskTable.open` installs the exact table selected by the surviving checkpoint and WAL. [Disk proof obligations](proof-roadmap.md#disk-guarantees-to-prove)
2. **Prove recovery progress and bound recovery work.** Show that after failures stop, a healthy reopen of a reachable state succeeds and remains recoverable through later crashes. A request-count bound already covers the cached marked worker. Bound directory enumeration, manifest acquisition, sorting, validation and replay separately, along with allocation under the resource contract. [Recovery guarantees](proof-roadmap.md#end-to-end-storage-guarantees)
3. **Complete reclamation.** `collectObsoleteRuns`, `collectCoveredWal` and `retainRunVersions` already provide explicit maintenance. Finish the native identity and crash refinement of these paths. Prove eventual reclamation and space bounds for old run generations, covered WAL and obsolete row versions. The WAL payload bound after a healthy complete collection requires a segment-width cap. A retained-space guarantee also needs a rotation policy and bounds for physical allocation and unlinked files still held open. [Garbage collection contract](proof-roadmap.md#garbage-collection-contract)
4. **Extend the database interface.** Grow the `UInt64` key and value interface as requirements become concrete. Design atomic batches and request retry semantics. Specify isolation before adding concurrent transactions, and use the same publication contract for backups. [End-to-end storage guarantees](proof-roadmap.md#end-to-end-storage-guarantees)
5. **Explore additional storage modes.** Study object storage and reactive materialization once the sequential local engine supports repeatable correctness and performance experiments.

During pre-release development, keep one active encoding per artifact. Remove superseded compatibility paths as their proof dependencies are replaced. Review executable entry points, proof assumptions, fault coverage and native performance at each milestone. [Formats](specifications.md#wal-and-checkpoint-manifest) · [Progress](progress.md)

## Release performance

Record release-to-release microbenchmarks for codecs, merge and replay, and larger workloads for the public engine under sustained writes, mixed reads and writes, checkpoints, compaction, reopen and pinned snapshots. Measure throughput, latency percentiles, peak memory, retained bytes and write amplification separately. Separate sync time from replay time. Evaluate durable batches to amortize sync costs while preserving acknowledgement ordering. [Benchmarks](benchmarks.md) · [WAL sync measurements](benchmarks.md#wal-sync-on-successful-reopen)

Use YCSB workload mixes as starting points for comparisons with RocksDB and Fjall. Match key and value sizes, durability, dataset, workload and hardware where the APIs permit it. Record any differences and run the matching proof and fault checks when changing the native path. [YCSB](https://github.com/brianfrankcooper/YCSB) · [RocksDB](https://github.com/facebook/rocksdb) · [Fjall](https://github.com/fjall-rs/fjall)

## Repository review follow-ups

| Work | Completion check |
|---|---|
| Segmented startup performance | Compare paired peak RSS and elapsed time for aligned and repair workloads. Before adopting a per-segment replay fold, prove it preserves file-read and span diagnostics as well as decoder output, replay and the exact keeper passed to repair. [Resource measurements](../benchmarks/results/disk/bounded-keeper-replay) · [Per-segment experiment](../benchmarks/results/disk/segmented-replay-lifetimes) · [Serial replay proof](../lean/Alvoki/Storage/Disk/WalSegmentSerialReplay.lean) |
| Checkpoint proof cleanup | Share the strict checkpoint read witness and exact manifest publication model so the old raw proof branches can be retired. Preserve the strict v2 guarantees and rejection fixtures. [Checkpoint lineage](../lean/Alvoki/Storage/Disk/VersionedCheckpointLineage.lean) · [Publication model](../lean/Alvoki/Storage/Publication/CheckpointPublicationModel.lean) |
| Native fixture organization | Group segmented WAL scenarios and share filesystem setup. Preserve the ordered read plan, independent format oracles, sparse prune, append preflight, lock, sync and process-death cases. [Disk fixtures](../lean/Alvoki/Checks/DiskTableChecks.lean) · [Process-death fixtures](../scripts/check-disk-process-death.py) |
