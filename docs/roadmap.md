# Roadmap

The stock correctness command, validated v1 run API, standalone byte proofs, and shared refinement model for the per-record merge and branching direct scan are in place. [Architecture](architecture.md) · [Verification status](verification-status.md)

The v1 round trips, the adaptive and bounded-window emitter refinements, and checked streaming replay are complete. Versioned workload proxies now exercise compaction and snapshot visibility and compare a fixed-width copy candidate against the stock builder. [Fast-path refinement](fast-path-refinement.md) · [Compaction experiment](compaction.md)

The [proof roadmap](proof-roadmap.md) records the completed codec and snapshot preservation theorems and the outstanding engine refinements.

The sequential multi-run engine now includes packed v3 reads, writes, flush, compaction, a WAL, checkpoint publication, and reopen. Differential traces cover the packed table and filesystem fixtures exercise recovery. [Sequential storage](architecture.md#sequential-storage)

The long-term proof target is end-to-end refinement of the storage engine across crashes. It includes recovery progress, maintenance and reclamation, atomic batches and retries, resource bounds, and backup and format migration. [End-to-end storage guarantees](proof-roadmap.md#end-to-end-storage-guarantees)

1. Complete the native primitive and live-session contracts for the locked mixed recovery proof. Compose uncertain-write recovery with the versioned writer invariant. [Disk proof obligations](proof-roadmap.md#disk-guarantees-to-prove)
2. Extend opt-in native collection beyond strictly older run generations. Add covered WAL segment and obsolete version collection. Measure retained space, replay work, and foreground latency during sustained collection. [Garbage collection contract](proof-roadmap.md#garbage-collection-contract)
3. Use the native replay baseline when changing the memtable or WAL protocol. Extend engine measurements to report sync time separately from replay so startup cost stays visible. Measure compaction and checkpoint write amplification. [Performance requirements](proof-roadmap.md#performance-requirements-for-verified-paths) · [WAL sync measurements](benchmarks.md#wal-sync-on-successful-reopen)
4. Evaluate MVCC, concurrency, and transaction semantics after a sequential LSM model stabilizes.
5. Study object storage and reactive materialization once the local engine supports repeatable correctness and performance experiments.

Review each milestone before starting its successor. Check the executable entry points, theorem assumptions, fault fixtures, and native timings. During larger milestones, review at natural checkpoints. Record confirmed issues and new obligations here or in the proof roadmap, with dependencies and clear completion criteria.

For single-write latency, evaluate a persistent sync-only helper against the current adapter and its failure fixtures. Preserve acknowledgement ordering, keep rename under the database lock, and measure the supported native path. Evaluate durable batches to amortize the remaining sync costs. [WAL sync process experiment](benchmarks.md#wal-sync-process-overhead)
