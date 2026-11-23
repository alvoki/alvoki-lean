# Roadmap

The stock correctness command, validated v1 run API, standalone byte proofs, and shared refinement model for the per-record merge and branching direct scan are in place. [Architecture](architecture.md) · [Verification status](verification-status.md)

The v1 round trips, the adaptive and bounded-window emitter refinements, and checked streaming replay are complete. Versioned workload proxies now exercise compaction and snapshot visibility and compare a fixed-width copy candidate against the stock builder. [Fast-path refinement](fast-path-refinement.md) · [Compaction experiment](compaction.md)

The [proof roadmap](proof-roadmap.md) records the completed codec and snapshot preservation theorems and the outstanding engine refinements.

The sequential multi-run engine now includes packed v3 reads, writes, flush, compaction, a WAL, checkpoint publication, and reopen. Differential traces cover the packed table and filesystem fixtures exercise recovery. [Sequential storage](architecture.md#sequential-storage)

The long-term proof target is end-to-end refinement of the storage engine across crashes. It includes recovery progress, maintenance and reclamation, atomic batches and retries, resource bounds, and backup and format migration. [End-to-end storage guarantees](proof-roadmap.md#end-to-end-storage-guarantees)

1. Model the durable outcomes of each publication step and prove acknowledgement durability across repeated crashes. The disk directory is now resolved and fixed at open. Add run payload integrity checks and enforce snapshot session isolation. [Disk proof obligations](proof-roadmap.md#disk-guarantees-to-prove)
2. Implement and prove garbage collection for old run generations, covered WAL segments, and obsolete versions. Measure retained space, replay work, and foreground latency during collection. [Garbage collection contract](proof-roadmap.md#garbage-collection-contract)
3. Use the native replay baseline when changing the memtable or WAL protocol. Extend engine measurements to report sync time separately from replay so startup cost stays visible. Measure compaction and checkpoint write amplification. [Performance requirements](proof-roadmap.md#performance-requirements-for-verified-paths) · [WAL sync measurements](benchmarks.md#wal-sync-on-successful-reopen)
4. Evaluate MVCC, concurrency, and transaction semantics after a sequential LSM model stabilizes.
5. Study object storage and reactive materialization once the local engine supports repeatable correctness and performance experiments.

Review each milestone before starting its successor. Check the executable entry points, theorem assumptions, fault fixtures, and native timings. During larger milestones, review at natural checkpoints. Record confirmed issues and new obligations here or in the proof roadmap, with dependencies and clear completion criteria.
