# Disk storage

[DiskTable.lean](DiskTable.lean) implements the sequential disk API. Adjacent modules provide paths, checkpoint and WAL formats, native I/O, and recovery. [Proofs](Proofs/README.md) groups proof and observation modules by topic; some executable modules retain their local contracts and proofs.

The [proof architecture](../../../../docs/proof-architecture.md) and [native storage invariant map](../../../../docs/proofs/native-storage.md) describe the refinement boundaries and remaining assumptions.

To follow a durable write, read the [write and acknowledgement sequence](../../../../docs/architecture.md#sequential-storage). For a maintenance operation, start at [WAL collection](WAL/README.md). For the value visible after open, follow a [snapshot read](../Table/README.md). Run the native examples and checks with the [getting-started guide](../../../../docs/getting-started.md).

## Follow the segmented WAL

| Operation | Entry into the implementation |
|---|---|
| Initialize, append, rotate | [Empty bootstrap](WalSegmentBootstrapIO.lean), [commit a write](WalSegmentCommit.lean), [install the next segment](WalSegmentRotationIO.lean) |
| Discover and replay | [Cached extent discovery and reads](WAL/WalSegmentCachedExtentOpen.lean), [segment read I/O](WAL/WalSegmentReadIO.lean), [replay](WAL/WalSegmentReplay.lean); [inventory](WAL/WalSegmentInventory.lean) and [read plan](WAL/WalSegmentReadPlan.lean) describe the corresponding model and proofs |
| Repair on reopen | [Repair I/O](WalSegmentRepairIO.lean), [open and repair](WalSegmentRepairOpen.lean) |
| Decide which segments to collect | [WAL collection](WAL/README.md). This subdirectory owns the collection plan and range checks. The old collection module names at this level forward existing imports. |
