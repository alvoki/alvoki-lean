# Disk storage

[DiskTable.lean](DiskTable.lean) implements the sequential disk API. Adjacent modules provide paths, checkpoint and WAL formats, native I/O, and recovery. [Proofs](Proofs/README.md) groups proof and observation modules by topic; some executable modules retain their local contracts and proofs.

The [proof architecture](../../../../docs/proof-architecture.md) and [native storage invariant map](../../../../docs/proofs/native-storage.md) describe the refinement boundaries and remaining assumptions.

To follow a durable write, read the [write and acknowledgement sequence](../../../../docs/architecture.md#sequential-storage). For a maintenance operation, start at [WAL collection](WAL/README.md). For the value visible after open, follow a [snapshot read](../Table/README.md). Run the native examples and checks with the [getting-started guide](../../../../docs/getting-started.md).
