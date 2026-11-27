# Disk storage

[DiskTable.lean](DiskTable.lean) implements the sequential disk API. Adjacent modules provide paths, checkpoint and WAL formats, native I/O, and recovery. [Proofs](Proofs/README.md) groups proof and observation modules by topic; some executable modules retain their local contracts and proofs.

The [proof architecture](../../../../docs/proof-architecture.md) and [native storage invariant map](../../../../docs/proofs/native-storage.md) describe the refinement boundaries and remaining assumptions.
