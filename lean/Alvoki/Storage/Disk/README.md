# Disk storage

[DiskTable.lean](DiskTable.lean) implements the sequential disk API: opening a directory, reading and writing, checkpointing, and explicit maintenance. It connects the in-memory [table](../Table/README.md) to the segmented write-ahead log (WAL), checkpoint files and native filesystem operations.

A write prepares the next table state, appends a WAL frame and publishes a durable boundary before acknowledging success. On open, the engine reads the checkpoint and recovers the selected WAL history before installing a table. Follow the [WAL lifecycle](WAL/README.md) for publication, rotation, recovery and collection; the [sequential storage overview](../../../../docs/architecture.md#sequential-storage) puts these operations together.

For other entry points:

- [DiskPaths.lean](DiskPaths.lean) identifies files in a database directory; [DiskSession.lean](DiskSession.lean) describes session operations and their state.
- [Manifest.lean](Manifest.lean) describes a checkpoint manifest. [CheckpointRead.lean](CheckpointRead.lean) and [IntegrityCheckpointRead.lean](IntegrityCheckpointRead.lean) handle checkpoint reads; [Recovery.lean](Recovery.lean) connects recovered data to the table.
- [Proofs](Proofs/README.md) groups proof and observation modules by operation. The [native storage invariant map](../../../../docs/proofs/native-storage.md) explains assumptions, proved cases and remaining refinement work.

The supported disk path uses a segmented WAL. The separate [single-file WAL experiment](../../Experiments/WAL/SingleFile.lean) explores recovery policies and is not the `DiskTable` implementation. Run native examples and checks using the [getting-started guide](../../../../docs/getting-started.md).
