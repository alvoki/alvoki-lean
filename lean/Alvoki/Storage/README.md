# Sequential storage engine

| Component | Responsibility |
|---|---|
| [Table](Table/README.md) | Organizes versioned rows into a memtable and immutable packed runs. Resolves a point or range read at a pinned sequence. |
| [Disk](Disk/README.md) | Owns the directory lock, serves the public disk API, commits writes to the segmented WAL, persists checkpoints and reconstructs a table on open. |
| [Publication](Publication/README.md) | Orders operations that make a replacement file or checkpoint durable and that retire obsolete names. |
| [Proofs](Proofs) | Contains refinements for the table and publication components. [Disk proofs](Disk/Proofs/README.md) cover WAL, checkpoint, recovery and session behavior. |

To follow a write, start at the [disk API](Disk/DiskTable.lean). The WAL records the mutations needed for recovery. The table serves reads from memory and packed runs. A checkpoint writes a generation of runs and publishes a manifest that names them. On open, that checkpoint and the committed WAL suffix reconstruct the table. [Write and recovery sequence](../../../docs/architecture.md#sequential-storage)
