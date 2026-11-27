# Lean source

[Alvoki/Storage](Alvoki/Storage) contains the storage engine, its models and proofs. Start with the [disk layout](Alvoki/Storage/Disk/README.md) for the native storage implementation. [Alvoki/Checks/Tests](Alvoki/Checks/Tests) contains executable checks; [Alvoki/Checks/Audit](Alvoki/Checks/Audit) contains proof audits and dependency tools.

[Alvoki/Bench/Disk](Alvoki/Bench/Disk) contains the disk benchmark entry points. Lake target names and build settings are in [lakefile.lean](lakefile.lean); the repository [getting-started guide](../docs/getting-started.md) documents the pinned toolchain and checks. Top-level modules such as `Compaction`, `CompactionCodec`, `PackedView` and `ByteWords` are also imported by the storage engine. The `*Main.lean` entry points drive separate search, codec and compaction experiments.

[CompactionRead.lean](Alvoki/Storage/Table/CompactionRead.lean)
implements checked-run reads, including the ordered history used by range reads.
[CompactionReadContract.lean](Alvoki/Storage/Table/CompactionReadContract.lean)
contains accepted-run validity and history definitions shared with compaction.
The runtime module imports `OptProofs`: range history construction requires
ordering evidence. `CompactionProofs` and the checked-run and packed-table
compaction correctness modules are outside the runtime import chain.

The checked-run lookup-to-history theorems are in
[CheckedRunLookup.lean](Alvoki/Storage/Proofs/Table/CheckedRunLookup.lean);
packed-table lookup and snapshot refinements are in
[PackedTableLookup.lean](Alvoki/Storage/Proofs/Table/PackedTableLookup.lean).
The `CompactionRead` module remains the runtime implementation. Code that used
its lookup theorems, or the packed-table lookup refinements previously imported
through `PackedTable` or `DiskTable`, must import the relevant proof module
explicitly.

For compaction and retention guarantees, import
[CheckedRunCompaction.lean](Alvoki/Storage/Proofs/Table/CheckedRunCompaction.lean)
or [PackedTableCompaction.lean](Alvoki/Storage/Proofs/Table/PackedTableCompaction.lean)
explicitly. Their operation definitions remain in the runtime modules.
