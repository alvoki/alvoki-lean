# Lean source

[Alvoki/Storage](Alvoki/Storage) contains the storage engine, its models and proofs. Start with the [disk layout](Alvoki/Storage/Disk/README.md) for the native storage implementation. [Alvoki/Checks/Tests](Alvoki/Checks/Tests) contains executable checks; [Alvoki/Checks/Audit](Alvoki/Checks/Audit) contains proof audits and dependency tools.

[Alvoki/Bench/Disk](Alvoki/Bench/Disk) contains the disk benchmark entry points. Lake target names and build settings are in [lakefile.lean](lakefile.lean); the repository [getting-started guide](../docs/getting-started.md) documents the pinned toolchain and checks. Top-level modules such as `Compaction`, `CompactionCodec`, `PackedView` and `ByteWords` are also imported by the storage engine. The `*Main.lean` entry points drive separate search, codec and compaction experiments.

Follow a [snapshot read](Alvoki/Storage/Table/README.md) from the table to one run, or follow [WAL collection](Alvoki/Storage/Disk/WAL/README.md) from a checkpoint and marker to the selected segments. Both guides point to the executable operation and its separate refinement proofs. Consumers of lookup, snapshot, compaction and retention theorems should import their proof modules explicitly.
