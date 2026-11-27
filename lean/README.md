# Lean source

[Alvoki/Storage](Alvoki/Storage) contains the storage engine, its models and proofs. Start with the [disk layout](Alvoki/Storage/Disk/README.md) for the native storage implementation. [Alvoki/Checks/Tests](Alvoki/Checks/Tests) contains executable checks; [Alvoki/Checks/Audit](Alvoki/Checks/Audit) contains proof audits and dependency tools.

[Alvoki/Bench/Disk](Alvoki/Bench/Disk) contains the disk benchmark entry points. Lake target names and build settings are in [lakefile.lean](lakefile.lean); the repository [getting-started guide](../docs/getting-started.md) documents the pinned toolchain and checks. Top-level modules such as `Compaction`, `CompactionCodec`, `PackedView` and `ByteWords` are also imported by the storage engine. The `*Main.lean` entry points drive separate search, codec and compaction experiments.

Follow a [snapshot read](Alvoki/Storage/Table/README.md) from the table to one run, or follow [WAL collection](Alvoki/Storage/Disk/WAL/README.md) from a checkpoint and marker to the selected segments. Both guides point to the executable operation and its separate refinement proofs. Consumers of lookup, snapshot, compaction and retention theorems should import their proof modules explicitly.

## Other source directories and top-level modules

| Location | What lives here |
|---|---|
| [Alvoki/Storage](Alvoki/Storage/README.md) | Runtime table, disk adapter, durable publication schedules and storage refinements. |
| [Alvoki/Bench](Alvoki/Bench) and [Alvoki/Checks](Alvoki/Checks) | Benchmark drivers, executable fixtures and proof audit tools. |
| [native](native) | C bindings including checked directory enumeration, descriptor sync and packed operations. |
| [runtime-experiment](runtime-experiment) | Experimental C lowerings, ABI checks and tooling for packed builders and accessors. |
| Top-level Lean modules | Shared byte and run codecs, merge and compaction kernels, logical models, correctness proofs and experiment entry points. For example, [ByteWords](ByteWords.lean) and [CompactionCodec](CompactionCodec.lean) feed storage, while [MergePhasesMain](MergePhasesMain.lean) drives a measurement. [Lake targets](lakefile.lean) identify the executable roots. |
