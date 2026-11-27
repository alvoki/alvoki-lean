# Lean source

[Alvoki/Storage](Alvoki/Storage) contains the storage engine, its models and proofs. Start with the [disk layout](Alvoki/Storage/Disk/README.md) for the native storage implementation. [Alvoki/Checks/Tests](Alvoki/Checks/Tests) contains executable checks; [Alvoki/Checks/Audit](Alvoki/Checks/Audit) contains proof audits and dependency tools.

[Alvoki/Bench/Disk](Alvoki/Bench/Disk) contains the disk benchmark entry points. Lake target names and build settings are in [lakefile.lean](lakefile.lean); the repository [getting-started guide](../docs/getting-started.md) documents the pinned toolchain and checks. The storage engine also imports shared modules such as [compaction](Alvoki/Compaction/Core.lean), its [codec](Alvoki/Compaction/Codec.lean), and [PackedView](Alvoki/Codec/PackedView.lean). The [benchmark entry points](Alvoki/Bench) drive separate disk, merge, search, codec and compaction experiments.

Follow a [snapshot read](Alvoki/Storage/Table/README.md) from the table to one run, or follow [WAL collection](Alvoki/Storage/Disk/WAL/README.md) from a checkpoint and marker to the selected segments. Both guides point to the executable operation and its separate refinement proofs. Consumers of lookup, snapshot, compaction and retention theorems should import their proof modules explicitly.

For an experiment, the `alvoki-fused-merge` target in [lakefile.lean](lakefile.lean)
starts [FusedMergeMain.lean](Alvoki/Bench/Merge/FusedMergeMain.lean), which calls
the shared [FusedMerge](Alvoki/Experiments/Merge/FusedMerge.lean) kernel and its
[SpanMerge](Alvoki/Experiments/Merge/SpanMerge.lean) emitter. Run the workload
and its fixtures through `bash scripts/fused-merge.sh`; see the
[benchmark guide](../docs/performance/benchmarks.md) for options and results.

## Other source directories and top-level modules

| Location | What lives here |
|---|---|
| [Alvoki/Storage](Alvoki/Storage/README.md) | Runtime table, disk adapter, durable publication schedules and storage refinements. |
| [Alvoki/Bench](Alvoki/Bench) and [Alvoki/Checks](Alvoki/Checks) | Benchmark drivers, executable fixtures and proof audit tools. |
| [native](native) | C bindings including checked directory enumeration, descriptor sync and packed operations. |
| [runtime-experiment](runtime-experiment) | Experimental C lowerings, ABI checks and tooling for packed builders and accessors. |
| [Alvoki/Codec](Alvoki/Codec), [Alvoki/Compaction](Alvoki/Compaction), [Alvoki/Kernel](Alvoki/Kernel), and [Alvoki/Packed](Alvoki/Packed) | Shared codecs, compaction operations, kernel contracts and packed models used by storage and experiments. |
| [Alvoki/Experiments](Alvoki/Experiments) and [Alvoki/Proofs](Alvoki/Proofs) | Experimental kernels and standalone byte, merge and packed correctness proofs. |

The only Lean source file kept directly in this directory is
[lakefile.lean](lakefile.lean), the package configuration Lake discovers at the
project root. Its existing target names remain the entry points for builds and
executables.
