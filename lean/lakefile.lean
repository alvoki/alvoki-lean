import Lake
open Lake DSL System

package alvoki

target fsyncO pkg : FilePath := do
  let source ← inputTextFile (pkg.dir / "native" / "fsync.c")
  let leanInclude ← getLeanIncludeDir
  buildO (pkg.buildDir / "native" / "fsync.o") source #["-I", leanInclude.toString]
    #["-O2", "-fPIC", "-Wall", "-Wextra"] "cc"

target readDirCheckedO pkg : FilePath := do
  let source ← inputTextFile (pkg.dir / "native" / "read_dir_checked.c")
  let leanInclude ← getLeanIncludeDir
  buildO (pkg.buildDir / "native" / "read_dir_checked.o") source #["-I", leanInclude.toString]
    #["-O2", "-fPIC", "-Wall", "-Wextra"] "cc"

lean_lib Block

lean_lib Proofs

lean_lib Optimizations

lean_lib OptProofs

lean_lib Packed

@[default_target]
lean_lib PackedRun

lean_lib PackedView

lean_lib PackedViewProofs

lean_lib MergeModel

lean_lib MergeProofs

lean_lib NativeTune where
  moreLeancArgs := #["-Rpass=loop-vectorize", "-Rpass-missed=loop-vectorize", "-Rpass-analysis=loop-vectorize"]

lean_lib MergePhases

lean_lib ScopedBytes

lean_lib ScopedBytesProofs

lean_lib ReplayProofs

lean_lib FusedMerge

lean_lib Compaction

lean_lib SpanMerge

lean_lib BlockCodec

lean_lib CompactionModel

lean_lib RunProofs

lean_lib ByteWords

lean_lib CompactionCodec

lean_lib CompactionProofs

lean_lib RunMergeProofs

lean_lib CodecVariants

lean_lib Alvoki.Storage where
  globs := #[`Alvoki.Storage.+]
  moreLinkObjs := #[fsyncO, readDirCheckedO]

lean_lib Alvoki.Checks.Audit.AxiomPolicy

@[default_target]
lean_exe alvoki where
  root := `Main

lean_exe «alvoki-opt» where
  root := `OptMain

lean_exe «alvoki-packed» where
  root := `PackedMain
  moreLinkArgs := #[".lake/alvoki-packed.o"]

lean_exe «alvoki-native» where
  root := `NativeMain

lean_exe «alvoki-merge-phases» where
  root := `Alvoki.Bench.Merge.MergePhasesMain

lean_exe «alvoki-fused-merge» where
  root := `Alvoki.Bench.Merge.FusedMergeMain

lean_exe «alvoki-compaction» where
  root := `CompactionMain

lean_exe «alvoki-compaction-cursor» where
  root := `CompactionCursorMain

lean_exe «alvoki-disk-checks» where
  root := `Alvoki.Checks.Tests.DiskTableChecks

lean_exe «alvoki-disk-replay» where
  root := `Alvoki.Bench.Disk.DiskReplayBench

lean_exe «alvoki-disk-write» where
  root := `Alvoki.Bench.Disk.DiskWriteBench

lean_exe «alvoki-disk-checkpoint» where
  root := `Alvoki.Bench.Disk.DiskCheckpointBench

lean_exe «alvoki-wide-accessors» where
  root := `WideAccessorBench
  srcDir := "runtime-experiment/wide-accessors"
  moreLeancArgs := #["-include", "runtime-experiment/wide-accessors/accessors.h"]

lean_exe «alvoki-disk-workload» where
  root := `Alvoki.Bench.Disk.DiskWorkloadBench

lean_exe «alvoki-disk-crash» where
  root := `Alvoki.Bench.Disk.DiskCrashBench

lean_exe «alvoki-disk-batch» where
  root := `Alvoki.Bench.Disk.DiskBatchBench
