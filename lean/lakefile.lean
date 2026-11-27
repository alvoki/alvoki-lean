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

target sstableO pkg : FilePath := do
  let source ← inputTextFile (pkg.dir / "native" / "sstable.c")
  let leanInclude ← getLeanIncludeDir
  buildO (pkg.buildDir / "native" / "sstable.o") source #["-I", leanInclude.toString]
    #["-O2", "-fPIC", "-Wall", "-Wextra"] "cc"

lean_lib ComponentPrimitives where
  roots := #[`Alvoki.Codec.Block, `Alvoki.Codec.WordChecksum, `Alvoki.Codec.ByteWords,
    `Alvoki.Kernel.BlockContracts]

@[default_target]
lean_lib Components where
  globs := #[`Alvoki.Experiments.DurableBlob.+, `Alvoki.Experiments.Manifest.+,
    `Alvoki.Experiments.SSTable.+, `Alvoki.Experiments.WAL.+]
  moreLinkObjs := #[fsyncO, readDirCheckedO, sstableO]

lean_lib Alvoki.Checks.Audit.AxiomPolicy
