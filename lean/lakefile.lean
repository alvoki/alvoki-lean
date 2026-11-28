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

lean_exe manifestNativeCheck where
  root := `Alvoki.Experiments.Manifest.NativeTests

target crc32cArchive pkg : FilePath := do
  let buildScript ← inputTextFile (pkg.dir / "native" / "build-crc32c.sh")
  let bridge ← inputTextFile (pkg.dir / "native" / "crc32c.c")
  let includeDir ← getLeanIncludeDir
  let archive := pkg.buildDir / "native" / "libalvoki_crc32c.a"
  buildFileAfterDep archive (Job.collectArray #[buildScript, bridge] "CRC32C sources") fun sources => do
    IO.FS.createDirAll archive.parent.get!
    proc { cmd := "bash", args := #[sources[0]!.toString, archive.toString, includeDir.toString,
      sources[1]!.toString] }

lean_lib CRC32C where
  roots := #[`Alvoki.Codec.CRC32C]
  moreLinkObjs := #[crc32cArchive]

lean_exe crc32cCheck where
  root := `Alvoki.Checks.Tests.CRC32C

lean_lib Alvoki.Checks.Tests.SSTableProducer

lean_exe immutableSSTableCheck where
  root := `Alvoki.Experiments.SSTable.UnifiedFixtures

lean_exe recursiveSSTableCheck where
  root := `Alvoki.Experiments.SSTable.Recursive.Fixtures

lean_lib Alvoki.Checks.Tests.RecursiveSSTableProducer

lean_lib Alvoki.Checks.Benchmarks.SSTableWorkload

lean_exe sstableIndexCacheBench where
  root := `Alvoki.Checks.Benchmarks.SSTableIndexCache
