import Alvoki.Experiments.L0.Native
import Std.Async.System

open ExperimentalL0 System

private def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def expectError (operation : IO α) : IO Unit := do
  match ← operation.toBaseIO with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "expected native operation to fail")

private def initializeRoot (root : FilePath) : IO Unit := do
  for dir in ["wal", "manifest", "tables"] do IO.FS.createDir (root / dir)
  let wal ← WalRecoverySlice.Segmented.Native.create (root / "wal") .boundary 2
  WalRecoverySlice.Segmented.Native.close wal
  (DurableBlob.native (root / "manifest")).publish (L0Manifest.encode .empty)

private def oneShotTableRead : IO Unit := IO.FS.withTempDir fun dir => do
  let root ← IO.FS.realPath dir
  initializeRoot root
  Native.withOpen root fun db => do
    Native.put db 7 10
    Native.flush db
  let descriptorCount := do return (← (FilePath.mk "/proc/self/fd").readDir).size
  let outside ← descriptorCount
  let escaped ← Native.withOpen root fun db => do
    let online ← descriptorCount
    let target := tablePath (root / "tables") 0
    Std.Async.System.setEnvVar "ALVOKI_L0_FAIL_TABLE_SIZE" target.toString
    expectError (Native.get db 7)
    check ((← descriptorCount) == online) "size error retained a table descriptor"
    check ((← Native.get db 7) == some 10) "get after the caught size error lost the value"
    check ((← descriptorCount) == online) "second get retained a table descriptor"
    return db
  check ((← descriptorCount) == outside) "withOpen retained a descriptor after the caught size error"
  expectError (Native.get escaped 7)
  Native.withOpen root fun db => do
    check ((← Native.get db 7) == some 10) "reopen after the size error lost the value"
  check ((← descriptorCount) == outside) "reopened scope retained a descriptor"

private def interruption (executable library cut : String) : IO Unit :=
  IO.FS.withTempDir fun root => do
    initializeRoot root
    Native.withOpen root fun db => do
      Native.put db 7 10
      Native.flush db
      Native.delete db 7
      Native.put db 8 20
    let proc ← IO.Process.output {
      cmd := executable
      args := #["flush", root.toString]
      env := #[("LD_PRELOAD", some library), ("ALVOKI_L0_CUT", some cut)]
    }
    check (proc.exitCode == 73) s!"missed process cut {cut}: {proc.stderr}"
    check proc.stdout.isEmpty "interrupted flush emitted an acknowledgement"
    let active := root / "manifest" / "BLOB"
    let expected : L0Manifest.Version :=
      if cut == "table" then ⟨[0], 1⟩ else ⟨[1, 0], 3⟩
    check (L0Manifest.decode (← IO.FS.readBinFile active) == some expected)
      "interruption reached the wrong manifest binding"
    let prepared := tablePath (root / "tables") 1
    check ((← prepared.symlinkMetadata).type == .file) "interruption lost the prepared table name"
    let required := tablePath (root / "tables") (if cut == "table" then 0 else 1)
    let hidden := root / "tables" / "hidden-required"
    let published ← IO.mkRef false
    IO.FS.rename required hidden
    try expectError (Native.withOpen root fun _ => published.set true)
    finally IO.FS.rename hidden required
    check (!(← published.get)) "failed restart published an L0 session"
    for _ in [0, 1] do
      Native.withOpen root fun db => do
        check (L0Manifest.decode (← IO.FS.readBinFile active) == some expected)
          "reopen selected the wrong manifest"
        check ((← Native.get db 7).isNone) "interruption lost the tombstone"
        check ((← Native.get db 8) == some 20) "interruption lost the acknowledged value"
    if cut == "table" then
      let orphan := root / "tables" / "table-1"
      let bytes ← IO.FS.readBinFile orphan
      Native.withOpen root Native.flush
      check ((← IO.FS.readBinFile orphan) == bytes) "retry overwrote the orphan"
      check (L0Manifest.decode (← IO.FS.readBinFile active) == some ⟨[2, 0], 3⟩)
        "retry reused the orphan's ID"

/-- Simulate acknowledgement loss at the caller after the public scope has
closed. The other two modes stop or fail inside the issued WAL operation. -/
private def appendChild (root : FilePath) (mode : String) (rotate : Bool) : IO Unit := do
  Native.withOpen root fun db => do
    let mutation := if rotate then Native.delete db 42 else Native.put db 42 99
    if mode == "error" then
      let id := if rotate then "segment-1" else "segment-0"
      Std.Async.System.setEnvVar "ALVOKI_L0_FAIL_WAL_SYNC" (root / "wal" / id / "segment").toString
      expectError mutation
      expectError (Native.get db 42)
    else
      if mode == "control" then Std.Async.System.setEnvVar "ALVOKI_L0_CUT" "control"
      mutation
  if mode == "lost" then IO.Process.exit 74
  IO.println "returned"

private def appendRetry (executable library mode : String) (rotate : Bool) : IO Unit :=
  IO.FS.withTempDir fun dir => do
    let root ← IO.FS.realPath dir
    initializeRoot root
    Native.withOpen root fun db => do
      Native.put db 42 11
      if rotate then Native.put db 17 23
    let proc ← IO.Process.output {
      cmd := executable
      args := #["append", root.toString, mode, if rotate then "rotate" else "active"]
      env := #[("LD_PRELOAD", some library)]
    }
    let expectedExit := if mode == "control" then 73 else if mode == "lost" then 74 else 0
    check (proc.exitCode == expectedExit) s!"append {mode}, rotation={rotate}: {proc.stderr}"
    check (proc.stdout == (if mode == "error" then "returned\n" else ""))
      "unexpected completion acknowledgement"
    let expected := if mode == "lost" then (if rotate then none else some 99) else some 11
    for _ in [0, 1] do
      Native.withOpen root fun db => do
        check ((← Native.get db 42) == expected) "reopen selected the wrong mutation"
        check ((← Native.get db 17) == (if rotate then some 23 else none)) "reopen lost the prior prefix"

private def nativeSchedule : IO Unit := IO.FS.withTempDir fun root => do
  initializeRoot root
  let active := root / "manifest" / "BLOB"
  let firstTable := root / "tables" / "table-0"
  let escaped ← Native.withOpen root fun db => do
    expectError (Native.withOpen root fun _ => pure ())
    let initial ← IO.FS.readBinFile active
    Native.put db 7 10
    Native.put db 256 (UInt64.ofNat (UInt64.size - 1))
    check ((← IO.FS.readBinFile active) == initial) "WAL writes changed the manifest"
    Native.flush db
    let firstBytes ← IO.FS.readBinFile firstTable
    Native.delete db 7
    Native.put db 8 20
    Native.flush db
    check ((← IO.FS.readBinFile firstTable) == firstBytes) "flush modified an immutable table"
    Native.put db 9 30
    check ((← Native.get db 7).isNone) "flushed tombstone returned an older value"
    check ((← Native.get db 256) == some (UInt64.ofNat (UInt64.size - 1))) "older run lookup"
    return db
  expectError (Native.get escaped 7)
  check ((← (root / "wal" / "segment-2").metadata).type == .dir) "WAL did not rotate"
  let newTable := root / "tables" / "table-1"
  let hidden := root / "tables" / "hidden"
  -- Hide the required newest table to exercise the failed table-open path,
  -- after manifest and WAL recovery have already succeeded.
  let exposed ← IO.mkRef false
  IO.FS.rename newTable hidden
  try expectError (Native.withOpen root fun _ => exposed.set true)
  finally IO.FS.rename hidden newTable
  check (!(← exposed.get)) "failed table check exposed an online session"
  let intendedBytes ← IO.FS.readBinFile newTable
  IO.FS.writeBinFile newTable (← IO.FS.readBinFile firstTable)
  try expectError (Native.withOpen root fun _ => exposed.set true)
  finally IO.FS.writeBinFile newTable intendedBytes
  check (!(← exposed.get)) "recovery accepted a valid table under the wrong ID"
  Native.withOpen root fun db => do
    check ((← Native.get db 7).isNone) "tombstone disappeared on recovery"
    check ((← Native.get db 8) == some 20) "new run value"
    check ((← Native.get db 9) == some 30) "WAL suffix was not replayed"
    IO.FS.rename newTable hidden
    try expectError (Native.get db 7)
    finally IO.FS.rename hidden newTable
    check ((← Native.get db 7).isNone) "failed read changed the session"
    -- Corrupt the checked-open input after recovery so the get fails only
    -- after the table descriptor has been acquired.
    let descriptors : FilePath := "/proc/self/fd"
    if ← descriptors.pathExists then
      let baseline := (← descriptors.readDir).size
      for _ in List.range 3 do
        check ((← Native.get db 8) == some 20) "descriptor fixture lost the value"
        check ((← descriptors.readDir).size == baseline) "successful get retained a descriptor"
      IO.FS.writeBinFile newTable ByteArray.empty
      try
        for _ in List.range 3 do
          expectError (Native.get db 8)
          check ((← descriptors.readDir).size == baseline) "failed get retained a descriptor"
      finally IO.FS.writeBinFile newTable intendedBytes
  let orphan := root / "tables" / "table-2"
  IO.FS.writeBinFile orphan ⟨#[42]⟩
  Native.withOpen root fun db => do
    check ((← Native.get db 9) == some 30) "second reopen lost the suffix"
    Native.flush db
  check ((← IO.FS.readBinFile orphan) == ⟨#[42]⟩) "allocator overwrote an orphan"
  Native.withOpen root fun db => do
    check ((← Native.get db 9) == some 30) "suffix failed to survive flush"
    Native.put db 10 40
    let tableDir := root / "tables"
    let hiddenDir := root / "hidden-tables"
    IO.FS.rename tableDir hiddenDir
    try expectError (Native.flush db)
    finally IO.FS.rename hiddenDir tableDir
    expectError (Native.get db 10)
  Native.withOpen root fun db => do
    check ((← Native.get db 10) == some 40) "failed flush lost acknowledged WAL input"

def main (args : List String) : IO Unit := do
  match args with
  | ["read-fault"] => oneShotTableRead
  | ["append", root, mode, branch] => appendChild (FilePath.mk root) mode (branch == "rotate")
  | ["flush", root] =>
    Native.withOpen (FilePath.mk root) Native.flush
    IO.println "flushed"
  | [library] =>
    nativeSchedule
    let executable ← IO.appPath
    let proc ← IO.Process.output {
      cmd := executable.toString
      args := #["read-fault"]
      env := #[("LD_PRELOAD", some library)]
    }
    check (proc.exitCode == 0) s!"one-shot table read fixture failed: {proc.stderr}"
    for rotate in [false, true] do
      for mode in ["lost", "error"] do appendRetry executable.toString library mode rotate
    appendRetry executable.toString library "control" true
    interruption executable.toString library "table"
    interruption executable.toString library "rename"
  | _ => throw (IO.userError "expected the process-interruption fixture library")
