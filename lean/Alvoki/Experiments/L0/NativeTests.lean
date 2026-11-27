import Alvoki.Experiments.L0.Native

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
    let active := root / "manifest" / "BLOB"
    let expected : L0Manifest.Version :=
      if cut == "table" then ⟨[0], 1⟩ else ⟨[1, 0], 3⟩
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
  Native.withOpen root fun db => do
    check ((← Native.get db 7).isNone) "tombstone disappeared on recovery"
    check ((← Native.get db 8) == some 20) "new run value"
    check ((← Native.get db 9) == some 30) "WAL suffix was not replayed"
    IO.FS.rename newTable hidden
    try expectError (Native.get db 7)
    finally IO.FS.rename hidden newTable
    check ((← Native.get db 7).isNone) "failed read changed the session"
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
  | ["flush", root] => Native.withOpen (FilePath.mk root) Native.flush
  | [library] =>
    nativeSchedule
    let executable ← IO.appPath
    interruption executable.toString library "table"
    interruption executable.toString library "rename"
  | _ => throw (IO.userError "expected the process-interruption fixture library")
