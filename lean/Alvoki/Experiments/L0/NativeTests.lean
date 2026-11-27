import Alvoki.Experiments.L0.Native

open ExperimentalL0 System

private def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def expectError (operation : IO α) : IO Unit := do
  match ← operation.toBaseIO with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "expected native operation to fail")

def main : IO Unit := IO.FS.withTempDir fun root => do
  for dir in ["wal", "manifest", "tables"] do IO.FS.createDir (root / dir)
  let wal ← WalRecoverySlice.Segmented.Native.create (root / "wal") .boundary 2
  WalRecoverySlice.Segmented.Native.close wal
  (DurableBlob.native (root / "manifest")).publish (L0Manifest.encode .empty)
  let escaped ← Native.withOpen root fun db => do
    expectError (Native.withOpen root fun _ => pure ())
    Native.put db 7 10
    Native.put db 256 (UInt64.ofNat (UInt64.size - 1))
    Native.flush db
    Native.delete db 7
    Native.put db 8 20
    Native.flush db
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
