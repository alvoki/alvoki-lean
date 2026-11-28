import Alvoki.Experiments.L0.Native
import Std.Async.System

open ExperimentalL0 System

private def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def initializeRoot (root : FilePath) (capacity : Nat := 2) (policy : WalRecoverySlice.Policy := .boundary) : IO Unit := do
  for dir in ["wal", "manifest", "tables"] do IO.FS.createDir (root / dir)
  let wal ← WalRecoverySlice.Segmented.Native.create (root / "wal") policy capacity
  WalRecoverySlice.Segmented.Native.close wal
  (DurableBlob.native (root / "manifest")).publish (L0Manifest.encode .empty)


private def checkAll (db : Native.Handle) (expected : Array (Option UInt64)) : IO Unit := do
  for k in [:expected.size] do
    check ((← Native.get db k.toUInt64) == expected[k]!) s!"key {k} mismatch"

private def exercise (policy : WalRecoverySlice.Policy) : IO Unit := IO.FS.withTempDir fun root => do
  initializeRoot root 72 policy
  let expected ← Native.withOpen root fun db => do
    let mut expected : Array (Option UInt64) := Array.replicate 31 none
    for i in [:205] do
      let k := i % 31
      if i % 5 == 0 then
        Native.delete db k.toUInt64
        expected := expected.set! k none
      else
        Native.put db k.toUInt64 (i+900).toUInt64
        expected := expected.set! k (some (i+900).toUInt64)
      if i == 49 || i == 117 then
        Native.flush db
        checkAll db expected
    checkAll db expected
    return expected
  check (← (WalRecoverySlice.Segmented.Native.segmentPath (root / "wal") 2).pathExists) "expected second rotation"
  for _ in [:2] do
    Native.withOpen root fun db => checkAll db expected
  Native.withOpen root fun db => Native.flush db
  Native.withOpen root fun db => checkAll db expected

def main : IO Unit := do
  exercise .logOnly
  IO.println "logOnly passed"
  exercise .boundary
  IO.println "boundary passed"
