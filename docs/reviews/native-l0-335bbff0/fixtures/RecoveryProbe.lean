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



def main (args : List String) : IO Unit := do
  match args with
  | ["seed", path, policy] =>
    let root : FilePath := path
    initializeRoot root 3 (if policy == "logOnly" then .logOnly else .boundary)
    Native.withOpen root fun db => do
      Native.put db 7 11
      Native.put db 7 22
      Native.put db 8 55
      Native.delete db 7
      Native.put db 9 99
  | ["check", path] =>
    Native.withOpen path fun db => do
      check ((← Native.get db 7).isNone) "tombstone lost"
      check ((← Native.get db 8) == some 55) "sealed history lost"
      check ((← Native.get db 9) == some 99) "active history lost"
  | _ => throw (IO.userError "probe arguments")
