import Alvoki.Experiments.L0.Basic
import Alvoki.Experiments.WAL.Segmented.Native

/-! Exercise the proposed L0 handoff from real compact WAL handles. -/
namespace CompactWalReplay
open System ExperimentalL0 WalRecoverySlice

private def step (watermark : Nat) (acc : Except String MemTable)
    (position : Nat) (batch : Bytes) : Except String MemTable := do
  if position ≤ watermark then return ← acc
  let mem ← acc
  let some change := ExperimentalL0.decode batch | throw "invalid L0 mutation batch"
  return ExperimentalL0.insert mem change

private def withReplay (path : FilePath) (watermark : UInt64) (checkTables : IO Unit)
    (use : Segmented.Native.Handle → MemTable → IO α) : IO α := do
  let through := watermark.toNat
  let (wal, bounds, replayed) ← Segmented.Native.openExistingFold path
    (.ok (∅ : MemTable)) (step through)
  let result ← Segmented.Native.cleanupOnError (error := IO.Error) (do
    unless bounds.base ≤ through && through ≤ bounds.tail do
      throw (IO.userError "manifest watermark outside the WAL view")
    let mem ← IO.ofExcept (replayed.mapError IO.userError)
    checkTables
    use wal mem) (Segmented.Native.close wal)
  Segmented.Native.close wal
  return result

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def expectError (operation : IO α) (message : String) : IO Unit := do
  match ← operation.toBaseIO with
  | .error (.userError actual) => require (actual == message) s!"expected {message}, got {actual}"
  | _ => throw (IO.userError s!"expected {message}")

private def replayFixture (dir : FilePath) (policy : Policy) : IO Unit := do
  let wal ← Segmented.Native.create dir policy 2
  let _ ← Segmented.Native.append wal [11]
  let _ ← Segmented.Native.append wal (encode (1, .put 77))
  let _ ← Segmented.Native.append wal (encode (1, .delete))
  let _ ← Segmented.Native.append wal (encode (2, .put 8))
  let _ ← Segmented.Native.append wal (encode (1, .put 99))
  Segmented.Native.close wal
  for _ in [:2] do
    withReplay dir 2 (pure ()) fun handle mem => do
      require (mem.get? 1 == some (.put 99) && mem.get? 2 == some (.put 8)) "bad replay"
      require ((← Segmented.Native.bounds handle) == ⟨0, 5⟩) "wrong reached handle"
    withReplay dir 5 (pure ()) fun _ mem => require mem.isEmpty "replayed flushed batches"
  expectError (withReplay dir 6 (pure ()) fun _ _ => pure ())
    "manifest watermark outside the WAL view"
  expectError (withReplay dir 2 (throw (IO.userError "required table unavailable")) fun _ _ => pure ())
    "required table unavailable"
  expectError (withReplay dir 0 (throw (IO.userError "required table unavailable")) fun _ _ => pure ())
    "invalid L0 mutation batch"
  let wal ← Segmented.Native.openExisting dir
  Segmented.Native.discardThrough wal 1
  Segmented.Native.close wal
  expectError (withReplay dir 0 (pure ()) fun _ _ => pure ())
    "manifest watermark outside the WAL view"

private def failurePriority (dir : FilePath) (policy : Policy) : IO Unit := do
  let wal ← Segmented.Native.create dir policy 1
  let _ ← Segmented.Native.append wal [11]
  let _ ← Segmented.Native.append wal [22]
  Segmented.Native.close wal
  let active := dir / "segment-1" / "segment"
  let valid ← IO.FS.readBinFile active
  IO.FS.writeBinFile active ⟨(frame 2 [22]).toArray⟩
  for watermark in [0, 3] do
    expectError (withReplay dir watermark (pure ()) fun _ _ => pure ()) "gap or generation mismatch"
  IO.FS.writeBinFile active valid
  expectError (withReplay dir 3 (pure ()) fun _ _ => pure ())
    "manifest watermark outside the WAL view"
  expectError (withReplay dir 0 (pure ()) fun _ _ => pure ()) "invalid L0 mutation batch"
  withReplay dir 2 (pure ()) fun _ mem => require mem.isEmpty "retry after errors failed"

def run : IO Unit := do
  for policy in [Policy.logOnly, .boundary] do
    IO.FS.withTempDir fun dir => replayFixture dir policy
    IO.FS.withTempDir fun dir => failurePriority dir policy
  IO.println "Compact WAL L0 replay and error-priority fixtures passed"

end CompactWalReplay

def main : IO Unit := CompactWalReplay.run
