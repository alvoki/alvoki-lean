import Alvoki.Storage.Disk.VersionedCheckpointRead
import Alvoki.Compaction.Codec

open Alvoki.Manifest Alvoki.Storage Alvoki.Compaction

private def oneRow (key sequence value : UInt64) : ByteArray :=
  appendV3Row (encodeV3Header 1) ⟨key, sequence, (0, value)⟩

def main : IO Unit := do
  let header : Checkpoint := ⟨7, 2, 1, 2⟩
  let first := oneRow 3 1 40
  let second := oneRow 4 2 80
  let files := [first, second]
  let integrity := IntegrityCheckpoint.fromRuns header files
  let reads ← IO.mkRef ([] : List (UInt64 × Nat))
  let readRun (files : List ByteArray) (generation : UInt64) (index : Nat) : IO ByteArray := do
    reads.modify ((generation, index) :: ·)
    let some bytes := files[index]? | throw (IO.userError "unexpected run index")
    pure bytes
  for bytes in [Alvoki.Manifest.encode header, integrity.encode] do
    reads.set []
    let some (loaded, generation) ←
      readVersionedCheckpoint (pure (some bytes)) (readRun files) IO.ofExcept
      | throw (IO.userError "expected a loaded checkpoint")
    unless generation == 7 && loaded.committed == 2 && loaded.pins.floor == 1 &&
        (← reads.get).reverse == [(7, 0), (7, 1)] do
      throw (IO.userError "manifest version changed the ordered read, generation, watermark, or floor")
    let some (pin, pinned) := loaded.acquireAt 2 | throw (IO.userError "expected recovered snapshot")
    unless pinned.lookup pin.handle 3 == some (some 40) && pinned.lookup pin.handle 4 == some (some 80) do
      throw (IO.userError "manifest version changed the recovered values")

  let resumed ← IO.mkRef false
  let failed ← (do
    let _ ← readVersionedCheckpoint (pure (some integrity.encode))
      (readRun [oneRow 3 1 41, second]) IO.ofExcept
    resumed.set true : IO Unit).toBaseIO
  match failed with
  | .error (.userError message) =>
    unless message == checkpointIntegrityMismatch do throw (IO.userError "unexpected integrity error")
  | _ => throw (IO.userError "expected a rejected substituted run")
  if ← resumed.get then throw (IO.userError "open resumed after its checkpoint failed integrity checking")
  IO.println "Versioned checkpoint reads preserve run order and stop open on an integrity mismatch."
