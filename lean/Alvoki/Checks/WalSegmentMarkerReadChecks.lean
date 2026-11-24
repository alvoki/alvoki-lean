import Alvoki.Storage.Disk.WalSegmentMarkerRead

open Alvoki Alvoki.Storage

private def checkReplay (files : List (Nat × ByteArray)) (count : Nat) (expected : ByteArray) : IO Unit := do
  let result := recoverMarkedWalSegments .empty (UInt64.ofNat (count * WAL.frameSize)) files
  let .ok (selected, table) := result
    | throw (IO.userError "expected marker-limited replay to succeed")
  unless selected == expected && table.committed.toNat == count do
    throw (IO.userError "marker-limited replay returned different bytes or committed sequence")

private def checkInvalidSpan (files : List (Nat × ByteArray)) (count : Nat) : IO Unit := do
  let result := recoverMarkedWalSegments .empty (UInt64.ofNat (count * WAL.frameSize)) files
  let .error "invalid selected WAL segment spans" := result
    | throw (IO.userError "expected marker-limited replay to reject an invalid file span")

def main : IO Unit := do
  unless selectWalSegmentReadsThrough [0, 1, 4, 9] 0 2 == some ([0, 1], [4, 9]) do
    throw (IO.userError "marker-limited selection lost a sparse later name or included its payload")
  let first := WAL.encodeFrame ⟨1, 7, some 11⟩
  let second := WAL.encodeFrame ⟨2, 8, some 12⟩
  let expected := first ++ second
  let tail := ByteArray.mk #[255, 254]
  checkReplay [(0, first), (1, second ++ tail)] 2 expected
  checkReplay [(0, first), (1, second ++ tail)] 1 first
  checkReplay [(0, expected)] 2 expected
  checkReplay [(0, expected ++ tail)] 2 expected
  checkInvalidSpan [(0, expected), (1, ByteArray.empty)] 2
  checkInvalidSpan [(0, first), (1, tail)] 2
  checkInvalidSpan [(0, expected), (3, ByteArray.empty)] 2
  IO.println "Marker-limited WAL segment checks passed"
