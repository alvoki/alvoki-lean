import Alvoki.Storage.Disk.WalBoundary

namespace Alvoki.Storage
open WAL (frameSize)

/-- Recover after physically removing `removedThrough` frames. Validate the
retained frames at their original positions before dropping frames already
represented by the checkpoint. The caller supplies a selected byte range
and a cutoff at or below the loaded checkpoint's watermark. -/
def recoverRetainedFrom (base : PackedTable) (removedThrough : Nat) (retained : ByteArray) :
    Except String PackedTable := do
  let events ← WAL.decodeOrdinalsFrom (removedThrough + 1) retained
  let table ← replay base (events.drop (base.committed.toNat - removedThrough))
  if table.committed.toNat == removedThrough + retained.size / frameSize then .ok table
  else .error "selected WAL frame count disagrees with the recovered sequence"

/-- Recover when every frame in the retained bytes is above the checkpoint
watermark. -/
def recoverRetainedSuffix (base : PackedTable) (retained : ByteArray) : Except String PackedTable :=
  recoverRetainedFrom base base.committed.toNat retained

end Alvoki.Storage

namespace Alvoki.WAL.Boundary

/-- Interpret the unchanged absolute byte marker against bytes starting
after a known number of removed complete frames. The result contains only
bytes after that offset. -/
def selectRetained (removedThrough : Nat) (length : UInt64) (retained : ByteArray) :
    Except String ByteArray :=
  let removedBytes := removedThrough * frameSize
  if length.toNat < removedBytes then .error "WAL boundary precedes its retained data"
  else select (length.toNat - removedBytes).toUInt64 retained

/-- Use the absolute marker to select bytes and replay them at their
original ordinals. -/
def recoverRetainedMarked (base : Storage.PackedTable) (removedThrough : Nat) (length : UInt64)
    (retained : ByteArray) : Except String (ByteArray × Storage.PackedTable) := do
  let selected ← selectRetained removedThrough length retained
  let table ← Storage.recoverRetainedFrom base removedThrough selected
  return (selected, table)

end Alvoki.WAL.Boundary
