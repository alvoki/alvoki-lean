import Alvoki.Storage.Disk.ManifestIntegrity
import Alvoki.Storage.Disk.WalBoundary
import Alvoki.Storage.Publication.DirectoryBindings

namespace Alvoki.Storage

open WAL (frameSize)

/-- The checkpoint covers `watermark` frames. The marker limits this
selection to `through` frames of the absolute WAL. -/
structure MarkedWalRange where
  watermark : Nat
  through : Nat

def selectedCheckpointWatermark : Option ByteArray → Option Nat
  | none => some 0
  | some bytes => (Manifest.IntegrityCheckpoint.decode bytes).toOption.map (·.header.committed.toNat)

/-- Decode the strict v2 manifest and marker from the same selected pair.
An absent checkpoint covers zero frames. A missing, invalid or unaligned
marker cannot authorize deletion. -/
def DirectoryPublication.Bindings.walRange (pair : DirectoryPublication.Bindings) : Option MarkedWalRange := do
  let watermark ← selectedCheckpointWatermark pair.manifest
  let marker ← pair.walBoundary
  let count ← (WAL.Boundary.decode marker).toOption
  let through := count.toNat / frameSize
  if count.toNat % frameSize = 0 ∧ watermark ≤ through then some ⟨watermark, through⟩ else none

end Alvoki.Storage
