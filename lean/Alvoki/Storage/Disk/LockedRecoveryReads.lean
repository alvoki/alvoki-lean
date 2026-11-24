import Alvoki.Storage.Disk.LockedOpenFileReads
import Alvoki.Storage.Disk.RecoveryProgress

namespace Alvoki.WAL.Boundary

open Storage

/-- Successful callback reports at the acquired directory's actual names
supply the read premises for every admitted recovery boundary. A successful
optional read can report absence. Run reads cover only the indices issued
after decoding the observed manifest. The lock and namespace observations
are the same ones used for the native file targets. -/
def RecoveryReads.ofLockedPaths {reports : OpenPathReadReports} {directory : DiskDirectory}
    {owners : DiskSession.LockOwners} {descriptor : Nat} {before : ReopenImage}
    {image : CheckpointPublication.Image} (held : owners.Owns directory descriptor)
    (observes : owners.Owns directory descriptor → reports.Observes directory before image.durable)
    (manifestRead : ∃ value, reports.readOptional (directory.file .manifest) = .ok value)
    (runReads : ∀ bytes header, before.directory.active.manifest = some bytes →
      Manifest.decode bytes = .ok header → ∀ index, index < header.runCount.toNat →
        ∃ payload, reports.readBin (directory.file (.run header.generation index)) = .ok payload)
    (markerRead : ∃ value, reports.readOptional (directory.file .walBoundary) = .ok value)
    (walRead : ∃ value, reports.readOptional (directory.file .wal) = .ok value) :
    RecoveryReads image before before.directory.active.manifest := by
  let checkpoint := (observes held).checkpointReads
  let wal := (observes held).walReads
  refine ⟨checkpoint, wal, ?_, ?_, ?_, ?_⟩
  · exact observedOptional_success manifestRead checkpoint.manifestVisible
  · intro bytes header selected decoded index inRange
    obtain ⟨payload, read⟩ := runReads bytes header selected decoded index inRange
    refine ⟨payload, ?_⟩
    change (reports.readBin (directory.file (.run header.generation index))).mapError toString = .ok payload
    rw [read]
    rfl
  · exact observedOptional_success markerRead (fun value read => (wal.markerVisible value read).symm)
  · exact observedOptional_success walRead (fun value read => (wal.walVisible value read).symm)

end Alvoki.WAL.Boundary
