import Alvoki.Storage.Disk.CheckpointManifestDirectoryCut
import Alvoki.Storage.Disk.CheckpointManifestRenameReopen

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication

/-- Reopen from an actual physical manifest survivor while keeping the
settled run map, the same WAL history, and the actual admitted session.
An effective final barrier selects the new checkpoint. -/
theorem CheckpointManifestDirectoryCut.reopens {directory : DiskDirectory} {before : SegmentedWriterState}
    {writer : Nat} {input : FilePath} {cut : CheckpointPowerCut directory before}
    {published : Image} {runs : RunUnlinkImage} {manifests : List (Option ByteArray)}
    (observed : CheckpointManifestDirectoryCut cut published runs manifests)
    (ready : before.RetainedReady directory writer) (selected : Option ByteArray) (survives : selected ∈ manifests)
    (retry : LockedFileState WalSegmentRepair.FileImage) :
    let pair : DirectoryPublication.Bindings := ⟨selected, before.wal.directory.active.walBoundary⟩
    BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first)
      ⟨(CheckpointPowerCut.physical before published).crash pair (some before.wal.active.bytes) [],
        before.owners.set (directory.file .lock) none⟩ retry →
    CheckpointHeldOpen.Reports input directory before retry published { published with durable := runs.guaranteed } →
    (cut.tookEffect = true → selected = some cut.checkpoint.manifest) ∧
    before.wal.directory.active.manifest ≠ some cut.checkpoint.manifest ∧
    cut.HeldReopen input writer retry published selected runs.guaranteed := by
  intro pair failures reads
  have admitted := observed.admitted selected survives
  have origin : selected = before.wal.directory.active.manifest ∨ selected = some cut.checkpoint.manifest := by
    rw [observed.manifestChoices] at admitted
    cases took : cut.tookEffect <;> simp_all [or_comm]
  refine ⟨fun took => List.mem_singleton.mp (observed.effective took ▸ survives), cut.manifestChanges ready, ?_⟩
  exact cut.reopensPhysicalCheckpoint ready published observed.executed selected admitted origin runs.guaranteed
    observed.newRuns observed.priorRuns retry failures reads

end Alvoki.Storage.DiskSession
