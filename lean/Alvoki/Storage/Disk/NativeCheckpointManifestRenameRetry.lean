import Alvoki.Storage.Disk.NativeCheckpointManifestRenameReboot
import Alvoki.Storage.Disk.NativeRejectedOpenAlignedRecovery

namespace Alvoki.Storage.DiskSession

open System

/-- A rejected open can leave a different descriptor inventory. When
the reported disposition releases the lock, the next attempt uses that
inventory, reads the same chosen crash files, and returns the retained
key-value history. The lineage records the exact requests and errors. -/
theorem NativeReadPosition.retriesCheckpointManifestRenamePowerLoss (current : NativeReadPosition history log)
    {cut : CheckpointPowerCut current.state.session.directory current.state.writer}
    {report : NativeCheckpointManifestRenameError (image := image) current.state cut}
    (crash : NativeCheckpointManifestRenameCrash report) {rejected input : FilePath}
    (lineage : NativeRejectedOpenLineage current.state.session.directory
      (current.state.census.inode current.state.owner.description)
      (current.state.census.inode current.state.directorySlot.description)
      (crash.reboot, crash.retry) (rejected :: inputs) errors after true)
    (observe : ∀ plan : crash.Plan, Nonempty (NativeCheckpointManifestRenameReads crash input plan after.1)) :
    after.2 = crash.retry ∧ after.1.inode = crash.reboot.inode ∧ errors.length = (rejected :: inputs).length ∧
    ∃ next, NativeCheckpointManifestRenameReopened current crash input next after.1 := by
  obtain ⟨inodes, _, count, _⟩ := lineage.preserves
  exact ⟨lineage.availableFiles, inodes, count, current.reopensCheckpointManifestRenameAt crash observe⟩

end Alvoki.Storage.DiskSession
