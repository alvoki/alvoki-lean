import Alvoki.Storage.Disk.CheckpointManifestRenameReopen

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair

private theorem CheckpointRunBarrierCut.preservesSelectedRuns
    {directory : DiskDirectory} {before : SegmentedWriterState} {cut : CheckpointPowerCut directory before}
    {published : Image} {reached interrupted : RunUnlinkImage}
    (observed : CheckpointRunBarrierCut cut published reached interrupted)
    (oldSelected : SelectedIntegrityCheckpoint before.published.durable before.wal.directory.active.manifest before.checkpoint)
    {survivor : RunFiles} (survives : survivor ∈ interrupted.crashImages) :
    SelectedRunsAgree before.wal.directory.active.manifest survivor before.published.durable := by
  intro bytes metadata visible decoded index within
  obtain ⟨payload, stored⟩ := oldSelected.runExists visible decoded within
  have known := (observed.priorBindings bytes metadata visible decoded index within).trans stored
  unfold RunUnlinkImage.guaranteed at known
  dsimp only at known
  split at known
  · rename_i agrees
    rw [observed.namespaceCut] at survives
    cases took : cut.tookEffect with
    | false =>
      have present : survivor ∈ reached.crashImages := by simpa [took] using survives
      exact (of_decide_eq_true (List.all_eq_true.mp agrees survivor present)).trans (known.trans stored.symm)
    | true =>
      have same : survivor = reached.visible := by
        simpa [took, RunUnlinkImage.syncDirectory, RunUnlinkImage.settled] using survives
      rw [same]
      exact known.trans stored.symm
  · contradiction

/-- A survivor that retains the prior manifest and its exact run bytes
reopens the prior checkpoint under the reported native calls. The logical
publication map may also contain an unselected newer generation. -/
theorem CheckpointPowerCut.reopensPriorCheckpoint {directory : DiskDirectory} {before : SegmentedWriterState}
    {writer : Nat} {input : FilePath} (cut : CheckpointPowerCut directory before)
    (ready : before.RetainedReady directory writer) (published : Image)
    (executed : before.published.executeVersioned cut.checkpoint.plan cut.checkpoint.cut = some published)
    (selected : before.wal.directory.active.manifest ∈ published.manifest.crashImages)
    (olderRuns : ∀ older, older ≠ SegmentedCheckpointReport.generation before → ∀ index,
      published.durable older index = before.published.durable older index)
    (survivor : RunFiles)
    (oldAgrees : SelectedRunsAgree before.wal.directory.active.manifest survivor before.published.durable)
    (retry : LockedFileState FileImage) :
    BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first)
      ⟨(CheckpointPowerCut.physical before published).crash before.wal.directory.active (some before.wal.active.bytes) [],
        before.owners.set (directory.file .lock) none⟩ retry →
    CheckpointHeldOpen.Reports input directory before retry published { published with durable := survivor } →
    cut.HeldReopen input writer retry published before.wal.directory.active.manifest survivor ∧
      ∀ checkpoint, SelectedIntegrityCheckpoint survivor before.wal.directory.active.manifest checkpoint →
        checkpoint = before.checkpoint := by
  intro failures reads
  have oldSelected := ready.resumed.selected
  rw [← ready.walPair] at oldSelected
  have agrees : SelectedRunsAgree before.wal.directory.active.manifest survivor published.durable := by
    intro bytes metadata visible decoded index within
    have different := (cut.priorSelectedGeneration ready visible decoded).2
    rw [olderRuns _ different _]
    exact oldAgrees bytes metadata visible decoded index within
  refine ⟨cut.reopensSelectedRunMap ready published executed _ selected survivor agrees retry failures reads, ?_⟩
  intro checkpoint chosen
  exact (SelectedIntegrityCheckpoint.withRunMap chosen oldAgrees).uniqueResult oldSelected

/-- The first directory barrier leaves the prior manifest selected. The old
checkpoint's guaranteed bindings at the reached prefix suffice for each
reported crash map. Fresh orphan bindings can vary with the barrier effect.
Open uses this surviving map and returns the admitted session and writer. -/
theorem CheckpointRunBarrierCut.reopens {directory : DiskDirectory} {before : SegmentedWriterState}
    {writer : Nat} {input : FilePath} {cut : CheckpointPowerCut directory before}
    {published : Image} {reached interrupted : RunUnlinkImage}
    (observed : CheckpointRunBarrierCut cut published reached interrupted)
    (ready : before.RetainedReady directory writer) (survivor : RunFiles)
    (survives : survivor ∈ interrupted.crashImages)
    (retry : LockedFileState FileImage) :
    BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first)
      ⟨(CheckpointPowerCut.physical before published).crash before.wal.directory.active (some before.wal.active.bytes) [],
        before.owners.set (directory.file .lock) none⟩ retry →
    CheckpointHeldOpen.Reports input directory before retry published { published with durable := survivor } →
    cut.HeldReopen input writer retry published before.wal.directory.active.manifest survivor ∧
      ∀ checkpoint, SelectedIntegrityCheckpoint survivor before.wal.directory.active.manifest checkpoint →
        checkpoint = before.checkpoint := by
  intro failures reads
  have oldSelected := ready.resumed.selected
  rw [← ready.walPair] at oldSelected
  have oldAgrees := observed.preservesSelectedRuns oldSelected survives
  have selected : before.wal.directory.active.manifest ∈ published.manifest.crashImages := by
    rw [observed.manifestChoices]
    exact List.mem_singleton_self _
  exact cut.reopensPriorCheckpoint ready published observed.executed selected observed.olderRuns survivor oldAgrees
    retry failures reads

end Alvoki.Storage.DiskSession
