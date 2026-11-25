import Alvoki.Storage.Disk.CheckpointManifestRenameReopen

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair

private theorem storedRunExists {indices : List Nat} {read : Nat → Option ByteArray}
    {files : List ByteArray} (stored : indices.mapM read = some files) {index : Nat}
    (named : index ∈ indices) : ∃ bytes, read index = some bytes := by
  induction indices generalizing files with
  | nil => simp at named
  | cons first rest ih =>
    cases firstRead : read first with
    | none => simp [List.mapM_cons, firstRead, Bind.bind, Option.bind] at stored
    | some bytes =>
      rcases List.mem_cons.mp named with same | later
      · exact ⟨bytes, same ▸ firstRead⟩
      · cases tailRead : rest.mapM read with
        | none => simp [List.mapM_cons, firstRead, tailRead, Bind.bind, Option.bind] at stored
        | some tail => exact ih tailRead later

private theorem selectedRunExists {runFiles binding checkpoint}
    (selected : SelectedIntegrityCheckpoint runFiles binding checkpoint)
    {bytes : ByteArray} {manifest : Manifest.IntegrityCheckpoint}
    (visible : binding = some bytes) (decoded : Manifest.IntegrityCheckpoint.decode bytes = .ok manifest)
    {index : Nat} (within : index < manifest.header.runCount.toNat) :
    ∃ payload, runFiles manifest.header.generation index = some payload := by
  cases selected with
  | absent => contradiction
  | @present actual checked files table accepted stored loaded =>
    cases visible
    cases Except.ok.inj (decoded.symm.trans accepted)
    exact storedRunExists stored (List.mem_range.mpr within)

private theorem CheckpointRunBarrierCut.preservesSelectedRuns
    {directory : DiskDirectory} {before : SegmentedWriterState} {cut : CheckpointPowerCut directory before}
    {published : Image} {reached interrupted : RunUnlinkImage}
    (observed : CheckpointRunBarrierCut cut published reached interrupted)
    (oldSelected : SelectedIntegrityCheckpoint before.published.durable before.wal.directory.active.manifest before.checkpoint)
    (beforeAgrees : SelectedRunsAgree before.wal.directory.active.manifest reached.guaranteed before.published.durable)
    {survivor : RunFiles} (survives : survivor ∈ interrupted.crashImages) :
    SelectedRunsAgree before.wal.directory.active.manifest survivor before.published.durable := by
  intro bytes metadata visible decoded index within
  obtain ⟨payload, stored⟩ := selectedRunExists oldSelected visible decoded within
  have known := (beforeAgrees bytes metadata visible decoded index within).trans stored
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
    (beforeAgrees : SelectedRunsAgree before.wal.directory.active.manifest reached.guaranteed before.published.durable)
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
  have oldAgrees := observed.preservesSelectedRuns oldSelected beforeAgrees survives
  have selected : before.wal.directory.active.manifest ∈ published.manifest.crashImages := by
    rw [observed.manifestChoices]
    exact List.mem_singleton_self _
  have agrees : SelectedRunsAgree before.wal.directory.active.manifest survivor published.durable := by
    intro bytes metadata visible decoded index within
    have parsed := CheckpointPowerCut.selectedGeneration oldSelected
    rw [← ready.resumed.generation, visible, Option.mapM, decoded] at parsed
    have previous : metadata.header.generation = before.installed.generation := Except.ok.inj parsed
    have different : before.installed.generation ≠ SegmentedCheckpointReport.generation before := by
      intro same
      have values := congrArg UInt64.toNat same
      unfold SegmentedCheckpointReport.generation at values
      rw [UInt64.toNat_ofNat_of_lt' cut.generationFits] at values
      omega
    rw [observed.olderRuns _ (previous ▸ different) _]
    exact oldAgrees bytes metadata visible decoded index within
  refine ⟨cut.reopensSelectedRunMap ready published observed.executed _ selected survivor agrees retry failures reads, ?_⟩
  intro checkpoint chosen
  exact (SelectedIntegrityCheckpoint.withRunMap chosen oldAgrees).uniqueResult oldSelected

end Alvoki.Storage.DiskSession
