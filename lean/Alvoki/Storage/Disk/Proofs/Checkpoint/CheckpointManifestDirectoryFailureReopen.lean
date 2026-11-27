import Alvoki.Storage.Disk.Proofs.Checkpoint.CheckpointManifestDirectoryFailure
import Alvoki.Storage.Disk.Proofs.Checkpoint.CheckpointLiveHeldReopen

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication WalSegmentRepair

namespace ObservedManifestDirectoryFailure

variable {directory : DiskDirectory} {before : SegmentedWriterState} {cut : CheckpointPowerCut directory before}

/-- The successful admitted open of the exact image left by the returned
manifest-directory error. It retains the chosen physical checkpoint, the
replay of the same WAL, and the actual ready session and writer. -/
structure Reopened (report : ObservedManifestDirectoryFailure cut) {writer : Nat} {input : FilePath}
    {retry : LockedFileState FileImage} {layout : CanonicalKeeperLayout retry.image before.history}
    (released : SegmentedFailureRelease writer) (opened : CheckpointHeldOpen input directory layout report.publication)
    (session : SegmentedSession) (final : LockedFileState FileImage) (after : SegmentedWriterState) : Prop extends
      CheckpointLiveHeldReopened opened session final after where
  poisoned : runCheckpointWithEffects ((report.calls.callbacks directory).perform directory)
      (.ready before.installed, ⟨report.atRun 0, before.owners⟩) =
    .error report.error (.poisoned, ⟨report.after, before.owners⟩)
  handoff : released.Observed (directory := directory) (.poisoned, ⟨report.after, before.owners⟩)
    ⟨report.after, before.owners.set (directory.file .lock) none⟩
  attempts : BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first)
    ⟨CheckpointPowerCut.physical before report.publication, before.owners.set (directory.file .lock) none⟩ retry
  choice : retry.image.directory.active.manifest = some cut.checkpoint.manifest ∨
    (cut.tookEffect = false ∧ retry.image.directory.active.manifest = before.wal.directory.active.manifest)
/-- With the newly renamed manifest live, a returned final sync error
hands the exact reached files to the bounded retry. A later crash before
repair authorization may select the old manifest only if the final sync
had left that binding possible. Both choices use the same physical run
map and preserve the acknowledged history. -/
theorem reopens (report : ObservedManifestDirectoryFailure cut) {writer : Nat} {input : FilePath}
    (ready : before.RetainedReady directory writer) (release : SegmentedFailureRelease writer)
    (retry : LockedFileState FileImage) :
    let publication := report.publication
    let released := ⟨CheckpointPowerCut.physical before publication, before.owners.set (directory.file .lock) none⟩
    BoundedReopenTrace directory (CheckpointRetryTarget before.history before.wal.active.first) released retry →
    CheckpointHeldOpen.Reports input directory before retry publication publication →
    ∃ (layout : CanonicalKeeperLayout retry.image before.history)
      (opened : CheckpointHeldOpen input directory layout publication)
      (session : SegmentedSession) (final : LockedFileState FileImage) (after : SegmentedWriterState),
      report.Reopened release opened session final after := by
  intro publication released attempts reads
  obtain ⟨_, _, _, _, logical, observed⟩ := cut.atManifestDirectory ready report.calls report.atRun report.runs
    report.runPrefix report.reached report.completed
  have choice (binding : Option ByteArray)
      (found : binding = publication.manifest.active ∨ binding ∈ publication.manifest.crashImages) :
      binding = some cut.checkpoint.manifest ∨
        (cut.tookEffect = false ∧ binding = before.wal.directory.active.manifest) := by
    rcases found with active | survived
    · exact .inl (active.trans report.liveManifest)
    · have modeled := observed.admitted binding survived
      rw [observed.manifestChoices] at modeled
      cases took : cut.tookEffect <;> simp_all
  have agrees (binding : Option ByteArray)
      (found : binding = publication.manifest.active ∨ binding ∈ publication.manifest.crashImages) :
      SelectedRunsAgree binding publication.durable logical.durable :=
    cut.selectedRunAgreement ready logical binding
      ((choice binding found).elim Or.inr (fun ⟨_, old⟩ => Or.inl old)) publication.durable
      observed.newRuns observed.priorRuns
  obtain ⟨layout, opened, session, final, after, endpoint⟩ := cut.reopensFromLive ready logical publication observed.executed
    (report.liveManifest.trans observed.liveManifest.symm) observed.admitted agrees retry attempts reads
  obtain ⟨poisoned, handoff, _⟩ := report.poisonsAndReleases ready release
  exact ⟨layout, opened, session, final, after, endpoint,
    cut.preflight.publicationError (report.calls.callbacks directory) directory poisoned,
    handoff, attempts, choice _ endpoint.selectedManifest⟩

end ObservedManifestDirectoryFailure

end Alvoki.Storage.DiskSession
