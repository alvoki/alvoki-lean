import Alvoki.Storage.Disk.Proofs.Session.DiskOpenAdmission
import Alvoki.Storage.Disk.Proofs.Append.SegmentedBatchAppend

namespace Alvoki.Storage.DiskSession

open System WalSegmentCommit WalSegmentRepair WAL.Boundary

/-- The final marked open reports the reads and callbacks for the layout
selected from a released or interrupted batch. -/
abbrev BatchCutReopenObservations (directory : DiskDirectory) (before : SegmentedWriterState)
    (batch : List WAL.Write) (files : Type) (input : FilePath) (retry : LockedFileState FileImage) : Prop :=
  ∀ history, ∀ layout : CanonicalKeeperLayout retry.image history,
    (history = before.history ∨ history = before.history ++ batch) →
    layout.target.first = before.wal.active.first →
    ∃ reported : MarkedRetryChunkReports files directory layout before.published,
      Nonempty (OpenAdmissionReports input directory reported.slot)

/-- The selected marked layout leads to the exact native-shaped open result
under that open's lock slot. Every frame of an uncertain batch shares the
same retention decision. -/
structure AdmittedBatchCutReopen {files : Type} (directory : DiskDirectory) (before : SegmentedWriterState)
    (batch : List WAL.Write) (input : FilePath) (retry : LockedFileState FileImage)
    (descriptor : Nat) (after : SegmentedWriterState) : Prop where
  reopened : ∃ (selected : List WAL.Write) (layout : CanonicalKeeperLayout retry.image selected)
    (reported : MarkedRetryChunkReports files directory layout before.published)
    (admission : OpenAdmissionReports input directory reported.slot)
    (session : SegmentedSession) (final : LockedFileState FileImage),
    reported.runWithAdmission admission = .ok session final ∧
    session.directory = directory ∧ session.descriptor = descriptor ∧ session.phase = .ready after.installed ∧
    final.owners.Owns directory descriptor ∧ after.files = final.image ∧ after.owners = final.owners ∧
    final.image.directory.active = retry.image.directory.active ∧ after.history = selected
  history : after.history = before.history ∨ after.history = before.history ++ batch
  checkpoint : after.checkpoint = before.checkpoint
  generation : after.installed.generation = before.installed.generation
  durable : after.published.durable = before.published.durable
  retained : after.RetainedReady directory descriptor
  sealedWal : after.wal.sealed = before.wal.sealed

/-- Use the same admitted opener for all cuts covered by the batch effect
model. Retry selection supplies the exact keeper, checkpoint authority,
sealed read plan and repair preconditions. -/
theorem BoundedReopenTrace.reopensBatchCutAdmitted {files : Type} {directory : DiskDirectory}
    {before : SegmentedWriterState} {writer : Nat} {input : FilePath}
    {rows : List (UInt64 × Option UInt64)} {batch : List WAL.Write} {next : PackedTable}
    {initial retry : LockedFileState FileImage}
    (attempts : BoundedReopenTrace directory (BatchRetryTarget before.history batch before.wal.active.first)
      initial retry)
    (ready : before.RetainedReady directory writer)
    (prepared : prepareBatch before.installed.table rows = some (batch, next))
    (fits : (WAL.encode (before.history ++ batch)).size < UInt64.size)
    (effects : WriteEffects)
    (sealedAtCut : initial.image.kept = (before.wal.checkpointReopenFiles before.wal.directory none).kept)
    (projected : BatchCutProjection initial.image
      ((writeFilesAfter (runBatchEffects before.history batch effects
        (before.wal.directory.staged .walBoundary))).reopenSegment before.wal.active.first
        before.history before.wal.directory.active.manifest))
    (reads : BatchCutReopenObservations directory before batch files input retry) :
    ∃ descriptor after, AdmittedBatchCutReopen (files := files) directory before batch input retry descriptor after := by
  have oldRange : before.wal.directory.active.walRange = some ⟨before.target.range.watermark, before.history.length⟩ := by
    rw [ready.walPair, ← ready.resumed.through]
    exact before.target.decoded
  have oldAccepted := (congrArg DirectoryPublication.Bindings.manifest ready.walPair).symm ▸ ready.resumed.accepted
  obtain ⟨model, refined, represented⟩ := ready.resumed.canonical
  have count : before.history.length = before.installed.table.committed.toNat :=
    represented.committed_count.symm.trans (congrArg UInt64.toNat refined.committed).symm
  obtain ⟨kept, manifest, history, allowed, _, layout, valid, selected, _, first, _, descriptors, offsets,
    prepared, _, accepted, ordered, _, _⟩ :=
    attempts.selectsAfterBatchCut ready.layout ready.valid oldRange ready.resumed.ordered count prepared
      fits oldAccepted effects projected
  obtain ⟨reported, ⟨admission⟩⟩ := reads history selected allowed first
  have following := reported.selectedAfterWatermark offsets descriptors
  have installed := runOpenWithAdmission_markedRetryFromChunks reported admission
    prepared.keeperPrefix prepared.newer following accepted ordered
  rw [reported.runWithAdmission_eq admission] at installed
  obtain ⟨_, cutReady⟩ := installed.readyForAppend accepted ordered
  let wal := before.wal.appendSelectedView retry.image.directory.active history
  have sealed : retry.image.kept = (wal.checkpointReopenFiles wal.directory none).kept := kept.trans sealedAtCut
  have spans : ∀ segment ∈ wal.sealed, segment.bytes.size = (segment.last - segment.first) * WAL.frameSize := ready.spans
  obtain ⟨session, final, after, returned, path, slot, phase, files, owners, openedWal, target, exactHistory, _, durable, next⟩ :=
    cutReady.writerRetained layout valid spans rfl first sealed
  have readyAfter : after.RetainedReady directory reported.slot.description := reported.inventoryDescription ▸ next
  have oldManifest := manifest.trans (congrArg DirectoryPublication.Bindings.manifest ready.walPair)
  have oldCheckpoint : SelectedIntegrityCheckpoint before.published.durable retry.image.directory.active.manifest
      before.checkpoint := oldManifest.symm ▸ ready.resumed.selected
  have loaded := readyAfter.resumed.selected
  rw [durable, target] at loaded
  have checkpoint := loaded.uniqueResult oldCheckpoint
  have generation : after.installed.generation = before.installed.generation := by
    rw [readyAfter.resumed.generation, checkpoint, ← ready.resumed.generation]
  have held : final.owners.Owns directory reported.slot.description := owners ▸ readyAfter.held
  have pair : final.image.directory.active = retry.image.directory.active :=
    files ▸ (readyAfter.resumed.ready.selected.trans (congrArg Target.pair target))
  have sealedWal := congrArg WalSegmentImage.sealed openedWal
  exact ⟨reported.slot.description, after, ⟨history, selected, reported, admission, session, final,
    (reported.runWithAdmission_eq admission).trans returned, path, slot.trans reported.inventoryDescription,
    phase, held, files, owners, pair, exactHistory⟩, exactHistory ▸ allowed, checkpoint, generation, durable, readyAfter, sealedWal⟩

namespace ObservedBatchFailure

variable {directory : DiskDirectory} {before : SegmentedWriterState}
  {failure : SegmentedBatchFailure directory before} {handle : Type} {writer : Nat}

/-- The exact poisoned batch result and its observed release lead to the
marked open over the same callback file cut. -/
structure AdmittedReopen {files : Type} (observed : ObservedBatchFailure failure handle)
    (release : SegmentedFailureRelease writer) (input : FilePath) (retry : LockedFileState FileImage)
    (descriptor : Nat) (after : SegmentedWriterState) : Prop where
  returned : ∃ cacheAfter,
    let poisoned : Phase Installed × LockedFileState (SyncHandleRouting.Cache handle × WriteFiles) :=
      (.poisoned, ⟨(cacheAfter, failure.failed), before.owners⟩)
    runBatchWrite directory failure.rows observed.guard.lookup observed.append observed.stage observed.sync observed.rename
      (.ready before.installed, ⟨(observed.cache, WriteFiles.initial before.history
        (before.wal.directory.staged .walBoundary)), before.owners⟩) =
      .error (.commitUnknown failure.cause) poisoned ∧
    release.Observed (directory := directory) poisoned ⟨poisoned.2.image, failure.released.owners⟩
  attempts : BoundedReopenTrace directory (BatchRetryTarget before.history failure.batch before.wal.active.first)
    failure.released retry
  installation : AdmittedBatchCutReopen (files := files) directory before failure.batch input retry descriptor after

theorem reopensAdmitted {files : Type} {input : FilePath} {retry : LockedFileState FileImage}
    (observed : ObservedBatchFailure failure handle) (ready : before.RetainedReady directory writer)
    (release : SegmentedFailureRelease writer)
    (attempts : BoundedReopenTrace directory (BatchRetryTarget before.history failure.batch before.wal.active.first)
      failure.released retry)
    (reads : BatchCutReopenObservations directory before failure.batch files input retry) :
    ∃ descriptor after, observed.AdmittedReopen (files := files) release input retry descriptor after := by
  obtain ⟨cacheAfter, returned⟩ := observed.commitUnknown
  obtain ⟨closed, dropped, _⟩ := runCloseWithFiles_handoff
    (phase := (.poisoned : Phase Installed)) (before := ⟨(cacheAfter, failure.failed), before.owners⟩)
    (by simp) ready.held
  have released : release.Observed (directory := directory)
      ((.poisoned : Phase Installed), ⟨(cacheAfter, failure.failed), before.owners⟩)
      ⟨(cacheAfter, failure.failed), failure.released.owners⟩ := by
    cases release with
    | closed => exact closed
    | references held drops last => exact dropped held drops last
  obtain ⟨fits, cut⟩ := failure.retainedCut ready
  have projected : BatchCutProjection failure.released.image
      ((writeFilesAfter (runBatchEffects before.history failure.batch failure.effects
        (before.wal.directory.staged .walBoundary))).reopenSegment before.wal.active.first
        before.history before.wal.directory.active.manifest) := by
    rw [cut]
    exact ⟨rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩⟩
  obtain ⟨descriptor, after, reopened⟩ :=
    attempts.reopensBatchCutAdmitted ready failure.prepared fits failure.effects rfl projected reads
  exact ⟨descriptor, after, ⟨cacheAfter, returned, released⟩, attempts, reopened⟩

end ObservedBatchFailure
end Alvoki.Storage.DiskSession
