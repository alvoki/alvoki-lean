import Alvoki.Storage.Disk.Proofs.Session.DiskOpenAdmission
import Alvoki.Storage.Disk.Proofs.Recovery.SegmentedReadyPowerLoss
import Alvoki.Storage.Disk.Proofs.Collection.SegmentedRunCollection

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair CheckpointPublication

/-- Observe the run namespace and the WAL/manifest survivors from the same
power loss during a checked obsolete-run pass. The executed prefix can
include the interrupted callback when its effect was already reached.
The collection callbacks affect only run names and their durability.
The old writer's settled WAL and manifest observations use its file image. -/
structure SegmentedRunCollectionPowerLoss {directory : DiskDirectory} {before : SegmentedWriterState}
    {runs : RunUnlinkImage} (reports : SegmentedRunCollectionReports directory before runs) where
  cut : Nat
  survivingRuns : RunFiles
  runsSurvive : survivingRuns ∈ (((RunCollection.steps reports.selected).take cut).foldl
    RunUnlinkImage.applyCollectionStep runs).crashImages
  pair : DirectoryPublication.Bindings
  pairSurvives : pair ∈ before.files.directory.crashImages
  keeper : Option ByteArray
  keeperSurvives : keeper ∈ before.files.keeper.crashImages
  later : List Nat
  laterSurvives : later ∈ before.files.later.crashImages

namespace SegmentedRunCollectionPowerLoss

variable {directory : DiskDirectory} {before : SegmentedWriterState} {runs : RunUnlinkImage}
  {reports : SegmentedRunCollectionReports directory before runs}

def crashed (loss : SegmentedRunCollectionPowerLoss reports) : LockedFileState FileImage :=
  ⟨before.files.crash loss.pair loss.keeper loss.later, before.owners.set (directory.file .lock) none⟩

def published (loss : SegmentedRunCollectionPowerLoss reports) : CheckpointPublication.Image :=
  { before.published with durable := loss.survivingRuns }

private theorem exactWal {writer : Nat} (loss : SegmentedRunCollectionPowerLoss reports)
    (ready : before.RetainedReady directory writer) :
    loss.crashed = before.powerLossFiles directory := by
  have pairSurvives := loss.pairSurvives
  have keeperSurvives := loss.keeperSurvives
  have laterSurvives := loss.laterSurvives
  rw [ready.resumed.ready.settled] at pairSurvives
  rw [ready.resumed.ready.keeperDurable] at keeperSurvives
  rw [ready.resumed.ready.pruned.2] at laterSurvives
  simp only [crashed, SegmentedWriterState.powerLossFiles, List.mem_singleton.mp pairSurvives,
    List.mem_singleton.mp keeperSurvives, List.mem_singleton.mp laterSurvives]

/-- The final marked read reports identify the exact runs of the observed
crash and the selected canonical WAL layout after any bounded retries.
The stable owned namespace contract applies between the crash and reads. -/
abbrev ReopenObservations (loss : SegmentedRunCollectionPowerLoss reports)
    (files : Type) (input : FilePath) (retry : LockedFileState FileImage) : Prop :=
  ∀ layout : CanonicalKeeperLayout retry.image before.history, layout.target = before.target →
    layout.keeper = before.wal.active →
    ∃ observed : MarkedRetryChunkReports files directory layout loss.published,
      Nonempty (OpenAdmissionReports input directory observed.slot)

/-- The admitted native reopen installs the observed run map with the
unchanged marked WAL. The result explicitly identifies the returned
session, reached image and writer under the new description. -/
structure Installs {files : Type} (loss : SegmentedRunCollectionPowerLoss reports)
    (input : FilePath) (retry : LockedFileState FileImage) (descriptor : Nat) (after : SegmentedWriterState) : Prop where
  runCut : RunUnlinkRetry reports.selected runs (.settled loss.survivingRuns)
  walRetries : BoundedReopenTrace directory (fun target => target = before.target) ⟨before.files, before.owners⟩ retry
  selected : SelectedIntegrityCheckpoint loss.survivingRuns before.target.pair.manifest before.checkpoint
  reopened : ∃ (layout : CanonicalKeeperLayout retry.image before.history)
    (observed : MarkedRetryChunkReports files directory layout loss.published)
    (admission : OpenAdmissionReports input directory observed.slot)
    (session : SegmentedSession) (final : LockedFileState FileImage),
    observed.runWithAdmission admission = .ok session final ∧
    session.directory = directory ∧ session.descriptor = descriptor ∧ session.phase = .ready after.installed ∧
    final.owners.Owns directory descriptor ∧ final.image.Ready before.target ∧
    after.files = final.image ∧ after.owners = final.owners
  checkpoint : after.checkpoint = before.checkpoint
  target : after.target = before.target
  history : after.history = before.history
  generation : after.installed.generation = before.installed.generation
  durable : after.published.durable = loss.survivingRuns
  replay : recoverSelected (before.checkpoint.getD (.empty, 0)).1 (WAL.encode before.history) = .ok after.installed.table
  retained : after.RetainedReady directory descriptor
  sealedWal : after.wal.sealed = before.wal.sealed

/-- Carry the reached collection cut through the shared cached recovery
layout selection and admitted opener. Neither the returned table nor a
successful open result is assumed. -/
theorem reopensAdmitted {files : Type} {input : FilePath} {retry : LockedFileState FileImage} {writer : Nat}
    (loss : SegmentedRunCollectionPowerLoss reports) (ready : before.RetainedReady directory writer)
    (attempts : BoundedReopenTrace directory (fun target => target = before.target) loss.crashed retry)
    (reads : loss.ReopenObservations files input retry) :
    ∃ descriptor after, loss.Installs (files := files) input retry descriptor after := by
  have ⟨runCut, chosenRuns⟩ := reports.crashAtCut ready (.start runs) (fun _ chosen => chosen)
    loss.cut loss.runsSurvive
  have older : ∀ address ∈ reports.selected, address.1 < before.installed.generation := by
    rintro ⟨generation, index⟩ member
    exact ((reports.selected_eligible ready).mp member).2.1
  have survivorMap : (RunUnlinkImage.settled loss.survivingRuns).guaranteed = loss.survivingRuns :=
    congrArg Image.durable (RunUnlinkImage.project_settled loss.survivingRuns before.published.manifest)
  have projected := survivorMap ▸ (ready.afterRunCollection runCut older reports.known).1
  have source := ready.powerLossLayout
  rw [← loss.exactWal ready] at source
  obtain ⟨layout, sameTarget, sameKeeper, seals, offsets, prepared⟩ := source
  have fixed : loss.crashed.image.syncDirectory = loss.crashed.image := by rw [loss.exactWal ready]; rfl
  have effects := (sameTarget.symm ▸ attempts :
    BoundedReopenTrace directory (fun target => target = layout.target) loss.crashed retry).effectsAfterFixedAuthority fixed
  obtain ⟨nextLayout, target, range, first, sameSeals, keeper, kept, retryPrepared⟩ :=
    effects.canonicalRetryLayout layout prepared
  have exactTarget := target.trans sameTarget
  have exactKeeper := keeper.trans sameKeeper
  have descriptors : nextLayout.sealed ++ [nextLayout.keeper] = before.wal.readDescriptors nextLayout.range.watermark := by
    rw [sameSeals, keeper, range]
    exact seals
  have positions : selectWalSegmentReads (before.wal.segments.map WalSegment.first) nextLayout.range.watermark =
      some (nextLayout.first, (before.wal.readDescriptors nextLayout.range.watermark).map WalSegment.first) := by
    rw [range, first]
    exact offsets
  have checked : Prepared retry.image nextLayout.target nextLayout.plan := target.symm ▸ retryPrepared
  have accepted := (congrArg (fun selected : Target => selected.pair.manifest) exactTarget).symm ▸ projected.resumed.accepted
  obtain ⟨observed, ⟨admission⟩⟩ := reads nextLayout exactTarget exactKeeper
  have installed := runOpenWithAdmission_markedRetryFromChunks observed admission checked.keeperPrefix checked.newer
    (observed.selectedAfterWatermark positions descriptors) accepted ready.resumed.ordered
  obtain ⟨_, appendReady⟩ := installed.readyForAppend accepted ready.resumed.ordered
  have visible := ready.walPair.trans (congrArg Target.pair exactTarget).symm
  have oldSeals : loss.crashed.image.kept = before.files.kept := rfl
  obtain ⟨session, final, after, returned, directoryExact, lock, phase, files, owners, wal, chosen,
    history, _, durable, retained⟩ := appendReady.writerRetained ready.layout ready.valid ready.spans visible
      (congrArg WalSegment.first exactKeeper) ((kept.trans oldSeals).trans ready.sealedFiles)
  have target := chosen.trans exactTarget
  have afterReady : after.RetainedReady directory observed.slot.description := observed.inventoryDescription ▸ retained
  have loaded := afterReady.resumed.selected
  rw [target, durable] at loaded
  have sameCheckpoint := loaded.uniqueResult chosenRuns
  have generation : after.installed.generation = before.installed.generation := by
    rw [afterReady.resumed.generation, sameCheckpoint, ← ready.resumed.generation]
  have finalReady := afterReady.resumed.ready
  rw [target, files] at finalReady
  obtain ⟨opened, checkpoint, _, reopened, reached, ran, _, _, installedPhase, _, _, _, _, _, _, _, _, _, _,
    selected, replayed, _⟩ := installed
  have sameSession := (EStateM.Result.ok.inj (ran.symm.trans returned)).1
  have sameInstalled := Phase.ready.inj ((sameSession ▸ installedPhase).symm.trans phase)
  change SelectedIntegrityCheckpoint loss.survivingRuns nextLayout.target.pair.manifest checkpoint at selected
  rw [exactTarget] at selected
  have checkpointMatches := selected.uniqueResult chosenRuns
  have replay : recoverSelected (before.checkpoint.getD (.empty, 0)).1 (WAL.encode before.history) =
      .ok after.installed.table := by
    rw [checkpointMatches] at replayed
    exact replayed.trans (congrArg Except.ok (congrArg Installed.table sameInstalled))
  have lost : BoundedReopenTrace directory (fun target => target = before.target) ⟨before.files, before.owners⟩
      loss.crashed := .powerLoss .empty loss.pairSurvives loss.keeperSurvives loss.laterSurvives
  have sealedWal := congrArg WalSegmentImage.sealed wal
  exact ⟨observed.slot.description, after, runCut, lost.trans attempts, chosenRuns,
    ⟨nextLayout, observed, admission, session, final, returned, directoryExact, lock.trans observed.inventoryDescription,
      phase, owners ▸ afterReady.held, finalReady, files, owners⟩,
    sameCheckpoint, target, history, generation, durable, replay, afterReady, sealedWal⟩

end SegmentedRunCollectionPowerLoss
end Alvoki.Storage.DiskSession
