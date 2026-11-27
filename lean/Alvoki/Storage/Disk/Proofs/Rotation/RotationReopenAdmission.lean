import Alvoki.Storage.Disk.Proofs.Rotation.WalSegmentRotationPowerLoss
import Alvoki.Storage.Disk.Proofs.WAL.WalSegmentCheckpointRetryLayout
import Alvoki.Storage.Disk.Proofs.Session.DiskOpenAdmission
import Alvoki.Storage.Disk.Proofs.Write.RetainedWriterReopen

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WalSegmentRotation
open WAL (frameSize)

/-- Project the observed crash to a fixed keeper only after the empty
successor's presence has been chosen. -/
def RotationInFlightCut.crashedFiles {directory : DiskDirectory} {before : SegmentedWriterState}
    (cut : RotationInFlightCut directory before) (pair : DirectoryPublication.Bindings) (present : Bool) :
    LockedFileState FileImage :=
  let crashed := cut.released pair present
  ⟨crashed.image.settledReopenImage before.wal, crashed.owners⟩

/-- The WAL selected by the observed presence or absence of the successor. -/
def RotationInFlightCut.survivingWal {directory : DiskDirectory} {before : SegmentedWriterState}
    (cut : RotationInFlightCut directory before) (pair : DirectoryPublication.Bindings) (present : Bool) : WalSegmentImage :=
  (cut.released pair present).image.settleForReopen.visible before.wal

abbrev RotationInFlightCut.ReopenObservations {directory : DiskDirectory} {before : SegmentedWriterState}
    (cut : RotationInFlightCut directory before) (pair : DirectoryPublication.Bindings) (present : Bool)
    (files : Type) (input : FilePath) (retry : LockedFileState FileImage) : Prop :=
  let wal := cut.survivingWal pair present
  ∀ layout : CanonicalKeeperLayout retry.image before.history,
    layout.keeper = wal.active → layout.target.pair = before.target.pair →
    layout.sealed ++ [layout.keeper] = wal.readDescriptors layout.range.watermark →
    ∃ observed : MarkedRetryChunkReports files directory layout before.published,
      Nonempty (OpenAdmissionReports input directory observed.slot)

/-- The observed power-loss choice and later retries yield an exact
admitted marked return for the next writer. -/
structure RotationInFlightCut.AdmittedReopen {directory : DiskDirectory} {before : SegmentedWriterState} {files : Type}
    (cut : RotationInFlightCut directory before) (pair : DirectoryPublication.Bindings) (present : Bool)
    (input : FilePath) (retry : LockedFileState FileImage) (descriptor : Nat) (after : SegmentedWriterState) : Prop where
  metadata : pair ∈ cut.image.metadata.crashImages
  successor : cut.image.successor.MaySurvive present
  retries : BoundedReopenTrace directory (CheckpointRetryTarget before.history (cut.survivingWal pair present).active.first)
    (cut.crashedFiles pair present) retry
  reopened : ∃ (layout : CanonicalKeeperLayout retry.image before.history)
    (observed : MarkedRetryChunkReports files directory layout before.published)
    (admission : OpenAdmissionReports input directory observed.slot)
    (session : SegmentedSession) (final : LockedFileState FileImage),
    observed.slot.description = descriptor ∧ observed.runWithAdmission admission = .ok session final ∧
    session.directory = directory ∧ session.descriptor = descriptor ∧ session.phase = .ready after.installed ∧
    final.owners.Owns directory session.descriptor ∧ after.files = final.image ∧ after.owners = final.owners ∧
    after.wal = { cut.survivingWal pair present with directory := final.image.directory }
  pairPreserved : after.target.pair = before.target.pair
  history : after.history = before.history
  checkpoint : after.checkpoint = before.checkpoint
  generation : after.installed.generation = before.installed.generation
  durable : after.published.durable = before.published.durable
  retained : after.RetainedReady directory descriptor

/-- A settled rotation survivor starts a fixed-keeper effects trace. -/
theorem BoundedReopenTrace.rotationRetryEffects {directory : DiskDirectory} {history : List WAL.Write} {first : Nat}
    {initial retry : LockedFileState FileImage} {target : Target} {plan : Plan}
    (attempts : BoundedReopenTrace directory (CheckpointRetryTarget history first) initial retry)
    (admitted : CheckpointRetryTarget history first target) (prepared : Prepared initial.image target plan)
    (fixed : initial.image.syncDirectory = initial.image) : EffectTrace target initial.image retry.image := by
  have initialTrace : EffectTrace target initial.image initial.image := fixed ▸ .authorized
  have observed {current : FileImage} (before : BeforeReopenBarrier initial.image current) :
      EffectTrace target initial.image current := by
    cases before with
    | live => exact initialTrace
    | crash _ _ _ pair keeper names => exact .crash initialTrace pair keeper names
  cases attempts.lineage (fun left right same => CheckpointRetryTarget.unique left right same) with
  | before source => exact observed source
  | repairing source checked retryPlan applied =>
    have previous := observed source
    have pair := (previous.valid prepared.pair prepared.keeperPrefix prepared.newer).selected
    have same := CheckpointRetryTarget.unique admitted checked (pair.symm.trans retryPlan.pair)
    exact previous.trans (same.symm ▸ applied)

/-- An observed rotation crash chooses the old keeper or the empty
successor before any fixed-keeper retry. Healthy admission and chunk
reports at the reached retry install that exact layout under the acquired
description and preserve the original checkpoint and retained history. -/
theorem RotationInFlightCut.reopensAdmitted {directory : DiskDirectory} {before : SegmentedWriterState}
    {files : Type} {writer : Nat} {input : FilePath}
    (cut : RotationInFlightCut directory before) (ready : before.RetainedReady directory writer)
    {pair : DirectoryPublication.Bindings} {present : Bool} (metadata : pair ∈ cut.image.metadata.crashImages)
    (survives : cut.image.successor.MaySurvive present) (retry : LockedFileState FileImage)
    (attempts : BoundedReopenTrace directory (CheckpointRetryTarget before.history (cut.survivingWal pair present).active.first)
      (cut.crashedFiles pair present) retry)
    (reads : cut.ReopenObservations pair present files input retry) :
    ∃ descriptor after, cut.AdmittedReopen (files := files) pair present input retry descriptor after := by
  let crashed := cut.released pair present
  let source := cut.crashedFiles pair present
  let wal := crashed.image.settleForReopen.visible before.wal
  have loss : WalSegmentRotation.Trace before.wal crashed.image := .crash cut.trace pair metadata survives
  have oldPair := cut.trace.selectsOriginal (List.mem_cons_of_mem _ metadata)
  have oldBinding : pair = before.wal.directory.active := by
    simpa [WalSegmentImage.Selects, ready.walDirectorySettled] using oldPair
  have samePair := oldBinding.trans ready.walPair
  have decoded : crashed.image.metadata.active.walRange = some before.target.range := by
    change pair.walRange = some before.target.range
    rw [samePair]
    exact before.target.decoded
  obtain ⟨layout, valid, _, sourcePair, chosen, chosenRange, keeper, _, descriptors, offsets, prepared⟩ :=
    loss.settledReopenLayout (ready.rotationInput cut.nonempty) ready.layout ready.valid decoded ready.resumed.through
  have authority : CheckpointRetryTarget before.history wal.active.first chosen.target := by
    refine ⟨congrArg WalSegment.first keeper, chosen.through, ?_⟩
    simpa only [CanonicalKeeperLayout.target, keeper] using chosen.chain.keeperBytes
  have effects := attempts.rotationRetryEffects authority prepared (crashed.image.settledReopenImage_sync before.wal)
  obtain ⟨selected, target, range, first, seals, active, kept, retryPrepared⟩ := effects.canonicalRetryLayout chosen prepared
  have sourceTarget := prepared.pair.symm.trans (sourcePair.trans samePair)
  have pairAtRetry := retryPrepared.pair.trans sourceTarget
  have exactKeeper := active.trans keeper
  have exactDescriptors : selected.sealed ++ [selected.keeper] = wal.readDescriptors selected.range.watermark := by
    rw [seals, active, range, chosenRange]
    exact descriptors
  have exactOffsets : selectWalSegmentReads (wal.segments.map WalSegment.first) selected.range.watermark =
      some (selected.first, (wal.readDescriptors selected.range.watermark).map WalSegment.first) := by
    rw [range, chosenRange, first]
    exact offsets
  have finalTarget := (congrArg Target.pair target).trans sourceTarget
  have accepted := (congrArg DirectoryPublication.Bindings.manifest pairAtRetry).symm ▸ ready.resumed.accepted
  have checked : Prepared retry.image selected.target selected.plan := target.symm ▸ retryPrepared
  obtain ⟨observed, ⟨admission⟩⟩ := reads selected exactKeeper finalTarget exactDescriptors
  have installed := runOpenWithAdmission_markedRetryFromChunks observed admission checked.keeperPrefix checked.newer
    (observed.selectedAfterWatermark exactOffsets exactDescriptors) accepted ready.resumed.ordered
  obtain ⟨_, appendReady⟩ := installed.readyForAppend accepted ready.resumed.ordered
  have visible : wal.directory.active = selected.target.pair :=
    (show wal.directory.active = source.image.directory.active from rfl).trans
      (prepared.pair.trans (congrArg Target.pair target).symm)
  have spans : ∀ segment ∈ wal.sealed, segment.bytes.size = (segment.last - segment.first) * frameSize := by
    have allSegments : ∀ segment ∈ before.wal.segments,
        segment.bytes.size = (segment.last - segment.first) * frameSize := by
      intro segment included
      rcases List.mem_append.mp included with sealed | active
      · exact ready.spans segment sealed
      · obtain rfl := List.mem_singleton.mp active
        rw [ready.layout.activeBytes, WAL.encode_size, List.length_drop, ready.layout.activeEnd, Nat.mul_comm]
    intro segment included
    have layoutChoice := WalSegmentRotation.State.crashReopenLayout before.wal pair present
    change wal = (if present then { before.wal with directory := .settled pair }.rotated
      else { before.wal with directory := .settled pair }) at layoutChoice
    rw [layoutChoice] at included
    cases present with
    | false => exact ready.spans segment (by simpa using included)
    | true =>
      exact allSegments segment (by simpa [WalSegmentImage.rotated, WalSegmentImage.segments] using included)
  obtain ⟨session, final, after, returned, path, slot, phase, files, owners, nextWal, nextTarget, history, _, durable, next⟩ :=
    appendReady.writerRetained layout valid spans visible (congrArg WalSegment.first exactKeeper) kept
  have retained : after.RetainedReady directory observed.slot.description := observed.inventoryDescription ▸ next
  have afterPair := (congrArg Target.pair nextTarget).trans finalTarget
  have selectedCheckpoint := retained.resumed.selected
  rw [afterPair, durable] at selectedCheckpoint
  have checkpoint := selectedCheckpoint.uniqueResult ready.resumed.selected
  have generation : after.installed.generation = before.installed.generation := by
    rw [retained.resumed.generation, checkpoint, ← ready.resumed.generation]
  exact ⟨observed.slot.description, after, metadata, survives, attempts,
    ⟨selected, observed, admission, session, final, rfl, returned, path, slot.trans observed.inventoryDescription,
      phase, slot ▸ (owners ▸ next.held), files, owners, nextWal⟩,
    afterPair, history, checkpoint, generation, durable, retained⟩

end Alvoki.Storage.DiskSession
