import Alvoki.Storage.Disk.DiskOpenAdmission
import Alvoki.Storage.Disk.SegmentedBatchAppendPowerLoss
import Alvoki.Storage.Disk.WalBatchAppendProcessExit

namespace Alvoki.Storage.DiskSession.BatchAppendInterruption

open System WalSegmentRepair WAL.Boundary

variable {directory : DiskDirectory} {before : SegmentedWriterState}
  {report : BatchAppendInterruption directory before} {writer : Nat}

/-- A power loss chooses a surviving tail. A process exit starts retries
with the live bytes and drops only the observed process's lock references. -/
inductive Stop (report : BatchAppendInterruption directory before) (writer : Nat) where
  | powerLoss (tail : ByteArray) (survives : tail ∈ ByteArray.empty :: report.cut.crashTails)
  | processExit (references : HeldLockReferences writer) (process : Nat)

def Stop.origin (stop : report.Stop writer) : LockedFileState FileImage :=
  match stop with
  | .powerLoss tail _ => report.cut.crashed before directory tail
  | .processExit references process =>
    references.afterFileDrops [.exited process] directory ⟨report.cut.physical before, before.owners⟩

/-- Neither stop can change the authority of the already settled marker.
The source layout includes the observed tail of the selected keeper. -/
private theorem Stop.priorAuthority (stop : report.Stop writer) (ready : before.RetainedReady directory writer) :
    BoundedReopenTrace directory (fun target => target = before.target)
      ⟨report.cut.physical before, before.owners⟩ stop.origin ∧
    stop.origin.image.syncDirectory = stop.origin.image ∧ stop.origin.image.kept = before.files.kept ∧
    ∃ source : CanonicalKeeperLayout stop.origin.image before.history,
      source.target = before.target ∧ source.keeper = before.wal.active ∧
      source.sealed ++ [source.keeper] = before.wal.readDescriptors source.range.watermark ∧
      selectWalSegmentReads (before.wal.segments.map WalSegment.first) source.range.watermark =
        some (source.first, (before.wal.readDescriptors source.range.watermark).map WalSegment.first) ∧
      Prepared stop.origin.image source.target source.plan := by
  cases stop with
  | powerLoss tail survives =>
    exact ⟨report.cut.powersOff ready _ survives, rfl, rfl, report.cut.crashedLayout ready tail⟩
  | processExit references process =>
    have stopped := (report.cut.batchProcessExit ready report.batch references process).1
    obtain ⟨fixed, _, source, target, keeper, _, descriptors, offsets, prepared⟩ :=
      report.cut.liveLayout ready
    exact ⟨stopped, fixed, rfl, source, target, keeper, descriptors, offsets, prepared⟩

abbrev ReopenObservations (directory : DiskDirectory) (before : SegmentedWriterState)
    (files : Type) (input : FilePath) (retry : LockedFileState FileImage) : Prop :=
  ∀ layout : CanonicalKeeperLayout retry.image before.history, layout.target = before.target →
    ∃ reported : MarkedRetryChunkReports files directory layout before.published,
      Nonempty (OpenAdmissionReports input directory reported.slot)

/-- The successful reopen continues from the same interrupted operation
and the reported finite retry lineage. Its installed phase comes from
the admitted open under the exact append-opened lock description. -/
structure AdmittedReopen {files : Type} (report : BatchAppendInterruption directory before)
    {writer : Nat} (stop : report.Stop writer) (input : FilePath) (retry : LockedFileState FileImage) (descriptor : Nat)
    (after : SegmentedWriterState) : Prop where
  valid : report.Valid
  reached : report.ReachesInterruption writer
  stopped : BoundedReopenTrace directory (fun target => target = before.target)
    ⟨report.cut.physical before, before.owners⟩ stop.origin
  retries : BoundedReopenTrace directory (fun target => target = before.target)
    stop.origin retry
  reopened : ∃ (layout : CanonicalKeeperLayout retry.image before.history)
    (reported : MarkedRetryChunkReports files directory layout before.published)
    (admission : OpenAdmissionReports input directory reported.slot) (session : SegmentedSession)
    (final : LockedFileState FileImage),
    reported.runWithAdmission admission = .ok session final ∧
    session.directory = directory ∧ session.descriptor = descriptor ∧ session.phase = .ready after.installed ∧
    final.owners.Owns directory descriptor ∧ after.files = final.image ∧ after.owners = final.owners ∧
    final.image.Ready before.target
  target : after.target = before.target
  history : after.history = before.history
  checkpoint : after.checkpoint = before.checkpoint
  generation : after.installed.generation = before.installed.generation
  durable : after.published.durable = before.published.durable
  retained : after.RetainedReady directory descriptor

/-- After either first-append stop and any admitted retries, the marked
opener installs the prior checkpoint and committed WAL from the exact
selected reads. Any physical tail lies beyond the old marker. -/
theorem Stop.reopensAdmitted {files : Type} {input : FilePath} {retry : LockedFileState FileImage}
    (stop : report.Stop writer) (observed : report.Valid) (ready : before.RetainedReady directory writer)
    (attempts : BoundedReopenTrace directory (fun target => target = before.target) stop.origin retry)
    (reads : ReopenObservations directory before files input retry) :
    ∃ descriptor after, report.AdmittedReopen (files := files) stop input retry descriptor after := by
  obtain ⟨stopped, fixed, oldSealed, source, target, keeper, descriptors, offsets, prepared⟩ :=
    stop.priorAuthority ready
  have effects := (target.symm ▸ attempts :
    BoundedReopenTrace directory (fun candidate => candidate = source.target) stop.origin retry)
    |>.effectsAfterFixedAuthority fixed
  obtain ⟨layout, chosen, range, first, sealed, active, kept, nextPrepared⟩ :=
    effects.canonicalRetryLayout source prepared
  have sameTarget := chosen.trans target
  obtain ⟨reported, ⟨admission⟩⟩ := reads layout sameTarget
  have exactDescriptors : layout.sealed ++ [layout.keeper] = before.wal.readDescriptors layout.range.watermark := by
    rw [sealed, active, range]
    exact descriptors
  have exactOffsets : selectWalSegmentReads (before.wal.segments.map WalSegment.first) layout.range.watermark =
      some (layout.first, (before.wal.readDescriptors layout.range.watermark).map WalSegment.first) := by
    rw [range, first]
    exact offsets
  have accepted := (congrArg (fun chosen : Target => chosen.pair.manifest) sameTarget).symm ▸ ready.resumed.accepted
  have preparedLayout : Prepared retry.image layout.target layout.plan := chosen.symm ▸ nextPrepared
  have installed := runOpenWithAdmission_markedRetryFromChunks reported admission
    preparedLayout.keeperPrefix preparedLayout.newer
    (reported.selectedAfterWatermark exactOffsets exactDescriptors) accepted ready.resumed.ordered
  obtain ⟨_, appendReady⟩ := installed.readyForAppend accepted ready.resumed.ordered
  have visible := ready.walPair.trans (congrArg Target.pair sameTarget).symm
  have firstKeeper := (congrArg WalSegment.first (active.trans keeper) : layout.target.first = before.wal.active.first)
  obtain ⟨session, final, after, returned, path, lock, phase, files, owners, _, selected, history, _, durable, next⟩ :=
    appendReady.writerRetained ready.layout ready.valid ready.spans visible firstKeeper
      ((kept.trans oldSealed).trans ready.sealedFiles)
  have nextReady : after.RetainedReady directory reported.slot.description := reported.inventoryDescription ▸ next
  have exactTarget := selected.trans sameTarget
  have loaded := nextReady.resumed.selected
  rw [exactTarget, durable] at loaded
  have checkpoint := loaded.uniqueResult ready.resumed.selected
  have generation : after.installed.generation = before.installed.generation := by
    rw [nextReady.resumed.generation, checkpoint, ← ready.resumed.generation]
  have finalReady : final.image.Ready before.target := by
    rw [← files, ← exactTarget]
    exact nextReady.resumed.ready
  exact ⟨reported.slot.description, after, observed, observed.reachesInterruption ready, stopped, attempts,
    ⟨layout, reported, admission, session, final, returned, path, lock.trans reported.inventoryDescription, phase,
      owners ▸ nextReady.held, files, owners, finalReady⟩,
    exactTarget, history, checkpoint, generation, durable, nextReady⟩

end Alvoki.Storage.DiskSession.BatchAppendInterruption
