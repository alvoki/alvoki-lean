import Alvoki.Storage.Disk.SegmentedCheckpointObservedReopen
import Alvoki.Storage.Disk.SegmentedCleanCachedReopen

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- A successful explicit unlock of the old writer's open description.
The observation is at the unlock call and may still have live aliases.
Closing the logical writer releases ownership without dropping those slots.
`DiskTable.close.eq_def` uses the same `Phase.close` schedule and clears
the native cache references before setting the phase to closed. -/
structure CleanUnlockReports (directory : DiskDirectory) (descriptor : Nat) where
  descriptors : DescriptorInventory
  slot : DescriptorSlot
  live : slot ∈ descriptors.slots
  description : slot.description = descriptor
  bindings : FilePath → Option Nat
  lockObject : bindings (directory.file .lock) = some (descriptors.inode slot.description)
  unlock : DescriptorSlot → Except IO.Error Unit
  returned : unlock slot = .ok ()

def CleanUnlockReports.report (observed : CleanUnlockReports directory descriptor) : UnlockReport :=
  match observed.unlock observed.slot with
  | .ok () => .success
  | .error cause => .failure cause false

/-- The exact returned writer after a successful clean unlock and the
admitted marked open of the same lock object under a new description. -/
structure AdmittedCleanReopen {files : Type} {input : FilePath} {directory : DiskDirectory}
    {oldDescriptor : Nat} {before : SegmentedWriterState}
    {layout : CanonicalKeeperLayout (SegmentedCleanReopenReport.released directory before).image before.history}
    (closed : CleanUnlockReports directory oldDescriptor)
    (observed : MarkedRetryChunkReports files directory layout before.published)
    (admission : OpenAdmissionReports input directory observed.slot) (after : SegmentedWriterState) : Prop where
  closeEffect : runCloseWithFiles directory oldDescriptor closed.report
    (.ready before.installed, ⟨before.files, before.owners⟩) =
    .ok () (.closed, SegmentedCleanReopenReport.released directory before)
  sameLock : observed.descriptors.inode observed.slot.description = closed.descriptors.inode closed.slot.description
  distinctDescription : observed.slot.description ≠ oldDescriptor
  writer : CheckpointChunkWriter directory before before.published observed after
  target : after.target = before.target
  checkpoint : after.checkpoint = before.checkpoint
  generation : after.installed.generation = before.installed.generation
  replay : recoverSelected (before.checkpoint.getD (.empty, 0)).1 (WAL.encode before.history) = .ok after.installed.table

/-- Apply the admission equation to the writer's returned session. The
same return also supplies freshness relative to the reported live tokens. -/
theorem AdmittedCleanReopen.reopenEffect {files : Type} {input : FilePath} {directory : DiskDirectory}
    {oldDescriptor : Nat} {before : SegmentedWriterState}
    {layout : CanonicalKeeperLayout (SegmentedCleanReopenReport.released directory before).image before.history}
    {closed : CleanUnlockReports directory oldDescriptor}
    {observed : MarkedRetryChunkReports files directory layout before.published}
    {admission : OpenAdmissionReports input directory observed.slot} {after : SegmentedWriterState}
    (endpoint : AdmittedCleanReopen closed observed admission after) :
    ∃ session final, observed.runWithAdmission admission = .ok session final ∧
      session.directory = directory ∧ session.descriptor = observed.slot.description ∧
      session.phase = .ready after.installed ∧ session.sessionRef ∉ observed.liveRefs ∧
      after.files = final.image ∧ after.owners = final.owners := by
  obtain ⟨session, final, returned, path, description, phase, files, owners⟩ := endpoint.writer.reopened
  have admitted := (observed.runWithAdmission_eq admission).trans returned
  exact ⟨session, final, admitted, path, description, phase,
    (observed.admittedSessionRefs admission admitted).2.2.2, files, owners⟩

/-- The reached marked-open observations for the canonical retained layout
and the same lock object as the successful explicit unlock. -/
abbrev CleanUnlockReports.ReopenObservations (closed : CleanUnlockReports directory oldDescriptor)
    (files : Type) (input : FilePath) (before : SegmentedWriterState) : Prop :=
  ∀ layout : CanonicalKeeperLayout (SegmentedCleanReopenReport.released directory before).image before.history,
    layout.keeper = before.wal.active → layout.tail = ByteArray.empty →
    layout.sealed ++ [layout.keeper] = before.wal.readDescriptors layout.range.watermark →
    ∃ observed : MarkedRetryChunkReports files directory layout before.published,
      observed.bindings (directory.file .lock) = closed.bindings (directory.file .lock) ∧
      observed.slot.description ≠ oldDescriptor ∧ Nonempty (OpenAdmissionReports input directory observed.slot)

/-- Derive the lookup and recovery plan from the old writer's settled
physical layout. The callback packets come from the same canonical lock
object at explicit unlock and later acquisition. A newly opened
file description may reuse a numeric fd after the previous slot drops. -/
theorem SegmentedWriterState.RetainedReady.closeWithAdmission {files : Type} {input : FilePath}
    {directory : DiskDirectory} {oldDescriptor : Nat} {before : SegmentedWriterState}
    (ready : before.RetainedReady directory oldDescriptor) (closed : CleanUnlockReports directory oldDescriptor)
    (observes : closed.ReopenObservations files input before) :
    ∃ (layout : CanonicalKeeperLayout (SegmentedCleanReopenReport.released directory before).image before.history)
      (observed : MarkedRetryChunkReports files directory layout before.published)
      (admission : OpenAdmissionReports input directory observed.slot) (after : SegmentedWriterState),
      AdmittedCleanReopen closed observed admission after := by
  let released := SegmentedCleanReopenReport.released directory before
  have closeRan : runCloseWithFiles directory oldDescriptor closed.report
      (.ready before.installed, ⟨before.files, before.owners⟩) = .ok () (.closed, released) := by
    simpa only [CleanUnlockReports.report, closed.returned, released, SegmentedCleanReopenReport.released] using
      runCloseWithFiles_success (before := ⟨before.files, before.owners⟩) (show Phase.ready before.installed ≠ .closed by simp)
        ready.held
  have decoded : before.wal.directory.active.walRange = some before.target.range := ready.walPair.symm ▸ before.target.decoded
  have chosen := ready.layout.checkpointReopenLayout ready.valid .visible decoded ready.resumed.through before.files.keeper.staged
  dsimp only at chosen
  rw [ready.cleanFiles] at chosen
  obtain ⟨layout, range, keeper, aligned, seals, offsets, _, keeperChoices, keeperPrefix, laterValid⟩ := chosen
  rw [← range] at seals offsets laterValid
  obtain ⟨observed, lockBinding, distinct, ⟨admission⟩⟩ := observes layout keeper aligned seals
  have sameLock := Option.some.inj (observed.lockObject.symm.trans (lockBinding.trans closed.lockObject))
  have prepared := layout.prepared keeperChoices keeperPrefix laterValid
  have choice : CheckpointRetryTarget before.history before.wal.active.first layout.target :=
    ⟨congrArg WalSegment.first keeper, layout.through,
      by simpa only [CanonicalKeeperLayout.target, keeper] using layout.chain.keeperBytes⟩
  have original : CheckpointRetryTarget before.history before.wal.active.first before.target :=
    ⟨ready.active, ready.resumed.through, by simpa only [ready.active] using ready.resumed.contents⟩
  have sameTarget : layout.target = before.target := CheckpointRetryTarget.unique choice original ready.resumed.ready.selected
  have accepted : before.published.AcceptsVersioned before.history.length.toUInt64
      (WAL.Boundary.CheckpointRepresentsPrefix before.history) released.image.directory.active.manifest :=
    (congrArg DirectoryPublication.Bindings.manifest ready.resumed.ready.selected).symm ▸ ready.resumed.accepted
  have installed := runOpenWithInstallation_markedRetryFromChunks observed prepared.keeperPrefix prepared.newer
    (observed.selectedAfterWatermark offsets seals) accepted ready.resumed.ordered
  obtain ⟨_, _, opened, _, _, _, recovered, _, _, phase, _, _, _, _, _, _, _, _, replayed,
    generation, _⟩ := ready.closeThenCachedReopen closeRan observed.reported observed.descriptors observed.slot
      observed.bindings observed.liveRefs installed
  obtain ⟨_, appended⟩ := installed.readyForAppend accepted ready.resumed.ordered
  have visible : before.wal.directory.active = layout.target.pair := congrArg Target.pair sameTarget ▸ ready.walPair
  obtain ⟨session, files, after, returned, path, description, installedPhase, afterFiles, owners, wal, target,
    history, _, durable, retained⟩ := appended.writerRetained ready.layout ready.valid ready.spans visible
      (congrArg WalSegment.first keeper) ready.sealedFiles
  have exactTarget := target.trans sameTarget
  have readyAfter : after.RetainedReady directory observed.slot.description := observed.inventoryDescription ▸ retained
  have output : CheckpointChunkWriter directory before before.published observed after :=
    ⟨⟨session, files, returned, path, description.trans observed.inventoryDescription, installedPhase, afterFiles, owners⟩,
      target, keeper, aligned, seals, history, by simpa only [afterFiles] using wal, durable, readyAfter⟩
  have selected := retained.resumed.selected
  rw [exactTarget, durable] at selected
  have checkpoint := selected.uniqueResult ready.resumed.selected
  have exactInstalled := Phase.ready.inj ((output.atReopen recovered).1.symm.trans phase)
  exact ⟨layout, observed, admission, after, closeRan, sameLock, distinct, output,
    exactTarget, checkpoint, (congrArg Installed.generation exactInstalled).trans generation,
    (congrArg Installed.table exactInstalled).symm ▸ replayed⟩

end Alvoki.Storage.DiskSession
