import Alvoki.Storage.Disk.Proofs.Recovery.SegmentedCheckpointObservedReopen
import Alvoki.Storage.Disk.Proofs.Recovery.SegmentedCleanCachedReopen

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

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

/-- The admitted marked worker reinstalls the retained checkpoint and
history of the previous writer. The release operation has its own proof. -/
structure ReadyReopenInstallation {files : Type} {input : FilePath} {directory : DiskDirectory}
    {before : SegmentedWriterState} {retry : LockedFileState FileImage}
    {layout : CanonicalKeeperLayout retry.image before.history}
    (observed : MarkedRetryChunkReports files directory layout before.published)
    (_admission : OpenAdmissionReports input directory observed.slot) (after : SegmentedWriterState) : Prop where
  writer : CheckpointChunkWriter directory before before.published observed after
  target : after.target = before.target
  checkpoint : after.checkpoint = before.checkpoint
  generation : after.installed.generation = before.installed.generation
  replay : recoverSelected (before.checkpoint.getD (.empty, 0)).1 (WAL.encode before.history) = .ok after.installed.table

/-- The caller reports the exiting process and the slots it held at the
last ready state. The full census accounts for surviving inherited aliases. -/
structure ReadyProcessExit (inventory : DescriptorInventory) (writer : Nat) (cached : DescriptorSlot) where
  process : Nat
  lock : DescriptorSlot
  lockLive : lock ∈ inventory.slots
  lockDescription : lock.description = writer
  lockProcess : lock.reference.process = process
  cachedLive : cached ∈ inventory.slots
  cachedProcess : cached.reference.process = process

namespace ReadyProcessExit

variable {inventory : DescriptorInventory} {writer : Nat} {cached : DescriptorSlot}

theorem live (exit : ReadyProcessExit inventory writer cached) : inventory.references writer ≠ [] := by
  have member := inventory.mem_references.mpr ⟨exit.lock, exit.lockLive, rfl, exit.lockDescription⟩
  intro empty
  rw [empty] at member
  exact List.not_mem_nil member

def reached (exit : ReadyProcessExit inventory writer cached) (directory : DiskDirectory)
    (before : LockedFileState FileImage) : LockedFileState FileImage :=
  (inventory.held writer exit.live).afterFileDrops [.exited exit.process] directory before

end ReadyProcessExit

/-- The exact returned writer after a successful clean unlock and the
admitted marked open of the same lock object under a new description.
The retry trace starts at the exact released state. -/
structure AdmittedCleanReopen {files : Type} {input : FilePath} {directory : DiskDirectory}
    {oldDescriptor : Nat} {before : SegmentedWriterState}
    {retry : LockedFileState FileImage} {layout : CanonicalKeeperLayout retry.image before.history}
    (closed : CleanUnlockReports directory oldDescriptor)
    (observed : MarkedRetryChunkReports files directory layout before.published)
    (admission : OpenAdmissionReports input directory observed.slot) (after : SegmentedWriterState) : Prop
    extends ReadyReopenInstallation observed admission after where
  closeEffect : runCloseWithFiles directory oldDescriptor closed.report
    (.ready before.installed, ⟨before.files, before.owners⟩) =
    .ok () (.closed, SegmentedCleanReopenReport.released directory before)
  retries : BoundedReopenTrace directory (· = before.target) (SegmentedCleanReopenReport.released directory before) retry
  sameLock : observed.descriptors.inode observed.slot.description = closed.descriptors.inode closed.slot.description
  distinctDescription : observed.slot.description ≠ oldDescriptor

/-- Apply the admission equation to the writer's returned session. The
same return also supplies freshness relative to the reported live tokens. -/
theorem ReadyReopenInstallation.reopenEffect {files : Type} {input : FilePath} {directory : DiskDirectory}
    {before : SegmentedWriterState}
    {retry : LockedFileState FileImage} {layout : CanonicalKeeperLayout retry.image before.history}
    {observed : MarkedRetryChunkReports files directory layout before.published}
    {admission : OpenAdmissionReports input directory observed.slot} {after : SegmentedWriterState}
    (endpoint : ReadyReopenInstallation observed admission after) :
    ∃ session final, observed.runWithAdmission admission = .ok session final ∧
      session.directory = directory ∧ session.descriptor = observed.slot.description ∧
      session.phase = .ready after.installed ∧ session.sessionRef ∉ observed.liveRefs ∧
      after.files = final.image ∧ after.owners = final.owners := by
  obtain ⟨session, final, returned, path, description, phase, files, owners⟩ := endpoint.writer.reopened
  have admitted := (observed.runWithAdmission_eq admission).trans returned
  exact ⟨session, final, admitted, path, description, phase,
    (observed.admittedSessionRefs admission admitted).2.2.2, files, owners⟩

/-- Apply the admission equation to the writer's returned session. The
same return also supplies freshness relative to the reported live tokens. -/
theorem AdmittedCleanReopen.reopenEffect {files : Type} {input : FilePath} {directory : DiskDirectory}
    {oldDescriptor : Nat} {before : SegmentedWriterState}
    {retry : LockedFileState FileImage} {layout : CanonicalKeeperLayout retry.image before.history}
    {closed : CleanUnlockReports directory oldDescriptor}
    {observed : MarkedRetryChunkReports files directory layout before.published}
    {admission : OpenAdmissionReports input directory observed.slot} {after : SegmentedWriterState}
    (endpoint : AdmittedCleanReopen closed observed admission after) :
    ∃ session final, observed.runWithAdmission admission = .ok session final ∧
      session.directory = directory ∧ session.descriptor = observed.slot.description ∧
      session.phase = .ready after.installed ∧ session.sessionRef ∉ observed.liveRefs ∧
      after.files = final.image ∧ after.owners = final.owners :=
  endpoint.toReadyReopenInstallation.reopenEffect

/-- The original ready writer fixes the retained history, keeper and file
ordering of each reached retry. Preparation uses the reached image. -/
structure ClosedReadyReopenLayout (before : SegmentedWriterState) (retry : LockedFileState FileImage) where
  layout : CanonicalKeeperLayout retry.image before.history
  target : layout.target = before.target
  keeper : layout.keeper = before.wal.active
  aligned : layout.tail = ByteArray.empty
  descriptors : layout.sealed ++ [layout.keeper] = before.wal.readDescriptors layout.range.watermark
  offsets : selectWalSegmentReads (before.wal.segments.map WalSegment.first) layout.range.watermark =
    some (layout.first, (before.wal.readDescriptors layout.range.watermark).map WalSegment.first)
  prepared : Prepared retry.image layout.target layout.plan

/-- Derive the initial plan from the settled files of the closed writer. -/
theorem SegmentedWriterState.RetainedReady.cleanReopenLayout {directory writer before}
    (ready : SegmentedWriterState.RetainedReady directory writer before) :
    Nonempty (ClosedReadyReopenLayout before (SegmentedCleanReopenReport.released directory before)) := by
  have decoded : before.wal.directory.active.walRange = some before.target.range := ready.walPair.symm ▸ before.target.decoded
  have chosen := ready.layout.checkpointReopenLayout ready.valid .visible decoded ready.resumed.through before.files.keeper.staged
  dsimp only at chosen
  rw [ready.cleanFiles] at chosen
  obtain ⟨layout, range, keeper, aligned, seals, offsets, _, keeperChoices, keeperPrefix, laterValid⟩ := chosen
  rw [← range] at seals offsets laterValid
  have prepared := layout.prepared keeperChoices keeperPrefix laterValid
  have choice : CheckpointRetryTarget before.history before.wal.active.first layout.target :=
    ⟨congrArg WalSegment.first keeper, layout.through,
      by simpa only [CanonicalKeeperLayout.target, keeper] using layout.chain.keeperBytes⟩
  have original : CheckpointRetryTarget before.history before.wal.active.first before.target :=
    ⟨ready.active, ready.resumed.through, by simpa only [ready.active] using ready.resumed.contents⟩
  have sameTarget : layout.target = before.target := CheckpointRetryTarget.unique choice original ready.resumed.ready.selected
  exact ⟨⟨layout, sameTarget, keeper, aligned, seals, offsets, prepared⟩⟩

/-- Install the retained checkpoint after any retry that preserves its
selected layout and sealed files. -/
theorem SegmentedWriterState.RetainedReady.admitsReadyReopenAt {files : Type} {input : FilePath}
    {directory : DiskDirectory} {oldDescriptor : Nat} {before : SegmentedWriterState}
    (ready : before.RetainedReady directory oldDescriptor) {retry : LockedFileState FileImage}
    (selected : ClosedReadyReopenLayout before retry) (keptSeals : retry.image.kept = before.files.kept)
    (observed : MarkedRetryChunkReports files directory selected.layout before.published)
    (admission : OpenAdmissionReports input directory observed.slot) :
    ∃ after, ReadyReopenInstallation observed admission after := by
  have pair := selected.prepared.pair.trans (congrArg Target.pair selected.target)
  have accepted : before.published.AcceptsVersioned before.history.length.toUInt64
      (CheckpointRepresentsPrefix before.history) retry.image.directory.active.manifest :=
    (congrArg DirectoryPublication.Bindings.manifest pair).symm ▸ ready.resumed.accepted
  have installed := runOpenWithInstallation_markedRetryFromChunks observed selected.prepared.keeperPrefix
    selected.prepared.newer (observed.selectedAfterWatermark selected.offsets selected.descriptors)
    accepted ready.resumed.ordered
  obtain ⟨_, appended⟩ := installed.readyForAppend accepted ready.resumed.ordered
  have visible : before.wal.directory.active = selected.layout.target.pair :=
    ready.walPair.trans (congrArg Target.pair selected.target).symm
  have kept : retry.image.kept = (before.wal.checkpointReopenFiles before.wal.directory none).kept :=
    keptSeals.trans ready.sealedFiles
  obtain ⟨session, final, after, returned, path, description, phase, files, owners, wal, target, history, _, durable,
    retained⟩ := appended.writerRetained ready.layout ready.valid ready.spans visible
      (congrArg WalSegment.first selected.keeper) kept
  have output : CheckpointChunkWriter directory before before.published observed after :=
    ⟨⟨session, final, returned, path, description.trans observed.inventoryDescription, phase, files, owners⟩,
      target, selected.keeper, selected.aligned, selected.descriptors, history,
      by simpa only [files] using wal, durable, observed.inventoryDescription ▸ retained⟩
  have exactTarget := target.trans selected.target
  have checkpoint := retained.resumed.selected
  rw [exactTarget, durable] at checkpoint
  have sameCheckpoint := checkpoint.uniqueResult ready.resumed.selected
  obtain ⟨_, _, _, _, _, recovered, _, _, recoveredPhase, _, _, _, _, _, _, _, _,
    _, _, actualCheckpoint, replay, generation, _⟩ := installed
  have sameSession := (EStateM.Result.ok.inj (recovered.symm.trans returned)).1
  have exactInstalled := Phase.ready.inj (phase.symm.trans (sameSession ▸ recoveredPhase))
  have originalCheckpoint : SelectedIntegrityCheckpoint before.published.durable
      retry.image.directory.active.manifest before.checkpoint :=
    (congrArg DirectoryPublication.Bindings.manifest pair).symm ▸ ready.resumed.selected
  have chosenCheckpoint := actualCheckpoint.uniqueResult originalCheckpoint
  rw [chosenCheckpoint] at replay generation
  exact ⟨after, ⟨output, exactTarget, sameCheckpoint,
    (congrArg Installed.generation exactInstalled).trans (generation.trans ready.resumed.generation.symm),
    (congrArg Installed.table exactInstalled).symm ▸ replay⟩⟩

/-- Install the exact marked worker result at a reached clean-close retry.
The retained prepared target fixes the checkpoint, generation and replay. -/
theorem SegmentedWriterState.RetainedReady.admitsCleanReopenAt {files : Type} {input : FilePath}
    {directory : DiskDirectory} {oldDescriptor : Nat} {before : SegmentedWriterState}
    (ready : before.RetainedReady directory oldDescriptor) (closed : CleanUnlockReports directory oldDescriptor)
    {retry : LockedFileState FileImage}
    (attempts : BoundedReopenTrace directory (· = before.target) (SegmentedCleanReopenReport.released directory before) retry)
    (selected : ClosedReadyReopenLayout before retry)
    (observed : MarkedRetryChunkReports files directory selected.layout before.published)
    (admission : OpenAdmissionReports input directory observed.slot)
    (lockBinding : observed.bindings (directory.file .lock) = closed.bindings (directory.file .lock))
    (distinct : observed.slot.description ≠ oldDescriptor) :
    ∃ after, AdmittedCleanReopen closed observed admission after := by
  have closeRan : runCloseWithFiles directory oldDescriptor closed.report
      (.ready before.installed, ⟨before.files, before.owners⟩) =
        .ok () (.closed, SegmentedCleanReopenReport.released directory before) := by
    simpa only [CleanUnlockReports.report, closed.returned, SegmentedCleanReopenReport.released] using
      runCloseWithFiles_success (before := ⟨before.files, before.owners⟩)
        (show Phase.ready before.installed ≠ .closed by simp) ready.held
  have sameLock := Option.some.inj (observed.lockObject.symm.trans (lockBinding.trans closed.lockObject))
  have kept := (attempts.lineage (fun a b _ => a.trans b.symm)).keepsSealed
  obtain ⟨after, installed⟩ := ready.admitsReadyReopenAt selected kept observed admission
  exact ⟨after, ⟨installed, closeRan, attempts, sameLock, distinct⟩⟩

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
file description may reuse a numeric fd after the previous slot drops.
Keep any supplied witness for the exact admitted report and its callbacks. -/
theorem SegmentedWriterState.RetainedReady.closeWithAdmissionFromReports {files : Type} {input : FilePath}
    {directory : DiskDirectory} {oldDescriptor : Nat} {before : SegmentedWriterState}
    (ready : before.RetainedReady directory oldDescriptor) (closed : CleanUnlockReports directory oldDescriptor)
    (observedBy : ∀ {layout : CanonicalKeeperLayout (SegmentedCleanReopenReport.released directory before).image before.history}
      (observed : MarkedRetryChunkReports files directory layout before.published),
      OpenAdmissionReports input directory observed.slot → Prop)
    (observes : ∀ layout : CanonicalKeeperLayout (SegmentedCleanReopenReport.released directory before).image before.history,
      layout.keeper = before.wal.active → layout.tail = ByteArray.empty →
      layout.sealed ++ [layout.keeper] = before.wal.readDescriptors layout.range.watermark →
      ∃ (observed : MarkedRetryChunkReports files directory layout before.published)
        (admission : OpenAdmissionReports input directory observed.slot),
        observed.bindings (directory.file .lock) = closed.bindings (directory.file .lock) ∧
        observed.slot.description ≠ oldDescriptor ∧ observedBy observed admission) :
    ∃ (layout : CanonicalKeeperLayout (SegmentedCleanReopenReport.released directory before).image before.history)
      (observed : MarkedRetryChunkReports files directory layout before.published)
      (admission : OpenAdmissionReports input directory observed.slot) (after : SegmentedWriterState),
      AdmittedCleanReopen closed observed admission after ∧ observedBy observed admission := by
  obtain ⟨selected⟩ := ready.cleanReopenLayout
  obtain ⟨observed, admission, lockBinding, distinct, reported⟩ :=
    observes selected.layout selected.keeper selected.aligned selected.descriptors
  obtain ⟨after, endpoint⟩ := ready.admitsCleanReopenAt closed .empty selected observed admission lockBinding distinct
  exact ⟨selected.layout, observed, admission, after, endpoint, reported⟩

/-- A clean lock handoff derives the exact next marked session. -/
theorem SegmentedWriterState.RetainedReady.closeWithAdmission {files : Type} {input : FilePath}
    {directory : DiskDirectory} {oldDescriptor : Nat} {before : SegmentedWriterState}
    (ready : before.RetainedReady directory oldDescriptor) (closed : CleanUnlockReports directory oldDescriptor)
    (observes : closed.ReopenObservations files input before) :
    ∃ (layout : CanonicalKeeperLayout (SegmentedCleanReopenReport.released directory before).image before.history)
      (observed : MarkedRetryChunkReports files directory layout before.published)
      (admission : OpenAdmissionReports input directory observed.slot) (after : SegmentedWriterState),
      AdmittedCleanReopen closed observed admission after := by
  obtain ⟨layout, observed, admission, after, endpoint, _⟩ :=
    ready.closeWithAdmissionFromReports closed (fun _ _ => True) (by
      intro layout keeper tail seals
      obtain ⟨observed, binding, description, ⟨admission⟩⟩ := observes layout keeper tail seals
      exact ⟨observed, admission, binding, description, trivial⟩)
  exact ⟨layout, observed, admission, after, endpoint⟩

end Alvoki.Storage.DiskSession
