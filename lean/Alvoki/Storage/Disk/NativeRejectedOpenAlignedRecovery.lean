import Alvoki.Storage.Disk.NativeExecutionClose
import Alvoki.Storage.Disk.Proofs.Recovery.NativeRejectedOpenLineage

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

private theorem NativeOpenErrorUnlock.keepsOtherLock
    {admission : CensusOpenAdmissionReports input directory inventory retry}
    (cleanup : NativeOpenErrorUnlock admission census) {path : FilePath}
    (other : path ≠ directory.file .lock) :
    cleanup.files.owners path = retry.owners path := by
  cases outcome : cleanup.result <;>
    simp [NativeOpenErrorUnlock.files, outcome, CensusOpenAdmissionReports.held, LockOwners.set, other]

private theorem NativeOpenErrorDisposal.keepsOtherLock
    {admission : CensusOpenAdmissionReports input directory inventory retry}
    {cleanup : NativeOpenErrorUnlock admission census}
    (disposed : NativeOpenErrorDisposal cleanup after) {path : FilePath}
    (other : path ≠ directory.file .lock) :
    after.2.owners path = retry.owners path := by
  cases disposed with
  | returned | released => exact cleanup.keepsOtherLock other
  | failed _ slots =>
    have files := congrArg (fun reached => reached.owners path) slots.reached.2.2
    split at files
    · exact files.trans (by simpa only [LockOwners.set, ite_eq_right other] using cleanup.keepsOtherLock other)
    · exact files.trans (cleanup.keepsOtherLock other)

private theorem NativeRejectedOpenLineage.framesOwners
    (lineage : NativeRejectedOpenLineage directory lock root first inputs errors after available) :
    TryLockObserves first.2.owners directory (.ok true) ∧
    ∀ path, path ≠ directory.file .lock → after.2.owners path = first.2.owners path := by
  induction lineage with
  | start vacant => exact ⟨vacant, fun _ _ => rfl⟩
  | attempted _ _ _ _ disposed prior =>
    exact ⟨prior.1, fun _ other => (disposed.keepsOtherLock other).trans (prior.2 _ other)⟩
  | cacheInitializationFailed _ _ attempt _ drops prior =>
    exact ⟨prior.1, fun path other => ((attempt.disposes drops).2.2 path other).trans (prior.2 path other)⟩

/-- When the final reported disposition allows another attempt, both
the original release and the latest state leave the same lock vacant.
The rejected opens never change other lock entries or selected bytes. -/
theorem NativeRejectedOpenLineage.availableFiles
    (lineage : NativeRejectedOpenLineage directory lock root first inputs errors after true) :
    after.2 = first.2 := by
  obtain ⟨_, selected, _, available⟩ := lineage.preserves
  obtain ⟨firstVacant, frame⟩ := lineage.framesOwners
  have afterVacant := available.mpr rfl
  have owners : after.2.owners = first.2.owners := by
    funext path
    by_cases same : path = directory.file .lock
    · subst path
      exact (afterVacant rfl).trans (firstVacant rfl).symm
    · exact frame path same
  change (⟨after.2.image, after.2.owners⟩ : LockedFileState FileImage) = ⟨first.2.image, first.2.owners⟩
  rw [selected, owners]

/-- The final reported healthy open starts at the exact post-error
inventory. Its returned session and physical selections agree with
the writer that performed the original explicit close. -/
structure NativeRejectedOpenAlignedResult (current : NativeReadPosition history log) (after : CensusOpenState)
    (files : NativeCloseFiles current.state) (input : FilePath) (next : NativeReadPosition history log) : Prop where
  released : after.2 = current.state.releasedFiles
  inventoryObjects : after.1.inode = current.state.census.inode
  reads : next.reads = current.reads
  frame : NativeReadRecoveryFrame current.state next.state
  sessionFresh : next.state.session.sessionRef ≠ current.state.session.sessionRef
  phaseFresh : next.state.session.phaseRef ≠ current.state.session.phaseRef
  pair : next.state.files.image.directory.active = current.state.files.image.directory.active
  seals : next.state.files.image.kept = current.state.files.image.kept
  exactOpen : ∃ (plan : ClosedReadyReopenLayout current.state.writer current.state.releasedFiles)
    (selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
      current.state.releasedFiles.image.directory.active.manifest current.state.writer.checkpoint)
    (seen : NativeCloseAlignedReads files input after.1 plan.layout selected),
    seen.run = .ok next.state.session (next.state.census, next.state.files) ∧
    next.opened = seen.run ∧ next.initial = next.state ∧
    next.state.owner = seen.opening.admission.owner ∧ next.state.directorySlot = seen.opening.admission.cached ∧
    next.state.cache = seen.opening.admission.cache ∧ next.state.census = seen.opening.finish.census ∧
    NativeCloseSelectedReads seen
  replay : InstalledClientReplay log current.reads history next.state.writer.installed next.state.session

/-- The exact final reader supplies a ready position after rejected
opens. Its initial files and inode map must frame the closed writer. -/
theorem NativeReadPosition.reopensAfterRejectedOpensAt
    (current : NativeReadPosition history log) (after : CensusOpenState)
    (released : after.2 = current.state.releasedFiles)
    (inventoryObjects : after.1.inode = current.state.census.inode)
    (files : NativeCloseFiles current.state) {input : FilePath}
    (plan : ClosedReadyReopenLayout current.state.writer current.state.releasedFiles)
    (selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
      current.state.releasedFiles.image.directory.active.manifest current.state.writer.checkpoint)
    (seen : NativeCloseAlignedReads files input after.1 plan.layout selected) :
    ∃ next, NativeRejectedOpenAlignedResult current after files input next ∧
      seen.run = next.opened ∧ next.opened = .ok next.state.session (next.state.census, next.state.files) ∧
      next.state.owner = seen.opening.admission.owner ∧ next.state.directorySlot = seen.opening.admission.cached ∧
      next.state.cache = seen.opening.admission.cache := by
  obtain ⟨valid, rows, prior⟩ := current.readPrefix.refines
  obtain ⟨state, continued, directory, owner, directorySlot, cache, census, sessionFresh,
    phaseFresh, lockInode, directoryInode, pair, kept, target, checkpoint, durable, manifestMissing, manifest,
    runs, marker, wal, replay⟩ := files.reopensReleasedAlignedAt valid.retained rows prior
      current.readPrefix.readsBounded plan selected seen
  let next : NativeReadPosition history log := ⟨seen.run, state, state, current.reads, continued⟩
  exact ⟨next, ⟨released, inventoryObjects, rfl,
    ⟨directory, directoryInode, lockInode, target, checkpoint, durable⟩, sessionFresh,
    phaseFresh, pair, kept, ⟨plan, selected, seen, continued.frames.1, rfl, rfl, owner, directorySlot, cache, census,
      ⟨manifestMissing, manifest, runs, marker, wal⟩⟩, replay⟩,
    rfl, continued.frames.1, owner, directorySlot, cache⟩

/-- Compose the actual close, the ordered returned early errors, and a
healthy aligned reopen. The final primitive observations use the exact
reached census. The prior history determines the selection before
those observations supply the concrete reads and barriers. -/
theorem NativeReadPosition.reopensAfterRejectedOpens (current : NativeReadPosition history log)
    (close : NativeReadyClose current.state) (success : close.report.result = .ok ())
    (lineage : NativeRejectedOpenLineage current.state.session.directory
      (current.state.census.inode current.state.owner.description)
      (current.state.census.inode current.state.directorySlot.description)
      (close.report.finished.descriptors, current.state.releasedFiles) inputs errors after true)
    (files : NativeCloseFiles current.state) {input : FilePath}
    (observe : ∀ plan : ClosedReadyReopenLayout current.state.writer current.state.releasedFiles,
      ∀ selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
        current.state.releasedFiles.image.directory.active.manifest current.state.writer.checkpoint,
      Nonempty (NativeCloseAlignedReads files input after.1 plan.layout selected)) :
    close.report.run = .ok () close.report.finished ∧ errors.length = inputs.length ∧
    ∃ next, NativeRejectedOpenAlignedResult current after files input next := by
  obtain ⟨closed, _, _, _, inventoryObjects, _, _, count, _, _⟩ :=
    current.rejectedOpensAfterClose close success lineage
  have released := lineage.availableFiles
  obtain ⟨plan, selected, seen, state, continued, directory, owner, directorySlot, cache, census, sessionFresh,
    phaseFresh, lockInode, directoryInode, pair, kept, target, checkpoint, durable, manifestMissing, manifest,
    runs, marker, wal, replay⟩ := current.readPrefix.reopensReleasedAligned files observe
  let next : NativeReadPosition history log := ⟨seen.run, state, state, current.reads, continued⟩
  exact ⟨closed, count, next, released, inventoryObjects, rfl,
    ⟨directory, directoryInode, lockInode, target, checkpoint, durable⟩, sessionFresh,
    phaseFresh, pair, kept, ⟨plan, selected, seen, continued.frames.1, rfl, rfl, owner, directorySlot, cache, census,
      ⟨manifestMissing, manifest, runs, marker, wal⟩⟩, replay⟩

/-- Reports for an explicit successful close, the prescribed rejected
open inputs, and the prescribed final aligned open. The lineage fixes
each diagnostic and the census consumed by the final callbacks. -/
structure NativeRejectedOpenReopenObservation (state : NativeReadyState)
    (inputs : List FilePath) (input : FilePath) where
  close : NativeReadyClose state
  closed : close.report.result = .ok ()
  errors : List IO.Error
  after : CensusOpenState
  lineage : NativeRejectedOpenLineage state.session.directory
    (state.census.inode state.owner.description) (state.census.inode state.directorySlot.description)
    (close.report.finished.descriptors, state.releasedFiles) inputs errors after true
  files : NativeCloseFiles state
  observe : ∀ plan : ClosedReadyReopenLayout state.writer state.releasedFiles,
    ∀ selected : SelectedIntegrityCheckpoint state.writer.published.durable
      state.releasedFiles.image.directory.active.manifest state.writer.checkpoint,
    Nonempty (NativeCloseAlignedReads files input after.1 plan.layout selected)

theorem NativeReadPosition.retriesAndReopens (current : NativeReadPosition history log)
    (observed : NativeRejectedOpenReopenObservation current.state inputs input) :
    observed.close.report.run = .ok () observed.close.report.finished ∧
    observed.errors.length = inputs.length ∧
    ∃ next, NativeRejectedOpenAlignedResult current observed.after observed.files input next :=
  current.reopensAfterRejectedOpens observed.close observed.closed observed.lineage observed.files observed.observe

end Alvoki.Storage.DiskSession
