import Alvoki.Storage.Disk.NativeExecutionClose
import Alvoki.Storage.Disk.Proofs.Recovery.NativeMarkedBarrierRetryReopen

namespace Alvoki.Storage.DiskSession

open System Manifest WalSegmentRepair WAL.Boundary

private theorem NativeMarkedBarrierAttempt.keepsOtherOwner
    {before : CensusOpenState} {input : FilePath} {directory : DiskDirectory}
    {published : CheckpointPublication.Image} {checkpoint : Option (PackedTable × UInt64)}
    (attempt : NativeMarkedBarrierAttempt directory input before history published checkpoint)
    (drops : List LockReferenceDrop) {path : FilePath} (other : path ≠ directory.file .lock) :
    (attempt.afterDrops drops).2.owners path = before.2.owners path := by
  have held : attempt.barrier.reachedFiles.owners path = before.2.owners path := by
    simp [NativeMarkedFirstBarrierError.reachedFiles, CensusOpenAdmissionReports.held, LockOwners.set, other]
  cases unlock : attempt.unlock with
  | ok value =>
    cases value
    simpa only [NativeMarkedBarrierAttempt.afterDrops, NativeMarkedBarrierAttempt.returnedFiles, unlock,
      NativeMarkedFirstBarrierError.afterUnlock, LockOwners.set, ite_eq_right other] using held
  | error cause =>
    have owns : (attempt.barrier.afterUnlock (.error cause)).owners.Owns directory attempt.admission.owner.description :=
      attempt.admission.opened.held
    have live : attempt.keeper.afterRead.references attempt.admission.owner.description ≠ [] :=
      List.ne_nil_of_mem (attempt.keeper.afterRead.mem_references.mpr
        ⟨attempt.admission.owner, attempt.keeper.ownerRetained, rfl, rfl⟩)
    have dropped := (LockCensusTrace.start owns live).drops drops
    have frame := congrArg (fun files => files.owners path) dropped.reached.2.2
    simp only [afterDrops, returnedFiles, unlock]
    split at frame
    · exact frame.trans (by simpa only [LockOwners.set, ite_eq_right other, NativeMarkedFirstBarrierError.afterUnlock] using held)
    · exact frame.trans held

private theorem NativeMarkedBarrierRetries.keepsOtherOwners
    {published : CheckpointPublication.Image} {checkpoint : Option (PackedTable × UInt64)}
    (trace : NativeMarkedBarrierRetries directory lock root history published checkpoint first events after available)
    {path : FilePath} (other : path ≠ directory.file .lock) :
    after.2.owners path = first.2.owners path := by
  induction trace with
  | start _ => rfl
  | attempted _ _ attempt _ drops prior => exact (attempt.keepsOtherOwner drops other).trans prior

/-- Once the previous owner has released a settled database, a finite
sequence of first-barrier errors returns the full original file and owner
image when its reported final cleanup leaves the same lock vacant. -/
theorem NativeMarkedBarrierRetries.availableSettledFiles
    {published : CheckpointPublication.Image} {checkpoint : Option (PackedTable × UInt64)}
    (trace : NativeMarkedBarrierRetries directory lock root history published checkpoint first events after true)
    (settled : first.2.image.syncDirectory = first.2.image)
    (vacant : TryLockObserves first.2.owners directory (.ok true)) :
    after.2 = first.2 := by
  have image := trace.preserves.1
  rw [settled] at image
  have contents : after.2.image = first.2.image := by simpa only [ite_self] using image
  have owners : after.2.owners = first.2.owners := by
    funext path
    by_cases same : path = directory.file .lock
    · subst path
      exact (trace.vacant rfl).trans (vacant rfl).symm
    · exact trace.keepsOtherOwners same
  cases before : first.2
  cases reached : after.2
  rw [before, reached] at contents owners
  rw [LockedFileState.mk.injEq]
  exact ⟨contents, owners⟩

private theorem settledFiles {state : NativeReadyState} (ready : state.Valid) :
    state.releasedFiles.image.syncDirectory = state.releasedFiles.image := by
  change state.writer.files.syncDirectory = state.writer.files
  rw [← ready.retained.cleanFiles]
  cases directory : state.writer.wal.directory with
  | mk active alternatives staged =>
    have exact := ready.retained.walDirectorySettled
    rw [directory] at exact
    change alternatives = [active] at exact
    subst alternatives
    rfl

/-- The aligned physically observed open uses the common marked worker
and its same chronological descriptor census. -/
def NativeCloseAlignedReads.toMarked
    {state : NativeReadyState} {files : NativeCloseFiles state}
    {input : FilePath} {inventory : DescriptorInventory}
    {layout : CanonicalKeeperLayout state.releasedFiles.image state.writer.history}
    {selected : SelectedIntegrityCheckpoint state.writer.published.durable
      state.releasedFiles.image.directory.active.manifest state.writer.checkpoint}
    (seen : NativeCloseAlignedReads files input inventory layout selected) :
    MarkedReadyOpenObservations input state.session.directory inventory state.releasedFiles
      layout state.writer.published state.releasedVacant selected :=
  { admission := seen.opening.admission
    callbacks := seen.opening.callbacks
    reads := seen.opening.reads
    finish := .aligned seen.opening.finish
    chronology := seen.chronology
    marker := seen.opening.marker
    markerFound := seen.opening.markerFound }

private theorem NativeCloseAlignedReads.selectedFiles
    {state : NativeReadyState} {files : NativeCloseFiles state}
    {input : FilePath} {inventory : DescriptorInventory}
    {plan : ClosedReadyReopenLayout state.writer state.releasedFiles}
    {selected : SelectedIntegrityCheckpoint state.writer.published.durable
      state.releasedFiles.image.directory.active.manifest state.writer.checkpoint}
    (seen : NativeCloseAlignedReads files input inventory plan.layout selected) (valid : state.Valid) :
    NativeCloseSelectedReads seen := by
  have pair := plan.prepared.pair.trans (congrArg Target.pair plan.target)
  let retained := valid.retained
  have marker : state.writer.target.pair.walBoundary = some (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64) :=
    (congrArg DirectoryPublication.Bindings.walBoundary retained.resumed.ready.selected).symm.trans
      (congrArg Publication.Image.active retained.resumed.markerImage)
  exact ⟨seen.manifestMissing pair, fun _ present => seen.readsManifest pair present,
    fun _ _ present decoded _ within _ stored => seen.readsRun pair present decoded within stored,
    seen.readsMarker pair marker, seen.readsWal plan.aligned plan.descriptors⟩

/-- The closed writer supplies the original checked layout and checkpoint
to the first-barrier retry work theorem. The final read reports are used
only to identify the actual catalog ordering. -/
private def closeSeed {state : NativeReadyState} {files : NativeCloseFiles state}
    {input : FilePath} {inventory : DescriptorInventory}
    {plan : ClosedReadyReopenLayout state.writer state.releasedFiles}
    {selected : SelectedIntegrityCheckpoint state.writer.published.durable
      state.releasedFiles.image.directory.active.manifest state.writer.checkpoint}
    (seen : NativeCloseAlignedReads files input inventory plan.layout selected)
    (valid : state.Valid) (closed : DescriptorInventory) :
    NativeMarkedBarrierSeed (closed, state.releasedFiles) state.writer.history state.writer.published state.writer.checkpoint :=
  let retained := valid.retained
  let pair := plan.prepared.pair.trans (congrArg Target.pair plan.target)
  { layout := plan.layout
    prepared := plan.prepared
    selected := selected
    accepted := (congrArg DirectoryPublication.Bindings.manifest pair).symm ▸ retained.resumed.accepted
    following := seen.opening.reads.walReads.selectedAfterWatermark plan.offsets plan.descriptors
    ordered := retained.resumed.ordered
    wal := state.writer.wal
    readLayout := retained.layout
    valid := retained.valid
    spans := retained.spans
    active := retained.walPair.trans (congrArg Target.pair plan.target).symm
    keeper := congrArg WalSegment.first plan.keeper
    kept := retained.sealedFiles }

/-- The final healthy open consumes the reached files and inventory
from the reported close and subsequent first repair barrier failures. -/
structure NativeCloseMarkedBarrierResult (current : NativeReadPosition history log)
    (files : NativeCloseFiles current.state) (after : CensusOpenState) (input : FilePath)
    (events : List NativeMarkedBarrierEvent) (next : NativeReadPosition history log) : Prop where
  released : after.2 = current.state.releasedFiles
  inventoryObjects : after.1.inode = current.state.census.inode
  reads : next.reads = current.reads
  frame : NativeReadRecoveryFrame current.state next.state
  sessionFresh : next.state.session.sessionRef ≠ current.state.session.sessionRef
  phaseFresh : next.state.session.phaseRef ≠ current.state.session.phaseRef
  table : recoverSelected (current.state.writer.checkpoint.getD (.empty, 0)).1 (WAL.encode history) =
    .ok next.state.writer.installed.table
  exactOpen : ∃ (plan : ClosedReadyReopenLayout current.state.writer current.state.releasedFiles)
    (selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
      current.state.releasedFiles.image.directory.active.manifest current.state.writer.checkpoint)
    (seen : NativeCloseAlignedReads files input after.1 plan.layout selected) (repairs : Nat),
      seen.run = .ok next.state.session (next.state.census, next.state.files) ∧
      next.opened = seen.run ∧ next.initial = next.state ∧
      next.state.owner = seen.opening.admission.owner ∧ next.state.directorySlot = seen.opening.admission.cached ∧
      next.state.cache = seen.opening.admission.cache ∧ next.state.census = seen.opening.finish.census ∧
      NativeCloseSelectedReads seen ∧
      countBoundedRepairCallbacks current.state.session.directory plan.layout.boundedPlan
        seen.opening.reads.wal.keeper.calls.metadata.byteSize.toNat = .ok repairs ∧
      (events.map (·.chunkRequests)).sum + seen.toMarked.metadataReadRequests + seen.toMarked.payloadReadRequests ≤
        (events.length + 1) * NativeMarkedBarrierAttempt.chunkBudget current.state.files.image
          current.state.writer.history current.state.writer.checkpoint ∧
      (events.map (·.directoryRequests)).sum +
        (seen.toMarked.directoryWork.opendirCalls + seen.toMarked.directoryWork.readdirCalls +
          seen.toMarked.directoryWork.closedirCalls) =
        (events.map (·.listedNames)).sum + seen.opening.reads.listing.scan.names.length + 3 * (events.length + 1) ∧
      (events.map (·.repairRequests)).sum + repairs = events.length + 2
  replay : InstalledClientReplay log current.reads history next.state.writer.installed next.state.session

/-- Compose actual close, the exact finite charged first-barrier prefix
on its returned files, and the final healthy marked open. Stable local
reports identify the same physical files; the earlier ready writer
supplies the exact selected checkpoint and read replay. -/
theorem NativeReadPosition.reopensAfterMarkedBarriers (current : NativeReadPosition history log)
    (close : NativeReadyClose current.state) (success : close.report.result = .ok ())
    (lineage : NativeMarkedBarrierRetries current.state.session.directory
      (current.state.census.inode current.state.owner.description)
      (current.state.census.inode current.state.directorySlot.description)
      current.state.writer.history current.state.writer.published current.state.writer.checkpoint
      (close.report.finished.descriptors, current.state.releasedFiles) events after true)
    (files : NativeCloseFiles current.state) {input : FilePath}
    (observe : ∀ plan : ClosedReadyReopenLayout current.state.writer current.state.releasedFiles,
      ∀ selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
        current.state.releasedFiles.image.directory.active.manifest current.state.writer.checkpoint,
      Nonempty (NativeCloseAlignedReads files input after.1 plan.layout selected)) :
    close.report.run = .ok () close.report.finished ∧ close.report.finished.phase = .closed ∧
    close.report.finished.descriptors = current.state.census.afterDrops
      (close.report.drops .active ++ close.report.drops .pending ++ close.report.drops .directory) ∧
    ∃ next, NativeCloseMarkedBarrierResult current files after input events next := by
  obtain ⟨valid, originalHistory, pending⟩ := current.readPrefix.refines
  obtain ⟨closed, phase, _, descriptors, vacant⟩ := close.closes valid success
  have released := lineage.availableSettledFiles (settledFiles valid) vacant
  have startObjects : close.report.finished.descriptors.inode = current.state.census.inode := by
    rw [descriptors]
    rfl
  have inodes : after.1.inode = current.state.census.inode := lineage.preserves.2.2.2.2.2.1.trans startObjects
  refine ⟨closed, phase, descriptors, ?_⟩
  obtain ⟨inventory, reached⟩ := after
  change reached = current.state.releasedFiles at released
  subst reached
  let retained := valid.retained
  obtain ⟨plan⟩ : Nonempty (ClosedReadyReopenLayout current.state.writer current.state.releasedFiles) :=
    retained.cleanReopenLayout
  have pair := plan.prepared.pair.trans (congrArg Target.pair plan.target)
  let selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
      current.state.releasedFiles.image.directory.active.manifest current.state.writer.checkpoint :=
    (congrArg DirectoryPublication.Bindings.manifest pair).symm ▸ retained.resumed.selected
  obtain ⟨seen⟩ := observe plan selected
  let seed := closeSeed seen valid close.report.finished.descriptors
  have objects :
      seen.toMarked.admission.view.modelObject seen.toMarked.reads.lock = current.state.census.inode current.state.owner.description ∧
      seen.toMarked.admission.view.modelObject seen.toMarked.admission.root =
        current.state.census.inode current.state.directorySlot.description := by
    refine ⟨?_, seen.admission.directoryObject⟩
    exact seen.opening.reads.identifiesLock.trans seen.admission.lockObject
  have pendingWriter : PendingClientReplay log current.reads current.state.writer.history := by
    rw [originalHistory]
    exact pending
  have boundedWriter : ∀ read ∈ current.reads, read.BoundedBy current.state.writer.history.length := by
    rw [originalHistory]
    exact current.readPrefix.readsBounded
  obtain ⟨state, repairs, started, returned, path, owner, cached, cache, census, lockObject, directoryObject,
    _, _, durable, checkpoint, target, phaseFresh, sessionFresh, recovered, _, count, chunks, listed, _⟩ :=
    lineage.reopensWithWork (seed := seed) seen.toMarked objects pendingWriter boundedWriter
  have continued : NativeReadyReadPrefix seen.run state history log current.reads state :=
    Eq.mp (congrArg (fun journal => NativeReadyReadPrefix seen.run state journal log current.reads state) originalHistory) started
  let next : NativeReadPosition history log := ⟨seen.run, state, state, current.reads, continued⟩
  have sameCensus : state.census.inode = seen.opening.admission.reached.inode := by
    change state.census = seen.opening.finish.census at census
    rw [census, CapturedAlignedFinish.census, seen.opening.finish.repair.opened]
    rfl
  have frame : NativeReadRecoveryFrame current.state state :=
    ⟨path, (congrFun sameCensus _).trans directoryObject, (congrFun sameCensus _).trans lockObject,
      target.trans plan.target, checkpoint, durable⟩
  have pruned : current.state.releasedFiles.image.later.visible = [] := retained.resumed.ready.pruned.1
  have aligned : seen.opening.reads.wal.keeper.calls.metadata.byteSize.toNat = plan.layout.boundedPlan.keeperSize := by
    have measured : seen.opening.reads.wal.keeper.calls.metadata.byteSize.toNat =
        (plan.layout.keeper.bytes ++ plan.layout.tail).size :=
      seen.opening.reads.wal.keeper.observesFile.extent
    rw [measured, plan.aligned, ByteArray.append_empty]
    exact plan.layout.target.trimmedSize
  obtain ⟨names, repairCount⟩ := seen.toMarked.repairWork_exact plan.prepared
  rw [pruned] at names
  have repairCountTwo : repairs = 2 := by
    change countBoundedRepairCallbacks current.state.session.directory plan.layout.boundedPlan
      seen.opening.reads.wal.keeper.calls.metadata.byteSize.toNat = .ok repairs at count
    have measured : seen.toMarked.reads.wal.keeper.calls.metadata.byteSize.toNat = plan.layout.boundedPlan.keeperSize :=
      aligned
    simp only [names, List.isEmpty_nil, measured, beq_self_eq_true, Bool.and_self, ite_true] at repairCount
    rw [aligned] at count
    exact Except.ok.inj (count.symm.trans repairCount)
  have repairWork : (events.map (·.repairRequests)).sum + repairs = events.length + 2 := by
    rw [lineage.boundedWork.2.2, repairCountTwo]
  have exactTable : recoverSelected (current.state.writer.checkpoint.getD (.empty, 0)).1 (WAL.encode history) =
      .ok state.writer.installed.table :=
    Eq.mp (congrArg (fun journal => recoverSelected (current.state.writer.checkpoint.getD (.empty, 0)).1
      (WAL.encode journal) = .ok state.writer.installed.table) originalHistory) recovered
  exact ⟨next, rfl, inodes, rfl, frame,
    fun same => sessionFresh (same.symm ▸ seen.earlierTokens.2),
    fun same => phaseFresh (same.symm ▸ seen.earlierTokens.1), exactTable,
    ⟨plan, selected, seen, repairs, returned, rfl, rfl, owner, cached, cache, census, seen.selectedFiles valid,
      count, chunks, listed, repairWork⟩, continued.guardedReplay⟩


end Alvoki.Storage.DiskSession
