import Alvoki.Storage.Disk.CheckpointRunDirectoryClose
import Alvoki.Storage.Disk.CleanCachedClose
import Alvoki.Storage.Disk.ClientReadTrace
import Alvoki.Storage.Disk.Proofs.Recovery.ListedMarkedFinish
import Alvoki.Storage.Disk.LockCensusTrace
import Alvoki.Storage.Disk.MaintainedRecoveryWork

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair
open scoped List

namespace CachedCloseReports

variable {handle image : Type} {directory : DiskDirectory} {writer : Nat}
  {start : CachedCloseState handle image}

/-- The current close's exact return and state, including its lock
authority. This result depends only on the reported close callbacks. -/
def Reached (close : CachedCloseReports directory writer start) : Prop :=
  match close.result with
  | .error cause => close.run = .error cause start ∧ start.files.owners.Owns directory writer
  | .ok () => close.run = .ok () close.finished ∧ close.finished.phase = .closed ∧
      close.finished.files =
        ⟨(⟨none, none, []⟩, start.files.image.2), start.files.owners.set (directory.file .lock) none⟩ ∧
      close.finished.descriptors = start.descriptors.afterDrops
        (close.drops .active ++ close.drops .pending ++ close.drops .directory) ∧
      TryLockObserves close.finished.files.owners directory (.ok true)

theorem reaches (close : CachedCloseReports directory writer start) (openPhase : start.phase ≠ .closed)
    (held : start.files.owners.Owns directory writer) : close.Reached := by
  have outcome := close.outcome_open openPhase
  unfold Reached
  cases reported : close.result with
  | error cause => exact ⟨by simpa only [reported] using outcome, held⟩
  | ok result =>
    cases result
    rw [reported] at outcome
    have files := close.finishedFiles held
    exact ⟨outcome, rfl, files, close.finishedDescriptors, by simp [files, TryLockObserves, LockOwners.set]⟩

/-- A returned unlock failure leaves the starting phase, cache, files
and census in force. The same census then accounts for later aliases,
private forks and drops of the lock description. -/
theorem afterFailedUnlockCensus (close : CachedCloseReports directory writer start) (openPhase : start.phase ≠ .closed)
    {cause : IO.Error} (failed : close.result = .error cause)
    {inventory : DescriptorInventory} {reached : LockedFileState (Cache handle × image)}
    (observed : LockCensusTrace directory writer start.descriptors start.files inventory reached) :
    close.run = .error cause start ∧
      inventory.inode = start.descriptors.inode ∧
      (TryLockObserves reached.owners directory (.ok true) ↔ inventory.references writer = []) ∧
      reached = if inventory.references writer = [] then
        ⟨start.files.image, start.files.owners.set (directory.file .lock) none⟩
      else start.files := by
  have returned := close.reaches openPhase observed.reached.1
  simp only [Reached, failed] at returned
  exact ⟨returned.1, observed.reached.2.1, observed.freshFlockAllowed, observed.reached.2.2⟩

end CachedCloseReports

/-- A trace ending at a reached explicit close, including a failed
unlock, preserves the recorded client observations. The returned state
can be used at this point even when recovery has yet to start. -/
theorem SegmentedClientReadTrace.cachedClosePrefix {handle : Type}
    {first : LockedFileState WalSegmentRotation.State} (bootstrap : BootstrapReady first.image)
    (held : first.owners.Owns directory initialDescriptor)
    (trace : SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
      allowCollection log reads writer before)
    {cache : Cache handle} {descriptors : DescriptorInventory}
    {causes : List IO.Error} {retry : CachedCloseState handle FileImage}
    (failed : CachedCloseFailureTrace directory writer
      ⟨.ready before.installed, ⟨(cache, before.files), before.owners⟩, descriptors⟩ causes retry)
    (close : CachedCloseReports directory writer retry) :
    retry = ⟨.ready before.installed, ⟨(cache, before.files), before.owners⟩, descriptors⟩ ∧ close.Reached ∧
    ∃ reference : Sequential.SnapshotTable UInt64,
      SnapshotWalReplay .empty before.history reference ∧
      DatabaseBatchRetention log before.history ∧
      log.flatMap DatabaseSubmissions.acknowledged <+ before.history ∧
      before.history <+ log.flatMap DatabaseSubmissions.submitted ∧
      ∀ read ∈ reads, read.agrees reference := by
  have same := failed.unchanged (by simp)
  subst retry
  have ready := (trace.writes.preservesRetained (bootstrap.writerReady held).toRetained).1
  exact ⟨rfl, close.reaches (by simp) ready.held, trace.keyValueRefinement bootstrap held⟩

/-- The live directory slot kept by the cache when close starts. -/
structure CachedCloseDirectory (start : CachedCloseState CheckpointOpenHandle FileImage) where
  captured : DescriptorInventory
  slot : DescriptorSlot
  ticket : Nat
  stored : start.files.image.1.directory = some (captured, slot, ticket)
  live : slot ∈ start.descriptors.slots

/-- Start both new allocations from the census left by the cache clears
and intervening drops. Successful explicit unlock releases the old owner
even when an alias of its description remains live. -/
structure CachedCloseReopenCensus {directory : DiskDirectory} {writer : Nat}
    {start : CachedCloseState CheckpointOpenHandle FileImage}
    (close : CachedCloseReports directory writer start) (oldDirectory : CachedCloseDirectory start)
    {input : FilePath} {before : SegmentedWriterState}
    {layout : CanonicalKeeperLayout (SegmentedCleanReopenReport.released directory before).image before.history}
    (opened : CheckpointHeldOpen input directory layout before.published) where
  drops : List LockReferenceDrop
  free : ∀ slot ∈ (close.finished.descriptors.afterDrops drops).slots, slot.address ≠ opened.calls.slot.address
  fresh : (close.finished.descriptors.afterDrops drops).references opened.calls.slot.description = []
  distinct : opened.calls.slot.description ≠ writer
  lockObject : opened.held.lifetime.namespaceView.modelObject opened.held.lifetime.lock =
    start.descriptors.inode close.slot.description
  directoryObject : opened.held.lifetime.namespaceView.modelObject opened.held.lifetime.root =
    start.descriptors.inode oldDirectory.slot.description
  cacheOpen : DirectoryCacheOpenReports directory
    ((close.finished.descriptors.afterDrops drops).insert opened.calls.slot free) opened.calls.slot
    opened.held.lifetime.directorySlot
    ⟨(SegmentedCleanReopenReport.released directory before).image,
      (SegmentedCleanReopenReport.released directory before).owners.set (directory.file .lock)
        (some opened.calls.slot.description)⟩
    opened.held.lifetime.namespaceView opened.held.lifetime.root
  census : opened.calls.descriptors =
    (((close.finished.descriptors.afterDrops drops).insert opened.calls.slot free).insert
      opened.held.lifetime.directorySlot cacheOpen.free)
  projected : opened.calls.openFiles before.files =
    match runSyncFilesOpen (cacheOpen.opened directory.path)
      ((close.finished.descriptors.afterDrops drops).insert opened.calls.slot free,
        ⟨(SegmentedCleanReopenReport.released directory before).image,
          (SegmentedCleanReopenReport.released directory before).owners.set (directory.file .lock)
            (some opened.calls.slot.description)⟩) with
    | .ok cache (_, reached) => .ok cache reached.image
    | .error cause (_, reached) => .error cause reached.image

namespace CachedCloseReopenCensus

variable {directory : DiskDirectory} {writer : Nat} {start : CachedCloseState CheckpointOpenHandle FileImage}
  {close : CachedCloseReports directory writer start} {oldDirectory : CachedCloseDirectory start}
  {input : FilePath} {before : SegmentedWriterState}
  {layout : CanonicalKeeperLayout (SegmentedCleanReopenReport.released directory before).image before.history}
  {opened : CheckpointHeldOpen input directory layout before.published}

/-- Use the exact issued descriptions for the shared cache initialization,
with both objects matching those of the closing writer. -/
theorem captures (observed : CachedCloseReopenCensus close oldDirectory opened) :
    opened.calls.bindings (directory.file .lock) = close.bindings (directory.file .lock) ∧
    opened.calls.cache = ⟨some (opened.calls.descriptors, opened.held.lifetime.directorySlot, 0), none, []⟩ ∧
    opened.calls.descriptors.references opened.calls.slot.description = [opened.calls.slot.reference] ∧
    opened.calls.descriptors.inode opened.held.lifetime.directorySlot.description =
      start.descriptors.inode oldDirectory.slot.description := by
  obtain ⟨cache, _, _, root⟩ := opened.wal.operations.capturedDirectoryFromOpen
    observed.cacheOpen observed.census observed.projected
  have separate := observed.cacheOpen.captures.2.2.2.1
  have refs : opened.calls.descriptors.references opened.calls.slot.description = [opened.calls.slot.reference] := by
    rw [observed.census, DescriptorInventory.references_insert, ite_eq_right separate,
      DescriptorInventory.references_insert, ite_eq_left rfl, observed.fresh]
  have lock := opened.held.lifetime.identifiesLock.symm.trans observed.lockObject
  exact ⟨opened.calls.lockObject.trans ((congrArg some lock).trans close.lockObject.symm), cache, refs,
    root.symm.trans observed.directoryObject⟩

end CachedCloseReopenCensus

/-- A ready client can retry an explicit close after local unlock errors.
The healthy close uses the unchanged phase, cache and descriptor table.
Its exact released image and reported allocations carry the held reopen
into the same submission and read ledgers. -/
theorem SegmentedClientReadTrace.reopenAfterCachedCloseRetries {input : FilePath}
    {first : LockedFileState WalSegmentRotation.State} (bootstrap : BootstrapReady first.image)
    (held : first.owners.Owns directory initialDescriptor)
    (trace : SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
      allowCollection log reads writer before)
    {cache : Cache CheckpointOpenHandle} {descriptors : DescriptorInventory}
    {causes : List IO.Error} {retry : CachedCloseState CheckpointOpenHandle FileImage}
    (failed : CachedCloseFailureTrace directory writer
      ⟨.ready before.installed, ⟨(cache, before.files), before.owners⟩, descriptors⟩ causes retry)
    (close : CachedCloseReports directory writer retry) (unlocked : close.result = .ok ())
    (oldDirectory : CachedCloseDirectory retry)
    (observe : ∀ layout : CanonicalKeeperLayout (SegmentedCleanReopenReport.released directory before).image before.history,
      layout.keeper = before.wal.active → layout.tail = ByteArray.empty →
      layout.sealed ++ [layout.keeper] = before.wal.readDescriptors layout.range.watermark →
      ∃ opened : PrimitiveCheckpointHeldOpen input directory layout before.published,
        Nonempty (CachedCloseReopenCensus close oldDirectory opened.toHeldOpen)) :
    (retry = ⟨.ready before.installed, ⟨(cache, before.files), before.owners⟩, descriptors⟩) ∧
    close.run = .ok () close.finished ∧ close.finished.phase = .closed ∧
    close.finished.files = ⟨(⟨none, none, []⟩, before.files), before.owners.set (directory.file .lock) none⟩ ∧
    close.finished.descriptors = descriptors.afterDrops (close.drops .active ++ close.drops .pending ++ close.drops .directory) ∧
    ∃ (layout : CanonicalKeeperLayout (SegmentedCleanReopenReport.released directory before).image before.history)
      (opened : CheckpointHeldOpen input directory layout before.published) (after : SegmentedWriterState)
      (session : SegmentedSession) (final : LockedFileState FileImage),
      Nonempty (CachedCloseReopenCensus close oldDirectory opened) ∧
      AdmittedCleanReopen (close.cleanUnlock unlocked) opened.chunkReports opened.admission after ∧
      opened.wal.operations.runWithAdmission opened.admission = .ok session final ∧
      session.directory = directory ∧ session.descriptor = opened.calls.slot.description ∧
      session.phase = .ready after.installed ∧ session.sessionRef ∉ opened.calls.liveRefs ∧
      final.owners.Owns directory session.descriptor ∧ after.files = final.image ∧ after.owners = final.owners ∧
      opened.calls.descriptors.references opened.calls.slot.description = [opened.calls.slot.reference] ∧
      opened.calls.descriptors.inode opened.held.lifetime.directorySlot.description =
        descriptors.inode oldDirectory.slot.description ∧
      SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
        allowCollection log reads opened.calls.slot.description after ∧ GuardedClientReplay log reads after session := by
  obtain ⟨same, reached, _⟩ := trace.cachedClosePrefix bootstrap held failed close
  subst retry
  simp only [CachedCloseReports.Reached, unlocked] at reached
  obtain ⟨returned, closed, cleared, finishedDescriptors, _⟩ := reached
  have ready := (trace.writes.preservesRetained (bootstrap.writerReady held).toRetained).1
  obtain ⟨layout, opened, after, endpoint, observed⟩ := ready.closeWithHeldEvidence (close.cleanUnlock unlocked)
    (fun opened => Nonempty (CachedCloseReopenCensus close oldDirectory opened)) (by
      intro layout keeper tail seals
      obtain ⟨primitive, observed⟩ := observe layout keeper tail seals
      obtain ⟨census⟩ := observed
      exact ⟨primitive.toHeldOpen, census.captures.1, census.distinct, ⟨census⟩⟩)
  obtain ⟨session, final, result, directoryExact, descriptorExact, phase, fresh, files, owners⟩ := endpoint.reopenEffect
  obtain ⟨census⟩ := observed
  have finalHeld : final.owners.Owns directory session.descriptor :=
    descriptorExact.symm ▸ owners ▸ endpoint.writer.retained.held
  have continued : SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
      allowCollection log reads opened.calls.slot.description after := by
    change SegmentedClientReadTrace directory initialDescriptor (bootstrap.writerState first.owners)
      allowCollection log reads opened.chunkReports.slot.description after
    simpa only [List.append_nil] using trace.advance (.cleanReopenObserved .start (close.cleanUnlock unlocked) endpoint)
  exact ⟨rfl, returned, closed, cleared, finishedDescriptors,
    layout, opened, after, session, final, ⟨census⟩, endpoint, result, directoryExact, descriptorExact, phase, fresh,
    finalHeld, files, owners, census.captures.2.2.1, census.captures.2.2.2, continued,
    continued.guardedReplay bootstrap held phase⟩

end Alvoki.Storage.DiskSession
