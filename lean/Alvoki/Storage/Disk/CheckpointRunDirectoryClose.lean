import Alvoki.Storage.Disk.CheckpointRunDirectoryFailure
import Alvoki.Storage.Disk.DirectoryCacheCapture
import Alvoki.Storage.Disk.PoisonedBatchClose

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair
open WAL.Boundary (WalInodeImage)

namespace CachedCloseReports

/-- The close schedule carries the census reached by the three cache
clears in their execution order. -/
theorem finishedDescriptors {handle image : Type} {directory : DiskDirectory} {writer : Nat}
    {before : CachedCloseState handle image} (report : CachedCloseReports directory writer before) :
    report.finished.descriptors = before.descriptors.afterDrops
      (report.drops .active ++ report.drops .pending ++ report.drops .directory) := by
  simp only [finished, CachedCloseState.finishClears, CachedCloseState.drop, CachedCloseState.release,
    DescriptorInventory.afterDrops_append]

end CachedCloseReports

/-- A caller may catch a failed explicit close and call close again. Each
step records the actual returned error and state of the shared schedule. -/
inductive CachedCloseFailureTrace {handle image : Type} (directory : DiskDirectory) (writer : Nat) :
    CachedCloseState handle image → List IO.Error → CachedCloseState handle image → Prop where
  | nil : CachedCloseFailureTrace directory writer before [] before
  | cons (report : CachedCloseReports directory writer before)
      (returned : report.run = .error cause reached)
      (rest : CachedCloseFailureTrace directory writer reached causes after) :
      CachedCloseFailureTrace directory writer before (cause :: causes) after

/-- An unlock error stops close before every cache clear. Repeating only
such attempts leaves the precise input to a later successful close. -/
theorem CachedCloseFailureTrace.unchanged (trace : CachedCloseFailureTrace directory writer before causes after)
    (openPhase : before.phase ≠ .closed) : after = before := by
  induction trace with
  | nil => rfl
  | cons report returned _ ih =>
    rw [report.outcome_open openPhase] at returned
    cases result : report.result with
    | ok value =>
      cases value
      simp [result] at returned
    | error cause =>
      rw [result] at returned
      have same := (EStateM.Result.error.inj returned).2
      subst same
      exact ih openPhase

namespace ObservedCheckpointRunDirectoryFailure

variable {directory : DiskDirectory} {before : SegmentedWriterState}
  {cut : CheckpointPowerCut directory before} {writer : Nat}

private abbrev Handle := DescriptorInventory × DescriptorSlot

/-- Frame the inode image and its exact run and manifest projection
when changing only the cache, lock owner, and phase during close. -/
def closeState (report : ObservedCheckpointRunDirectoryFailure cut) :
    CachedCloseState Handle (WalInodeImage × Image) :=
  ⟨.poisoned, ⟨(report.after.1, report.after.2, report.publication), before.owners⟩,
    report.directoryHandle.1.afterDrops report.drops⟩

def released (report : ObservedCheckpointRunDirectoryFailure cut) : LockedFileState FileImage :=
  ⟨CheckpointPowerCut.physical before report.publication, before.owners.set (directory.file .lock) none⟩

/-- The native close schedule unlocks the reached poisoned writer before
clearing its active, pending and directory references. The three observed
drops leave the same checkpoint namespace available for the next open. -/
theorem closes (report : ObservedCheckpointRunDirectoryFailure cut)
    (close : CachedCloseReports directory writer report.closeState)
    (ready : before.RetainedReady directory writer) (unlocked : close.result = .ok ()) :
    let after := close.finished
    close.run = .ok () after ∧ after.phase = .closed ∧
    after.files.image = (⟨none, none, []⟩, report.after.2, report.publication) ∧
    after.descriptors = (report.directoryHandle.1.afterDrops report.drops).afterDrops
      (close.drops .active ++ close.drops .pending ++ close.drops .directory) ∧
    (⟨CheckpointPowerCut.physical before after.files.image.2.2, after.files.owners⟩ : LockedFileState FileImage) =
      report.released := by
  intro after
  have outcome := close.outcome rfl
  rw [unlocked] at outcome
  have files := close.finishedFiles ready.held
  refine ⟨outcome, rfl, congrArg LockedFileState.image files, close.finishedDescriptors, ?_⟩
  change (⟨CheckpointPowerCut.physical before close.finished.files.image.2.2, close.finished.files.owners⟩ :
    LockedFileState FileImage) = report.released
  rw [files]
  rfl

/-- Start the next admitted open from the census after close and the
reported intervening drops. The actual append-open slot and directory
open then add their own fresh slots to that census. The two opens resolve
the same lock and directory objects as the failed writer and its close. -/
structure CloseReopenCensus {report : ObservedCheckpointRunDirectoryFailure cut}
    (close : CachedCloseReports directory writer report.closeState) {input : FilePath}
    {layout : CanonicalKeeperLayout report.released.image before.history}
    (opened : CheckpointHeldOpen input directory layout report.publication) where
  drops : List LockReferenceDrop
  lockFree : ∀ live ∈ (close.finished.descriptors.afterDrops drops).slots, live.address ≠ opened.calls.slot.address
  lockFresh : (close.finished.descriptors.afterDrops drops).references opened.calls.slot.description = []
  lockObject : opened.held.lifetime.namespaceView.modelObject opened.held.lifetime.lock =
    report.closeState.descriptors.inode close.slot.description
  directoryObject : opened.held.lifetime.namespaceView.modelObject opened.held.lifetime.root =
    report.directoryHandle.1.inode report.directoryHandle.2.description
  cacheOpen : DirectoryCacheOpenReports directory
    ((close.finished.descriptors.afterDrops drops).insert opened.calls.slot lockFree) opened.calls.slot
    opened.held.lifetime.directorySlot
    ⟨report.released.image, report.released.owners.set (directory.file .lock) (some opened.calls.slot.description)⟩
    opened.held.lifetime.namespaceView opened.held.lifetime.root
  census : opened.wal.operations.descriptors =
    (((close.finished.descriptors.afterDrops drops).insert opened.calls.slot lockFree).insert
      opened.held.lifetime.directorySlot cacheOpen.free)
  projected : opened.wal.operations.openFiles report.released.image =
    match runSyncFilesOpen (cacheOpen.opened directory.path)
      ((close.finished.descriptors.afterDrops drops).insert opened.calls.slot lockFree,
        ⟨report.released.image, report.released.owners.set (directory.file .lock) (some opened.calls.slot.description)⟩) with
    | .ok cache (_, reached) => .ok cache reached.image
    | .error cause (_, reached) => .error cause reached.image

/-- The checked open reaches the same canonical lock and directory
objects using the two reported allocations, and its cache refers to that
directory slot in the resulting census. -/
theorem CloseReopenCensus.captured {report : ObservedCheckpointRunDirectoryFailure cut}
    {close : CachedCloseReports directory writer report.closeState} {input : FilePath}
    {layout : CanonicalKeeperLayout report.released.image before.history}
    {opened : CheckpointHeldOpen input directory layout report.publication}
    (observed : CloseReopenCensus close opened) :
    opened.admission.openAppend (directory.file .lock) = .ok opened.calls.slot ∧
    opened.wal.operations.cache = ⟨some (opened.wal.operations.descriptors, opened.held.lifetime.directorySlot, 0), none, []⟩ ∧
    opened.calls.slot ∈ opened.wal.operations.descriptors.slots ∧
    opened.held.lifetime.directorySlot ∈ opened.wal.operations.descriptors.slots ∧
    opened.wal.operations.descriptors.references opened.calls.slot.description = [opened.calls.slot.reference] ∧
    close.bindings (directory.file .lock) = some (opened.wal.operations.descriptors.inode opened.calls.slot.description) ∧
    opened.wal.operations.descriptors.inode opened.held.lifetime.directorySlot.description =
      report.directoryHandle.1.inode report.directoryHandle.2.description := by
  obtain ⟨cache, lock, dir, object⟩ := opened.wal.operations.capturedDirectoryFromOpen
    observed.cacheOpen observed.census observed.projected
  have fresh : opened.wal.operations.descriptors.references opened.calls.slot.description = [opened.calls.slot.reference] := by
    have separate : opened.held.lifetime.directorySlot.description ≠ opened.calls.slot.description := by
      exact observed.cacheOpen.captures.2.2.2.1
    rw [observed.census, DescriptorInventory.references_insert, ite_eq_right separate,
      DescriptorInventory.references_insert, ite_eq_left rfl, observed.lockFresh]
  exact ⟨opened.admission.opened, cache, lock, dir, fresh,
    close.lockObject.trans (congrArg some (observed.lockObject.symm.trans opened.held.lifetime.identifiesLock)),
    object.symm.trans observed.directoryObject⟩

/-- After the reported explicit close, the first healthy admitted retry
uses the exact reached run map and the census derived from that close.
It returns the ready session that loads the prior checkpoint and WAL. -/
theorem reopensAfterCachedClose (report : ObservedCheckpointRunDirectoryFailure cut) {input : FilePath}
    (ready : before.RetainedReady directory writer)
    (close : CachedCloseReports directory writer report.closeState) (unlocked : close.result = .ok ())
    (reads : ∀ layout : CanonicalKeeperLayout report.released.image before.history,
      layout.keeper = before.wal.active → layout.tail = ByteArray.empty →
      layout.sealed ++ [layout.keeper] =
        (report.publication.segmentedCheckpointView before.wal).readDescriptors layout.range.watermark →
      ∃ opened : CheckpointHeldOpen input directory layout report.publication, Nonempty (CloseReopenCensus close opened)) :
    close.run = .ok () close.finished ∧
    (⟨CheckpointPowerCut.physical before close.finished.files.image.2.2, close.finished.files.owners⟩ :
      LockedFileState FileImage) = report.released ∧
    ∃ (layout : CanonicalKeeperLayout report.released.image before.history)
      (opened : CheckpointHeldOpen input directory layout report.publication)
      (session : SegmentedSession) (final : LockedFileState FileImage) (after : SegmentedWriterState),
      report.Reopened (.closed : SegmentedFailureRelease writer) opened session final after ∧
      Nonempty (CloseReopenCensus close opened) := by
  have active : report.publication.manifest.active = before.wal.directory.active.manifest := by
    rw [report.priorManifest, ready.manifestFiles, ready.directoryFiles]
    rfl
  have choices : report.publication.manifest.crashImages = [before.wal.directory.active.manifest] := by
    rw [report.priorManifest, ready.manifestFiles, ready.directoryFiles]
    simp [DirectoryPublication.Image.project, DirectoryPublication.Bindings.get, ready.walDirectorySettled]
  obtain ⟨layout, opened, session, final, after, installed, census⟩ := ready.reopensPriorCheckpointLiveWith
    report.publication active choices (report.priorRuns ready) report.released
    (fun opened => Nonempty (CloseReopenCensus close opened)) .empty reads
  obtain ⟨poisoned, released, _⟩ := report.poisonsAndReleases ready (.closed : SegmentedFailureRelease writer)
  obtain ⟨closed, _, _, _, projected⟩ := report.closes close ready unlocked
  exact ⟨closed, projected, layout, opened, session, final, after,
    ⟨installed, cut.preflight.publicationError (report.calls.callbacks directory) directory poisoned, released, .empty⟩, census⟩

/-- After any finite list of observed failed closes, the successful
close starts from the checkpoint error's exact cache, files, phase and
descriptor census. Its reached state supplies the next admitted open. -/
theorem reopensAfterCachedCloseRetries (report : ObservedCheckpointRunDirectoryFailure cut) {input : FilePath}
    (ready : before.RetainedReady directory writer) {causes : List IO.Error}
    {retry : CachedCloseState Handle (WalInodeImage × Image)}
    (failed : CachedCloseFailureTrace directory writer report.closeState causes retry)
    (close : CachedCloseReports directory writer retry) (unlocked : close.result = .ok ())
    (reads : ∀ (same : retry = report.closeState) (layout : CanonicalKeeperLayout report.released.image before.history),
      layout.keeper = before.wal.active → layout.tail = ByteArray.empty →
      layout.sealed ++ [layout.keeper] =
        (report.publication.segmentedCheckpointView before.wal).readDescriptors layout.range.watermark →
      ∃ opened : CheckpointHeldOpen input directory layout report.publication,
        Nonempty (CloseReopenCensus (same ▸ close) opened)) :
    ∃ same : retry = report.closeState, close.run = .ok () close.finished ∧
      (⟨CheckpointPowerCut.physical before close.finished.files.image.2.2, close.finished.files.owners⟩ :
        LockedFileState FileImage) = report.released ∧
      ∃ (layout : CanonicalKeeperLayout report.released.image before.history)
        (opened : CheckpointHeldOpen input directory layout report.publication)
        (session : SegmentedSession) (final : LockedFileState FileImage) (after : SegmentedWriterState),
        report.Reopened (.closed : SegmentedFailureRelease writer) opened session final after ∧
        Nonempty (CloseReopenCensus (same ▸ close) opened) := by
  have same := failed.unchanged (by simp [closeState])
  subst retry
  exact ⟨rfl, report.reopensAfterCachedClose ready close unlocked (reads rfl)⟩

end ObservedCheckpointRunDirectoryFailure

end Alvoki.Storage.DiskSession
