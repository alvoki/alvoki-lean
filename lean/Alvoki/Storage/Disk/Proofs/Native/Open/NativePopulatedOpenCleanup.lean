import Alvoki.Storage.Disk.Proofs.Recovery.NativeRawManifestStatError

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair SyncHandleRouting

variable {heap stream : Type} {view : OpenCloseHeapView heap FileImage} {entry : heap}
  {source : RawMarkedOpenInterpreter heap stream} {input : FilePath} {directory : DiskDirectory}
  {admission : CensusOpenAdmissionReports input directory (view.descriptors entry) (view.files entry)}
  {raw : RawOpenAdmissionReport admission view source.calls entry}

local notation "syncer" => source.keeperCallbacks.withFileReads source.fileCalls

variable (source) in
/-- The fixed worker stops at an error from the first root fsync.
No later unlink or keeper operation executes after this error. -/
theorem RawMarkedOpenInterpreter.workerRejectsRootAuthorization
    (directory : DiskDirectory) (lock root : IO.FS.Handle)
    (cache : DiskTable.OpenSyncFiles)
    (cached : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
    {before checked atCheckpoint prepared issued reached : heap}
    {cause : IO.Error} {metadata : IO.FS.Metadata} {plan : Plan} {opened : Reopened} {size : Nat}
    (flat : rejectFlatWalWith directory (optionalMetadataWith (source.calls.lookup (directory.file .wal)))
      before = .ok () checked)
    (marked : optionalMetadataWith (source.calls.lookup (directory.file .walBoundary)) checked = .ok (some metadata) atCheckpoint)
    (ready : source.prepareMarkedRead directory pending atCheckpoint = .ok (plan, opened, size) prepared)
    (valid : plan.valid = true) (exactSize : plan.keeperBytes.size = plan.keeperSize) (bounded : plan.keeperSize ≤ size)
    (loaded : AlignedKeeperCacheCallbacks.getDirectory syncer cached prepared = .ok (some root) issued)
    (syncFailed : AlignedKeeperCacheCallbacks.sync syncer root issued = .error cause reached) :
    source.worker cached active pending directory lock cache before =
      .error (IO.userError s!"sync failed for '{directory.path}': {cause}") reached := by
  let diagnostic := IO.userError s!"sync failed for '{directory.path}': {cause}"
  let sync := AlignedKeeperCacheCallbacks.syncPaths syncer directory.path cached active pending
  have barrier : sync #[directory.path] prepared = .error diagnostic reached := by
    dsimp only [sync]
    rw [AlignedKeeperCacheCallbacks.syncPaths, SyncPathGroup.run_single]
    simp [syncWithHandles, Bind.bind, EStateM.bind, loaded, syncFailed, Pure.pure, EStateM.pure]
    rfl
  have stopped : finishBoundedMarkedOpen directory plan size source.remove
      (source.stage.stage pending (AlignedKeeperCacheCallbacks.modifyPending syncer)) sync source.rename
      prepared = .error diagnostic reached := by
    by_cases fast : plan.newer = [] ∧ size = plan.keeperSize <;>
      simp [finishBoundedMarkedOpen, fast, valid, exactSize, bounded, Bind.bind, EStateM.bind, runRepairPlan, barrier]
  unfold RawMarkedOpenInterpreter.prepareMarkedRead at ready
  dsimp only [sync] at stopped
  simp only [RawMarkedOpenInterpreter.worker, recoverHealthyMarkedWithRefs, recoverSegmentedWalWith,
    reopenMarkedBoundedWithCachedExtents, Bind.bind, EStateM.bind, flat, marked, Option.isSome_some, ↓reduceIte, ready, stopped]
  rfl

/-- Apply the observed descriptor drops of the actual cache disposal.
A drop depends on handle lifetime, so several cells can share one drop
and a handle retained outside the cache can survive. Preserve the file
image of the heap where the worker returned its error. -/
theorem RawOpenAdmissionReport.finalizesFailedWorker
    (raw : RawOpenAdmissionReport admission view source.calls entry)
    (seed : OpenSyncCacheAllocations admission.opened view source.init raw.afterFlock)
    {cause : IO.Error} {reached afterDisposal afterUnlock : heap}
    (worker : source.worker seed.directoryRef seed.activeRef seed.pendingRef directory raw.lock
      (RawMarkedOpenInterpreter.makeCache directory seed.directoryRef seed.activeRef seed.pendingRef)
      seed.afterPending = .error cause reached)
    (dispose : source.dispose (RawMarkedOpenInterpreter.makeCache directory seed.directoryRef seed.activeRef seed.pendingRef)
      reached = .ok () afterDisposal)
    {drops : List LockReferenceDrop}
    (disposalCensus : view.descriptors afterDisposal = (view.descriptors reached).afterDrops drops)
    (disposalFiles : view.files afterDisposal = view.files reached)
    (unlockResult : Except IO.Error Unit)
    (unlocked : source.calls.unlock raw.lock afterDisposal = match unlockResult with
      | .ok () => .ok () afterUnlock
      | .error diagnostic => .error diagnostic afterUnlock)
    (unlockCensus : view.descriptors afterUnlock = view.descriptors afterDisposal)
    (unlockFiles : view.files afterUnlock = RawOpenCacheDisposal.filesAfterUnlock directory (view.files afterDisposal) unlockResult)
    (finalized : RawOpenErrorLockFinalization view directory source.release raw.lock admission.owner afterUnlock) :
    source.openTable input entry = .error (RawOpenCacheDisposal.diagnosticAfterUnlock cause unlockResult) finalized.reached ∧
    view.descriptors finalized.reached = ((view.descriptors reached).afterDrops drops).afterDrops [admission.owner.closeEvent] ∧
    (view.files finalized.reached).image = (view.files reached).image := by
  have actual := raw.returnsFailedMarkedInterpreter source seed worker dispose unlockResult unlocked finalized.finalized
  have finalCensus := finalized.census.trans
    (congrArg (·.afterDrops [admission.owner.closeEvent]) (unlockCensus.trans disposalCensus))
  refine ⟨actual, finalCensus, ?_⟩
  have lockLive : (view.descriptors afterUnlock).references admission.owner.description ≠ [] :=
    List.ne_nil_of_mem ((view.descriptors afterUnlock).mem_references.mpr ⟨_, finalized.live, rfl, rfl⟩)
  have image : (view.files finalized.reached).image = (view.files afterUnlock).image := by
    rw [finalized.files]
    simp [DescriptorInventory.dropLockState, lockLive, HeldLockReferences.afterFileDrops]
  rw [image, unlockFiles, disposalFiles]
  cases unlockResult with
  | ok result => cases result; rfl
  | error => rfl

end Alvoki.Storage.DiskSession
