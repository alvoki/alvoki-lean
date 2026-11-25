import Alvoki.Storage.Disk.NativeRawManifestDecodeError
import Alvoki.Storage.Disk.NativeRawFinalizedOpenError

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {heap stream α : Type} {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {admission : CensusOpenAdmissionReports input directory inventory retry}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap}
  {calls : RawOpenAdmissionCallbacks heap} {entry : heap}
  {admitted : RawOpenAdmissionReport admission view calls entry}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {fault : NativeManifestDecodeError admission} {fileCalls : MarkedTemporaryReadCalls heap}
  {release : IO.FS.Handle → heap → heap}

/-- After the malformed manifest's temporary release, the held scope
disposes the initialized cache. Local unlock selects the diagnostic,
then the reported lock finalizer reaches the caller-visible state. -/
theorem RawManifestDecodeRead.returnsFinalized
    (seen : RawManifestDecodeRead (admitted := admitted) fault seed fileCalls)
    (disposal : RawOpenCacheDisposal (admitted := admitted) seed seen.closed)
    (finalized : RawOpenErrorLockFinalization view directory release admitted.lock admission.owner disposal.reached)
    (directoryCalls : MarkedDirectoryReadCalls heap stream) (callbacks : AlignedKeeperCacheCallbacks heap)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (install : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → Reopened → EStateM IO.Error heap α) :
    let recover := fun resolved lock cache =>
      calls.recoverMarkedWithCacheRefs fileCalls directoryCalls callbacks seed.directoryRef seed.activeRef seed.pendingRef
        remove write rename bootstrap resolved cache >>= install resolved lock cache
    ∃ (cacheOpen : IO DiskTable.OpenSyncFiles)
      (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
        IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
      (cache : DiskTable.OpenSyncFiles),
      DiskTable.OpenSyncFiles.IsOpenAction directory.path cacheOpen ∧
      cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
        (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
        (fun value => liftM (IO.mkRef value)) makeCache ∧
      openSyncFilesWith (init.openDirectory directory.path) init.newRef init.newRef init.newRef makeCache
        admitted.afterFlock = .ok cache seed.afterPending ∧
      cache.UsesCacheReferences seed.activeRef seed.pendingRef seed.directoryRef ∧
      finishFailedOpen (calls.runOpen input init makeCache (disposal.errorScope recover)) release admitted.lock entry =
        .error (disposal.diagnostic (IO.userError fault.cause)) finalized.reached ∧
      view.descriptors finalized.reached =
        ((view.descriptors seen.closed).afterDrops [admission.cached.closeEvent]).afterDrops [admission.owner.closeEvent] ∧
      (view.descriptors finalized.reached).references fault.manifest.calls.slot.description = [] ∧
      (view.files finalized.reached).image = retry.image ∧
      (view.files finalized.reached).image.directory.active.manifest = some fault.bytes ∧
      (TryLockObserves (view.files finalized.reached).owners directory (.ok true) ↔
        disposal.unlockResult = .ok () ∨ (view.descriptors finalized.reached).references admission.owner.description = []) := by
  intro recover
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, files, _⟩ := seed.installs
  have returned := disposal.returns recover (IO.userError fault.cause) (fun rawCache => by
    simp only [recover, Bind.bind, EStateM.bind, seen.stopsBeforeWal directoryCalls callbacks remove write rename bootstrap])
    (seen.frame.files.trans files)
  obtain ⟨action, makeCache, cache, native, source, initialized, references, ran, census, retained, available⟩ :=
    disposal.returnsAfterLockFinalization recover _ returned finalized
  refine ⟨action, makeCache, cache, native, source, initialized, references, ran, census, ?_, retained,
    (congrArg (fun image => image.directory.active.manifest) retained).trans fault.selected, available⟩
  rw [census, DescriptorInventory.references_afterDrops, DescriptorInventory.references_afterDrops,
    seen.readsSelected.2.2.2.2.2]
  rfl

end Alvoki.Storage.DiskSession
