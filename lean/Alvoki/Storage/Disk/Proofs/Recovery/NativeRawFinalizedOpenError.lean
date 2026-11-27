import Alvoki.Storage.Disk.Proofs.Native.Open.NativeOpenErrorLockFinalization
import Alvoki.Storage.Disk.NativeRawOpenCacheDisposal

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {heap α : Type} {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {admission : CensusOpenAdmissionReports input directory inventory retry}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap}
  {calls : RawOpenAdmissionCallbacks heap} {entry : heap}
  {admitted : RawOpenAdmissionReport admission view calls entry}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}

/-- The caller-visible result preserves the diagnostic and exact ordered
descriptor drops of the same cache and acquired lock. -/
abbrev RawOpenCacheDisposal.FinalizedAt {before : heap}
    (seen : RawOpenCacheDisposal (admitted := admitted) seed before)
    (recover : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap α)
    (cause : IO.Error) (workerImage : FileImage)
    {release : IO.FS.Handle → heap → heap}
    (finalized : RawOpenErrorLockFinalization view directory release admitted.lock admission.owner seen.reached) : Prop :=
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
      finishFailedOpen (calls.runOpen input init makeCache (seen.errorScope recover)) release admitted.lock entry =
        .error (seen.diagnostic cause) finalized.reached ∧
      view.descriptors finalized.reached =
        ((view.descriptors before).afterDrops [admission.cached.closeEvent]).afterDrops [admission.owner.closeEvent] ∧
      (view.files finalized.reached).image = workerImage ∧
      (TryLockObserves (view.files finalized.reached).owners directory (.ok true) ↔
        seen.unlockResult = .ok () ∨ (view.descriptors finalized.reached).references admission.owner.description = [])

/-- The read-only cleanup keeps the admitted file image. -/
abbrev RawOpenCacheDisposal.Finalized {before : heap}
    (seen : RawOpenCacheDisposal (admitted := admitted) seed before)
    (recover : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap α)
    (cause : IO.Error)
    {release : IO.FS.Handle → heap → heap}
    (finalized : RawOpenErrorLockFinalization view directory release admitted.lock admission.owner seen.reached) : Prop :=
  seen.FinalizedAt recover cause retry.image finalized

/-- Compose the two reported runtime drops around local unlock. The
failed open uses the same canonical cache constructor, worker and lock
handle and returns its chosen diagnostic after the final lock close. -/
theorem RawOpenCacheDisposal.returnsAfterLockFinalizationAt {before : heap}
    (seen : RawOpenCacheDisposal (admitted := admitted) seed before)
    (recover : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap α)
    (cause : IO.Error) {workerImage : FileImage} (returned : seen.ReturnedAt recover cause workerImage)
    {release : IO.FS.Handle → heap → heap}
    (finalized : RawOpenErrorLockFinalization view directory release admitted.lock admission.owner seen.reached) :
    seen.FinalizedAt recover cause workerImage finalized := by
  obtain ⟨cacheOpen, makeCache, cache, isOpen, source, initialized, uses, ran, _, droppedCache, _, _, stable, _, owner⟩ := returned
  obtain ⟨result, _, _, files, available⟩ := finalized.returns _ ran seen.unlockResult owner
  refine ⟨cacheOpen, makeCache, cache, isOpen, source, initialized, uses, result, ?_, files.trans stable, available⟩
  rw [finalized.census, droppedCache]

/-- Specialize the caller-visible cleanup to a read-only failed open. -/
theorem RawOpenCacheDisposal.returnsAfterLockFinalization {before : heap}
    (seen : RawOpenCacheDisposal (admitted := admitted) seed before)
    (recover : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap α)
    (cause : IO.Error) (returned : seen.Returned recover cause)
    {release : IO.FS.Handle → heap → heap}
    (finalized : RawOpenErrorLockFinalization view directory release admitted.lock admission.owner seen.reached) :
    seen.Finalized recover cause finalized :=
  seen.returnsAfterLockFinalizationAt recover cause returned finalized

end Alvoki.Storage.DiskSession
