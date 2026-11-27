import Alvoki.Storage.Disk.Proofs.Native.Open.NativeRawOpenAdmission

namespace Alvoki.Storage.DiskSession

open System

variable {heap : Type}

/-- The no-follow check immediately before opening the canonical LOCK. -/
def RawOpenAdmissionCallbacks.checkLock (calls : RawOpenAdmissionCallbacks heap) (directory : DiskDirectory) :
    EStateM IO.Error heap Unit := do
  if let some metadata ← optionalMetadataWith (calls.lookup (directory.file .lock)) then
    checkPrivateRegularWith (directory.file .lock) metadata

/-- Run the actual admission source only as far as the returned append
handle. The pair is passed to flock by the public open continuation. -/
def RawOpenAdmissionCallbacks.beforeFlock (calls : RawOpenAdmissionCallbacks heap) (input : FilePath) :
    EStateM IO.Error heap (DiskDirectory × IO.FS.Handle) :=
  DiskTable.withOpenAdmission input calls.realPath calls.lookup calls.openAppend
    (fun directory handle => pure (directory, handle))

private theorem RawOpenAdmissionCallbacks.admissionPrefix (calls : RawOpenAdmissionCallbacks heap) (input : FilePath)
    (continueOpen : DiskDirectory → IO.FS.Handle → EStateM IO.Error heap α) :
    DiskTable.withOpenAdmission input calls.realPath calls.lookup calls.openAppend continueOpen = (do
      let directory ← DiskDirectory.openWith calls.realPath input
      rejectFlatWalWith directory (optionalMetadataWith (calls.lookup (directory.file .wal)))
      calls.checkLock directory
      let handle ← calls.openAppend (directory.file .lock)
      continueOpen directory handle) := by
  simp only [DiskTable.withOpenAdmission, checkLock, bind_assoc]
  congr 1
  funext directory
  congr 1
  funext _
  congr 1
  funext metadata
  cases metadata <;> simp

/-- Every ordinary prefix return comes from the first failing callback
or guard at its actual reached heap, or the exact append handle. -/
inductive RawOpenPrefixReturn (calls : RawOpenAdmissionCallbacks heap) (input : FilePath) (entry : heap) :
    EStateM.Result IO.Error heap (DiskDirectory × IO.FS.Handle) → Prop where
  | resolveError {cause : IO.Error} {reached : heap}
      (resolved : DiskDirectory.openWith calls.realPath input entry = .error cause reached) :
      RawOpenPrefixReturn calls input entry (.error cause reached)
  | flatError {directory : DiskDirectory} {afterResolve reached : heap} {cause : IO.Error}
      (resolved : DiskDirectory.openWith calls.realPath input entry = .ok directory afterResolve)
      (flat : rejectFlatWalWith directory (optionalMetadataWith (calls.lookup (directory.file .wal)))
        afterResolve = .error cause reached) :
      RawOpenPrefixReturn calls input entry (.error cause reached)
  | lockGuardError {directory : DiskDirectory} {afterResolve afterFlat reached : heap} {cause : IO.Error}
      (resolved : DiskDirectory.openWith calls.realPath input entry = .ok directory afterResolve)
      (flat : rejectFlatWalWith directory (optionalMetadataWith (calls.lookup (directory.file .wal)))
        afterResolve = .ok () afterFlat)
      (checked : calls.checkLock directory afterFlat = .error cause reached) :
      RawOpenPrefixReturn calls input entry (.error cause reached)
  | appendError {directory : DiskDirectory} {afterResolve afterFlat afterLock reached : heap} {cause : IO.Error}
      (resolved : DiskDirectory.openWith calls.realPath input entry = .ok directory afterResolve)
      (flat : rejectFlatWalWith directory (optionalMetadataWith (calls.lookup (directory.file .wal)))
        afterResolve = .ok () afterFlat)
      (checked : calls.checkLock directory afterFlat = .ok () afterLock)
      (appended : calls.openAppend (directory.file .lock) afterLock = .error cause reached) :
      RawOpenPrefixReturn calls input entry (.error cause reached)
  | appended {directory : DiskDirectory} {handle : IO.FS.Handle} {afterResolve afterFlat afterLock reached : heap}
      (resolved : DiskDirectory.openWith calls.realPath input entry = .ok directory afterResolve)
      (flat : rejectFlatWalWith directory (optionalMetadataWith (calls.lookup (directory.file .wal)))
        afterResolve = .ok () afterFlat)
      (checked : calls.checkLock directory afterFlat = .ok () afterLock)
      (appended : calls.openAppend (directory.file .lock) afterLock = .ok handle reached) :
      RawOpenPrefixReturn calls input entry (.ok (directory, handle) reached)

theorem RawOpenAdmissionCallbacks.classifiesBeforeFlock (calls : RawOpenAdmissionCallbacks heap)
    (input : FilePath) (entry : heap) : RawOpenPrefixReturn calls input entry (calls.beforeFlock input entry) := by
  rw [beforeFlock, calls.admissionPrefix]
  simp only [Bind.bind, EStateM.bind]
  cases resolved : DiskDirectory.openWith calls.realPath input entry with
  | error cause reached =>
    exact .resolveError resolved
  | ok directory afterResolve =>
    dsimp only
    cases flat : rejectFlatWalWith directory (optionalMetadataWith (calls.lookup (directory.file .wal))) afterResolve with
    | error cause reached => exact .flatError resolved flat
    | ok _ afterFlat =>
      dsimp only
      cases checked : calls.checkLock directory afterFlat with
      | error cause reached => exact .lockGuardError resolved flat checked
      | ok _ afterLock =>
        dsimp only
        cases appended : calls.openAppend (directory.file .lock) afterLock with
        | error cause reached => exact .appendError resolved flat checked appended
        | ok handle reached => exact .appended resolved flat checked appended

/-- Recover the exact successful prefix stages from the append handle
returned by the fixed admission interpreter. The stages can change
the raw heap before the checked lock is opened. -/
theorem RawOpenAdmissionCallbacks.beforeFlock_steps (calls : RawOpenAdmissionCallbacks heap) {input : FilePath}
    {entry afterAppend : heap} {directory : DiskDirectory} {handle : IO.FS.Handle}
    (opened : calls.beforeFlock input entry = .ok (directory, handle) afterAppend) :
    ∃ afterResolve afterFlat afterGuard,
      DiskDirectory.openWith calls.realPath input entry = .ok directory afterResolve ∧
      rejectFlatWalWith directory (optionalMetadataWith (calls.lookup (directory.file .wal))) afterResolve =
        .ok () afterFlat ∧
      calls.checkLock directory afterFlat = .ok () afterGuard ∧
      calls.openAppend (directory.file .lock) afterGuard = .ok handle afterAppend := by
  have classified := calls.classifiesBeforeFlock input entry
  rw [opened] at classified
  cases classified with
  | appended resolved flat checked appended => exact ⟨_, _, _, resolved, flat, checked, appended⟩

/-- The public open calls flock on precisely the handle and heap from
the prefix. A failed prefix returns directly without cache allocation,
recovery, or attempting an unlock. -/
theorem RawOpenAdmissionCallbacks.runsAfterPrefix (calls : RawOpenAdmissionCallbacks heap) (input : FilePath)
    (init : OpenSyncCacheCallbacks heap)
    (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
    (recovery : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap α) (entry : heap) :
    calls.runOpen input init makeCache recovery entry =
      match calls.beforeFlock input entry with
      | .error cause reached => .error cause reached
      | .ok (directory, handle) reached =>
        openWithLock (calls.flock handle) (fun _ => IO.userError s!"database already open: {directory.path}")
          (fun _ => calls.unlock handle) (fun _ => do
            let cache ← openSyncFilesWith (init.openDirectory directory.path) init.newRef init.newRef init.newRef makeCache
            recovery directory handle cache) reached := by
  unfold RawOpenAdmissionCallbacks.runOpen RawOpenAdmissionCallbacks.beforeFlock
  rw [calls.admissionPrefix, calls.admissionPrefix]
  simp only [Bind.bind, EStateM.bind]
  cases DiskDirectory.openWith calls.realPath input entry with
  | error cause reached => rfl
  | ok directory resolved =>
    dsimp only
    cases rejectFlatWalWith directory (optionalMetadataWith (calls.lookup (directory.file .wal))) resolved with
    | error cause reached => rfl
    | ok _ checked =>
      dsimp only
      cases calls.checkLock directory checked with
      | error cause reached => rfl
      | ok _ guarded =>
        dsimp only
        cases calls.openAppend (directory.file .lock) guarded <;> rfl

end Alvoki.Storage.DiskSession
