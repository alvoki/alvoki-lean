import Alvoki.Storage.Disk.NativeRawOpenReturn

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {heap α : Type}

/-- A non-ENOENT no-follow error stops the optional metadata reader. -/
theorem rawOptionalMetadataError (lookup : EStateM IO.Error heap (Except IO.Error IO.FS.Metadata))
    {before : heap} {cause : IO.Error} (reported : lookup before = .ok (.error cause) before)
    (notMissing : ∀ path message, cause ≠ .noFileOrDirectory path 2 message) :
    optionalMetadataWith lookup before = .error cause before := by
  simp only [optionalMetadataWith, Bind.bind, EStateM.bind, reported]
  rfl

/-- The held source dispatcher runs its late guards before selecting
recovery, and installs only after the selected worker succeeds. -/
def RawOpenAdmissionCallbacks.recoverAndInstall (calls : RawOpenAdmissionCallbacks heap)
    (marked bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (install : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → Reopened → EStateM IO.Error heap α)
    (directory : DiskDirectory) (lock : IO.FS.Handle) (cache : DiskTable.OpenSyncFiles) : EStateM IO.Error heap α :=
  recoverSegmentedWalWith
    (rejectFlatWalWith directory (optionalMetadataWith (calls.lookup (directory.file .wal))))
    (optionalMetadataWith (calls.lookup (directory.file .walBoundary)))
    (marked directory cache) (bootstrap directory cache) >>= install directory lock cache

/-- The worker's exact recovered value is the installer input. A worker
error returns on its reached heap without invoking the installer. -/
inductive OpenRecoveryWorkerReturn (worker : EStateM IO.Error heap Reopened)
    (install : Reopened → EStateM IO.Error heap α) (entry : heap) : EStateM.Result IO.Error heap α → Prop where
  | workerError {cause : IO.Error} {reached : heap}
      (failed : worker entry = .error cause reached) :
      OpenRecoveryWorkerReturn worker install entry (.error cause reached)
  | reachedInstaller {opened : Reopened} {recovered : heap} {result : EStateM.Result IO.Error heap α}
      (ran : worker entry = .ok opened recovered) (installed : install opened recovered = result) :
      OpenRecoveryWorkerReturn worker install entry result

/-- Classify the held recovery by the actual checked path and marker
lookup before replay or bootstrap. The same selected worker determines
whether the installer runs and what it receives. -/
inductive HeldOpenRecoveryReturn (flat : EStateM IO.Error heap Unit)
    (marker : EStateM IO.Error heap (Option IO.FS.Metadata))
    (marked bootstrap : EStateM IO.Error heap Reopened) (install : Reopened → EStateM IO.Error heap α)
    (entry : heap) : EStateM.Result IO.Error heap α → Prop where
  | flatError {cause : IO.Error} {reached : heap}
      (failed : flat entry = .error cause reached) :
      HeldOpenRecoveryReturn flat marker marked bootstrap install entry (.error cause reached)
  | markerError {cause : IO.Error} {afterFlat reached : heap}
      (checked : flat entry = .ok () afterFlat) (failed : marker afterFlat = .error cause reached) :
      HeldOpenRecoveryReturn flat marker marked bootstrap install entry (.error cause reached)
  | marked {metadata : IO.FS.Metadata} {afterFlat afterMarker : heap} {result : EStateM.Result IO.Error heap α}
      (checked : flat entry = .ok () afterFlat) (found : marker afterFlat = .ok (some metadata) afterMarker)
      (ran : OpenRecoveryWorkerReturn marked install afterMarker result) :
      HeldOpenRecoveryReturn flat marker marked bootstrap install entry result
  | bootstrap {afterFlat afterMarker : heap} {result : EStateM.Result IO.Error heap α}
      (checked : flat entry = .ok () afterFlat) (absent : marker afterFlat = .ok none afterMarker)
      (ran : OpenRecoveryWorkerReturn bootstrap install afterMarker result) :
      HeldOpenRecoveryReturn flat marker marked bootstrap install entry result

/-- The production dispatcher and its installer bind use the observed
results of their fixed callbacks, in order and at their reached heaps. -/
theorem HeldOpenRecoveryReturn.classifies (flat : EStateM IO.Error heap Unit)
    (marker : EStateM IO.Error heap (Option IO.FS.Metadata))
    (marked bootstrap : EStateM IO.Error heap Reopened) (install : Reopened → EStateM IO.Error heap α) (entry : heap) :
    HeldOpenRecoveryReturn flat marker marked bootstrap install entry
      ((recoverSegmentedWalWith flat marker marked bootstrap >>= install) entry) := by
  have follows (worker : EStateM IO.Error heap Reopened) (before : heap) :
      OpenRecoveryWorkerReturn worker install before ((worker >>= install) before) := by
    simp only [Bind.bind, EStateM.bind]
    cases ran : worker before with
    | error cause reached => exact .workerError ran
    | ok opened reached => exact .reachedInstaller ran rfl
  simp only [recoverSegmentedWalWith, Bind.bind, EStateM.bind]
  cases noFlat : flat entry with
  | error cause reached => exact .flatError noFlat
  | ok checked afterFlat =>
    cases checked
    dsimp only
    cases found : marker afterFlat with
    | error cause reached => exact .markerError noFlat found
    | ok metadata afterMarker =>
      cases metadata with
      | none => exact .bootstrap noFlat found (follows bootstrap afterMarker)
      | some metadata => exact .marked noFlat found (follows marked afterMarker)

/-- The outer open classifier and the held route classifier use the
same recovery program, lookup, lock handle and synchronization record.
This covers ordinary returns under that callback interpretation. -/
theorem RawOpenAdmissionCallbacks.classifiesSegmentedOpenReturn
    (calls : RawOpenAdmissionCallbacks heap) (input : FilePath)
    (init : OpenSyncCacheCallbacks heap)
    (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
    (marked bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (install : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → Reopened → EStateM IO.Error heap α)
    (entry : heap) :
    let flat := fun (directory : DiskDirectory) =>
      rejectFlatWalWith directory (optionalMetadataWith (calls.lookup (directory.file .wal)))
    let marker := fun (directory : DiskDirectory) => optionalMetadataWith (calls.lookup (directory.file .walBoundary))
    let recover := calls.recoverAndInstall marked bootstrap install
    let openCache := fun directory : DiskDirectory =>
      openSyncFilesWith (init.openDirectory directory.path) init.newRef init.newRef init.newRef makeCache
    RawOpenReturn calls input entry openCache recover (calls.runOpen input init makeCache recover entry) ∧
      ∀ directory lock cache afterCache,
        HeldOpenRecoveryReturn (flat directory) (marker directory) (marked directory cache) (bootstrap directory cache)
          (install directory lock cache) afterCache (recover directory lock cache afterCache) := by
  intro flat marker recover openCache
  exact ⟨calls.classifiesOpenReturn input init makeCache recover entry,
    fun directory lock cache afterCache => HeldOpenRecoveryReturn.classifies (flat directory) (marker directory)
      (marked directory cache) (bootstrap directory cache) (install directory lock cache) afterCache⟩

end Alvoki.Storage.DiskSession
