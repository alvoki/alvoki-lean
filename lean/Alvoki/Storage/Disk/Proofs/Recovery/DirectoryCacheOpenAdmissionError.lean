import Alvoki.Storage.Disk.Proofs.Recovery.DirectoryCacheCapture
import Alvoki.Storage.Disk.Proofs.Recovery.SegmentedRetryTrace

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

/-- A read-only raw open error introduces no slot. A failed Lean handle
wrap can leave the fresh raw descriptor live at the resolved directory. -/
inductive DirectoryCacheFailureCensus (directory : DiskDirectory) (bindings : FilePath → Option Nat)
    (initial : DescriptorInventory) : DescriptorInventory → Prop where
  | rawOpenFailed : DirectoryCacheFailureCensus directory bindings initial initial
  | handleWrapFailed (raw : DescriptorSlot) (free : ∀ previous ∈ initial.slots, previous.address ≠ raw.address)
      (fresh : initial.references raw.description = [])
      (bound : bindings directory.path = some (initial.inode raw.description)) :
      DirectoryCacheFailureCensus directory bindings initial (initial.insert raw free)

theorem DirectoryCacheFailureCensus.inodes {directory bindings initial reached}
    (census : DirectoryCacheFailureCensus directory bindings initial reached) : reached.inode = initial.inode := by
  cases census <;> rfl

/-- An allocated directory slot belongs to a fresh description. Neither
raw error changes the references of the acquired lock description. -/
theorem DirectoryCacheFailureCensus.lockReferences {directory bindings initial reached} {owner : DescriptorSlot}
    (census : DirectoryCacheFailureCensus directory bindings initial reached) (live : owner ∈ initial.slots) :
    reached.references owner.description = initial.references owner.description := by
  cases census with
  | rawOpenFailed => rfl
  | handleWrapFailed raw free fresh _ =>
    have distinct : raw.description ≠ owner.description := by
      intro same
      have lock : owner.reference ∈ initial.references raw.description :=
        initial.mem_references.mpr ⟨owner, live, rfl, same.symm⟩
      rw [fresh] at lock
      exact List.not_mem_nil lock
    rw [DescriptorInventory.references_insert, ite_eq_right distinct]

private abbrev NativeState := DescriptorInventory × FileImage
private abbrev Handle := DescriptorInventory × DescriptorSlot × Nat

/-- The directory-read open is reported after acquisition by the
append-open slot. Its reached census and file image are explicit. -/
structure DirectoryCacheOpenErrorReports (directory : DiskDirectory) (before : LockedFileState FileImage) where
  initial : DescriptorInventory
  owner : DescriptorSlot
  lockLive : owner ∈ initial.slots
  bindings : FilePath → Option Nat
  lockBound : bindings (directory.file .lock) = some (initial.inode owner.description)
  flock : DescriptorSlot → Except IO.Error Bool
  acquired : flock owner = .ok true
  acquisition : TryLockObserves before.owners directory (flock owner)
  nextRef : Nat
  unlock : UnlockReport
  localUnlock : unlock.LocalFlock
  openDirectory : FilePath → EStateM IO.Error NativeState Handle
  cause : IO.Error
  reached : DescriptorInventory
  census : DirectoryCacheFailureCensus directory bindings initial reached
  failed : openDirectory directory.path (initial, before.image) = .error cause (reached, before.image)

/-- Pass the data image from a census-bearing failure to the bounded
retry. The admitted result still records the reached raw census. -/
def CachedOpenPrefixFailure.projectFiles {census image files : Type} {directory : DiskDirectory}
    {before : LockedFileState image} {initial : census}
    (failure : CachedOpenPrefixFailure files directory
      (⟨(initial, before.image), before.owners⟩ : LockedFileState (census × image))) :
    CachedOpenPrefixFailure files directory before where
  descriptor := failure.descriptor
  nextRef := failure.nextRef
  acquisition := failure.acquisition
  unlock := failure.unlock
  localUnlock := failure.localUnlock
  prepare := fun image =>
    match failure.prepare (initial, image) with
    | .ok prepared (_, reached) => .ok prepared reached
    | .error cause (_, reached) => .error cause reached
  cause := failure.cause
  reached := failure.reached.2
  failed := by rw [show failure.prepare (initial, before.image) = .error failure.cause failure.reached from failure.failed]

/-- The accepted descriptor drives the same lock, cache and recovery
suffix whether admission records its raw allocation or projects it away. -/
def runAdmittedCachedOpenAt {files image : Type} (directory : DiskDirectory) (slot : DescriptorSlot)
    (flock : DescriptorSlot → Except IO.Error Bool) (nextRef : Nat) (unlock : UnlockReport)
    (openFiles : DiskDirectory → DescriptorSlot → EStateM IO.Error image files)
    (lookup : FilePath → EStateM IO.Error image (Except IO.Error IO.FS.Metadata))
    (marked bootstrap : DiskDirectory → files → EStateM IO.Error image Reopened) :
    EStateM IO.Error (LockedFileState image) SegmentedSession :=
  runOpenWithInstallation directory slot.description nextRef (flock slot) unlock (do
    let cache ← openFiles directory slot
    recoverSegmentedWalWith (rejectFlatWalWith directory (optionalMetadataWith (lookup (directory.file .wal))))
      (optionalMetadataWith (lookup (directory.file .walBoundary))) (marked directory cache) (bootstrap directory cache))

/-- Interpret the admitted cached opener on observed callbacks. The lock
returned by admission guards initialization and the two route probes. -/
def runAdmittedCachedOpen {files image : Type} {input : FilePath} {directory : DiskDirectory} {owner : DescriptorSlot}
    (admission : OpenAdmissionReports input directory owner) (before : LockedFileState image)
    (flock : DescriptorSlot → Except IO.Error Bool) (nextRef : Nat) (unlock : UnlockReport)
    (openFiles : DiskDirectory → DescriptorSlot → EStateM IO.Error image files)
    (lookup : FilePath → EStateM IO.Error image (Except IO.Error IO.FS.Metadata))
    (marked bootstrap : DiskDirectory → files → EStateM IO.Error image Reopened) :
    EStateM.Result IO.Error (LockedFileState image) SegmentedSession :=
  DiskTable.withOpenAdmission input (fun path => liftExcept (admission.realPath path))
    (fun path => pure (admission.lookup path)) (fun path => liftExcept (admission.openAppend path))
    (fun resolved slot => runAdmittedCachedOpenAt resolved slot flock nextRef unlock openFiles lookup marked bootstrap)
    before

namespace DirectoryCacheOpenErrorReports

variable {directory : DiskDirectory} {before : LockedFileState FileImage}

/-- The failed cache initialization returns the original cause and the
exact reported census. No synchronization reference has been allocated. -/
theorem openError (observed : DirectoryCacheOpenErrorReports directory before) :
    runSyncFilesOpen (observed.openDirectory directory.path) (observed.initial, before.image) =
      .error observed.cause (observed.reached, before.image) :=
  runSyncFilesOpen_openError observed.failed

def nativeFailure (observed : DirectoryCacheOpenErrorReports directory before) :
    CachedOpenPrefixFailure (Cache Handle) directory
      (⟨(observed.initial, before.image), before.owners⟩ : LockedFileState NativeState) where
  descriptor := observed.owner.description
  nextRef := observed.nextRef
  acquisition := observed.acquired ▸ observed.acquisition
  unlock := observed.unlock
  localUnlock := observed.localUnlock
  prepare := runSyncFilesOpen (observed.openDirectory directory.path)
  cause := observed.cause
  reached := (observed.reached, before.image)
  failed := observed.openError

def projectedFailure (observed : DirectoryCacheOpenErrorReports directory before) :
    CachedOpenPrefixFailure (Cache Handle) directory before :=
  observed.nativeFailure.projectFiles

/-- The native-shaped admission executes the directory cache initialization
under the opened lock before the locked flat-WAL check and marker dispatch. -/
def runWithAdmission {input : FilePath} (observed : DirectoryCacheOpenErrorReports directory before)
    (admission : OpenAdmissionReports input directory observed.owner)
    (lookup : FilePath → EStateM IO.Error NativeState (Except IO.Error IO.FS.Metadata))
    (marked bootstrap : DiskDirectory → Cache Handle → EStateM IO.Error NativeState Reopened) :
    EStateM.Result IO.Error (LockedFileState NativeState) SegmentedSession :=
  runAdmittedCachedOpen admission ⟨(observed.initial, before.image), before.owners⟩
    observed.flock observed.nextRef observed.unlock
    (fun resolved _ => runSyncFilesOpen (observed.openDirectory resolved.path)) lookup marked bootstrap

/-- Failure stops before either recovery route, returning the exact raw
state under local unlock precedence. The projected state extends the same
bounded retry without choosing a checkpoint or authorizing repair. -/
theorem continuesAfterError {input : FilePath} {source : LockedFileState FileImage} {admits : Target → Prop}
    (observed : DirectoryCacheOpenErrorReports directory before)
    (admission : OpenAdmissionReports input directory observed.owner)
    (lookup : FilePath → EStateM IO.Error NativeState (Except IO.Error IO.FS.Metadata))
    (marked bootstrap : DiskDirectory → Cache Handle → EStateM IO.Error NativeState Reopened)
    (prior : BoundedReopenTrace directory admits source before) :
    let failed := observed.projectedFailure
    observed.runWithAdmission admission lookup marked bootstrap = .error failed.error observed.nativeFailure.after ∧
    BoundedReopenTrace directory admits source failed.after ∧
    observed.nativeFailure.after.image = (observed.reached, failed.after.image) ∧
    observed.nativeFailure.after.owners = failed.after.owners ∧
    observed.reached.references observed.owner.description = observed.initial.references observed.owner.description ∧
    match observed.unlock with
    | .success => failed.error = observed.cause ∧ failed.after.owners (directory.file .lock) = none
    | .failure cleanup _ =>
      failed.error = cleanup ∧ failed.after.owners (directory.file .lock) = some observed.owner.description := by
  intro failed
  refine ⟨?_, .cachedPrefixFailed prior failed rfl, rfl, rfl, observed.census.lockReferences observed.lockLive, ?_⟩
  · unfold runWithAdmission runAdmittedCachedOpen
    rw [admission.admits]
    unfold runAdmittedCachedOpenAt
    rw [observed.acquired]
    exact observed.nativeFailure.run_error _
  · exact failed.cleanupOutcome

end DirectoryCacheOpenErrorReports
end Alvoki.Storage.DiskSession
