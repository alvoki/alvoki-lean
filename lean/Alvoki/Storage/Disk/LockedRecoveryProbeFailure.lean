import Alvoki.Storage.Disk.DirectoryCacheOpenAdmissionError

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

/-- The locked WAL lookup can fail or expose a flat WAL binding. The
marker lookup is reached only after the locked flat path was absent. -/
inductive LockedRecoveryProbeError (directory : DiskDirectory)
    (lookup : FilePath → Except IO.Error IO.FS.Metadata) : IO.Error → Prop where
  | flatLookup {cause : IO.Error}
      (reported : lookup (directory.file .wal) = .error cause)
      (propagated : ∀ name message, cause ≠ .noFileOrDirectory name 2 message) :
      LockedRecoveryProbeError directory lookup cause
  | flatPresent {metadata : IO.FS.Metadata}
      (reported : lookup (directory.file .wal) = .ok metadata) :
      LockedRecoveryProbeError directory lookup (IO.userError s!"unsupported flat WAL binding: '{directory.file .wal}'")
  | markerLookup {cause : IO.Error} {name message : String}
      (flatAbsent : lookup (directory.file .wal) = .error (.noFileOrDirectory name 2 message))
      (reported : lookup (directory.file .walBoundary) = .error cause)
      (propagated : ∀ filename reason, cause ≠ .noFileOrDirectory filename 2 reason) :
      LockedRecoveryProbeError directory lookup cause

private theorem optionalMetadata_nonmissingError {state : Type} (before : state) {cause : IO.Error}
    (propagated : ∀ name message, cause ≠ .noFileOrDirectory name 2 message) :
    (optionalMetadataWith (pure (.error cause)) : EStateM IO.Error state (Option IO.FS.Metadata)) before =
      .error cause before := by
  cases cause <;> try rfl
  rename_i name code message
  by_cases missing : code = 2
  · subst code
    exact False.elim (propagated name message rfl)
  · simp [optionalMetadataWith, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, throw,
      throwThe, MonadExceptOf.throw, EStateM.throw]

private def checkedPrefix {state files : Type} (directory : DiskDirectory)
    (openFiles : EStateM IO.Error state files) (lookup : FilePath → Except IO.Error IO.FS.Metadata) :
    EStateM IO.Error state (files × Option IO.FS.Metadata) := do
  let cache ← openFiles
  rejectFlatWalWith directory (optionalMetadataWith (pure (lookup (directory.file .wal))))
  let marker ← optionalMetadataWith (pure (lookup (directory.file .walBoundary)))
  return (cache, marker)

private theorem dispatch_eq_prefix {state files : Type} (directory : DiskDirectory)
    (openFiles : EStateM IO.Error state files) (lookup : FilePath → Except IO.Error IO.FS.Metadata)
    (marked bootstrap : files → EStateM IO.Error state Reopened) :
    (do
      let cache ← openFiles
      recoverSegmentedWalWith (rejectFlatWalWith directory (optionalMetadataWith (pure (lookup (directory.file .wal)))))
        (optionalMetadataWith (pure (lookup (directory.file .walBoundary)))) (marked cache) (bootstrap cache)) =
    (checkedPrefix directory openFiles lookup >>= fun (cache, marker) =>
      if marker.isSome then marked cache else bootstrap cache) := by
  simp only [checkedPrefix, recoverSegmentedWalWith, bind_assoc, pure_bind]

private theorem LockedRecoveryProbeError.prefixError {state files : Type}
    {directory : DiskDirectory} {lookup : FilePath → Except IO.Error IO.FS.Metadata} {cause : IO.Error}
    (failed : LockedRecoveryProbeError directory lookup cause)
    {openFiles : EStateM IO.Error state files} {before reached : state} {cache : files}
    (initialized : openFiles before = .ok cache reached) :
    checkedPrefix directory openFiles lookup before = .error cause reached := by
  cases failed with
  | flatLookup reported propagated =>
    have raw := optionalMetadata_nonmissingError reached propagated
    simp only [checkedPrefix, Bind.bind, EStateM.bind, initialized, rejectFlatWalWith, reported, raw]
  | flatPresent reported =>
    simp [checkedPrefix, rejectFlatWalWith, initialized, Bind.bind, EStateM.bind, optionalMetadataWith,
      reported, Pure.pure, EStateM.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
  | markerLookup absent reported propagated =>
    have raw := optionalMetadata_nonmissingError reached propagated
    have admitted : (rejectFlatWalWith directory (optionalMetadataWith
        (pure (lookup (directory.file .wal)))) : EStateM IO.Error state Unit) reached = .ok () reached := by
      simp [rejectFlatWalWith, optionalMetadataWith, Bind.bind, EStateM.bind, absent, Pure.pure, EStateM.pure]
    simp only [checkedPrefix, Bind.bind, EStateM.bind, initialized, admitted, reported, raw]

private abbrev NativeState := DescriptorInventory × FileImage
private abbrev Handle := DescriptorInventory × DescriptorSlot × Nat

/-- The same admitted lock reaches the reported directory handle
capture and the locked no-follow route probes. The phase ends on the
reported probe error before selecting a recovery callback. -/
structure LockedRecoveryProbeReports (directory : DiskDirectory) (before : LockedFileState FileImage) where
  initial : DescriptorInventory
  owner : DescriptorSlot
  cached : DescriptorSlot
  view : DirectoryReadNamespace
  root : DeviceInode
  captured : DirectoryCacheOpenReports directory initial owner cached
    ⟨before.image, before.owners.set (directory.file .lock) (some owner.description)⟩ view root
  bindings : FilePath → Option Nat
  lockBound : bindings (directory.file .lock) = some (initial.inode owner.description)
  flock : DescriptorSlot → Except IO.Error Bool
  acquired : flock owner = .ok true
  acquisition : TryLockObserves before.owners directory (flock owner)
  nextRef : Nat
  unlock : UnlockReport
  localUnlock : unlock.LocalFlock
  lookup : FilePath → Except IO.Error IO.FS.Metadata
  cause : IO.Error
  failed : LockedRecoveryProbeError directory lookup cause

namespace LockedRecoveryProbeReports

variable {directory : DiskDirectory} {before : LockedFileState FileImage}

def reached (observed : LockedRecoveryProbeReports directory before) : DescriptorInventory :=
  observed.initial.insert observed.cached observed.captured.free

def openFiles (observed : LockedRecoveryProbeReports directory before) (resolved : DiskDirectory)
    (slot : DescriptorSlot) : EStateM IO.Error NativeState (Cache Handle) := fun (inventory, image) =>
  let held : LockedFileState FileImage :=
    ⟨image, before.owners.set (resolved.file .lock) (some slot.description)⟩
  match runSyncFilesOpen (observed.captured.opened resolved.path) (inventory, held) with
  | .ok cache (reached, files) => .ok cache (reached, files.image)
  | .error cause (reached, files) => .error cause (reached, files.image)

theorem initialized (observed : LockedRecoveryProbeReports directory before) :
    observed.openFiles directory observed.owner (observed.initial, before.image) =
      .ok ⟨some (observed.reached, observed.cached, 0), none, []⟩ (observed.reached, before.image) := by
  have raw := observed.captured.captures.1
  simp [openFiles, raw, reached]

def nativeFailure (observed : LockedRecoveryProbeReports directory before) :
    CachedOpenPrefixFailure (Cache Handle × Option IO.FS.Metadata) directory
      (⟨(observed.initial, before.image), before.owners⟩ : LockedFileState NativeState) where
  descriptor := observed.owner.description
  nextRef := observed.nextRef
  acquisition := observed.acquired ▸ observed.acquisition
  unlock := observed.unlock
  localUnlock := observed.localUnlock
  prepare := checkedPrefix directory (observed.openFiles directory observed.owner) observed.lookup
  cause := observed.cause
  reached := (observed.reached, before.image)
  failed := observed.failed.prefixError observed.initialized

def projectedFailure (observed : LockedRecoveryProbeReports directory before) :
    CachedOpenPrefixFailure (Cache Handle × Option IO.FS.Metadata) directory before :=
  observed.nativeFailure.projectFiles

def runWithAdmission {input : FilePath} (observed : LockedRecoveryProbeReports directory before)
    (admission : OpenAdmissionReports input directory observed.owner)
    (marked bootstrap : DiskDirectory → Cache Handle → EStateM IO.Error NativeState Reopened) :
    EStateM.Result IO.Error (LockedFileState NativeState) SegmentedSession :=
  runAdmittedCachedOpen admission ⟨(observed.initial, before.image), before.owners⟩
    observed.flock observed.nextRef observed.unlock observed.openFiles
    (fun path => pure (observed.lookup path)) marked bootstrap

/-- The actual admitted dispatcher returns a failed locked flat or
marker probe through local unlock. The next bounded retry has the exact
unchanged data image and returned owner. The native-shaped result also
keeps the reached census of the successful directory capture. -/
theorem continuesAfterError {input : FilePath} {source : LockedFileState FileImage} {admits : Target → Prop}
    (observed : LockedRecoveryProbeReports directory before)
    (admission : OpenAdmissionReports input directory observed.owner)
    (marked bootstrap : DiskDirectory → Cache Handle → EStateM IO.Error NativeState Reopened)
    (prior : BoundedReopenTrace directory admits source before) :
    let failed := observed.projectedFailure
    observed.runWithAdmission admission marked bootstrap = .error failed.error observed.nativeFailure.after ∧
    BoundedReopenTrace directory admits source failed.after ∧
    observed.nativeFailure.after.image = (observed.reached, failed.after.image) ∧
    observed.nativeFailure.after.owners = failed.after.owners ∧
    observed.owner ∈ observed.reached.slots ∧ observed.cached ∈ observed.reached.slots ∧
    observed.view.modelObject observed.root = observed.reached.inode observed.cached.description ∧
    match observed.unlock with
    | .success => failed.error = observed.cause ∧ failed.after.owners (directory.file .lock) = none
    | .failure cleanup _ =>
      failed.error = cleanup ∧ failed.after.owners (directory.file .lock) = some observed.owner.description := by
  intro failed
  obtain ⟨_, ownerLive, directoryLive, _, object, _⟩ := observed.captured.captures
  refine ⟨?_, .cachedPrefixFailed prior failed rfl, rfl, rfl, ownerLive, directoryLive, object, ?_⟩
  · unfold runWithAdmission runAdmittedCachedOpen
    rw [admission.admits]
    unfold runAdmittedCachedOpenAt
    rw [observed.acquired, dispatch_eq_prefix]
    exact observed.nativeFailure.run_error _
  · exact failed.cleanupOutcome

end LockedRecoveryProbeReports
end Alvoki.Storage.DiskSession
