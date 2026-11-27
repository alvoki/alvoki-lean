import Alvoki.Storage.Disk.Proofs.Recovery.DirectoryCacheOpenAdmissionError
import Alvoki.Storage.Disk.Proofs.Filesystem.LockCensusOpenAdmission

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

private abbrev RawOpenState := LockedFileState (DescriptorInventory × FileImage)
private abbrev Handle := DescriptorInventory × DescriptorSlot × Nat

/-- An admitted open reaches cache initialization after the reported
append-open inserts its exact lock slot. The retained files belong to
the original settled checkpoint and WAL and are unaffected by the cache error. -/
structure NativeCacheOpenRejection (input : FilePath) (directory : DiskDirectory) (before : CensusOpenState) where
  failure : DirectoryCacheOpenErrorReports directory before.2
  admission : OpenAdmissionReports input directory failure.owner
  free : ∀ previous ∈ before.1.slots, previous.address ≠ failure.owner.address
  fresh : before.1.references failure.owner.description = []
  identity : failure.initial = before.1.insert failure.owner free
  append : FilePath → EStateM IO.Error RawOpenState DescriptorSlot
  opened : append (directory.file .lock) ⟨(before.1, before.2.image), before.2.owners⟩ =
    .ok failure.owner ⟨(failure.initial, before.2.image), before.2.owners⟩
  view : DirectoryReadNamespace
  root : DeviceInode
  lock : RunChildLookup root "LOCK" view
  rootedLock : view.modelObject lock.child = failure.initial.inode failure.owner.description
  directoryObject : failure.bindings directory.path = some (view.modelObject root)

namespace NativeCacheOpenRejection

variable {input : FilePath} {directory : DiskDirectory} {before : CensusOpenState}
  (observed : NativeCacheOpenRejection input directory before)

def run (lookup : FilePath → EStateM IO.Error (DescriptorInventory × FileImage) (Except IO.Error IO.FS.Metadata))
    (marked bootstrap : DiskDirectory → Cache Handle → EStateM IO.Error (DescriptorInventory × FileImage) Reopened) :
    EStateM.Result IO.Error RawOpenState SegmentedSession :=
  DiskTable.withOpenAdmission input (fun path => liftExcept (observed.admission.realPath path))
    (fun path => pure (observed.admission.lookup path)) observed.append
    (fun resolved slot => runAdmittedCachedOpenAt resolved slot observed.failure.flock
      observed.failure.nextRef observed.failure.unlock
      (fun path _ => runSyncFilesOpen (observed.failure.openDirectory path.path))
      lookup marked bootstrap)
    ⟨(before.1, before.2.image), before.2.owners⟩

/-- The same raw slot reaches the flock and cache attempt. When that
attempt fails, the chosen cleanup error and census are its exact return. -/
theorem returns (lookup : FilePath → EStateM IO.Error (DescriptorInventory × FileImage) (Except IO.Error IO.FS.Metadata))
    (marked bootstrap : DiskDirectory → Cache Handle → EStateM IO.Error (DescriptorInventory × FileImage) Reopened) :
    observed.run lookup marked bootstrap = .error observed.failure.projectedFailure.error observed.failure.nativeFailure.after := by
  let first : RawOpenState := ⟨(before.1, before.2.image), before.2.owners⟩
  let atLock : RawOpenState := ⟨(observed.failure.initial, before.2.image), before.2.owners⟩
  have resolved :
      (liftExcept (observed.admission.realPath input) : EStateM IO.Error RawOpenState FilePath) first =
        .ok directory.path first := by simp [observed.admission.resolved, liftExcept, Pure.pure, EStateM.pure]
  obtain ⟨_, _, absent⟩ := observed.admission.flatAbsent
  have flat :
      (optionalMetadataWith (pure (observed.admission.lookup (directory.file .wal))) : EStateM IO.Error RawOpenState _) first =
        .ok none first := by simp [optionalMetadataWith, absent, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
  have route : observed.run lookup marked bootstrap =
      runAdmittedCachedOpenAt directory observed.failure.owner observed.failure.flock
        observed.failure.nextRef observed.failure.unlock
        (fun path _ => runSyncFilesOpen (observed.failure.openDirectory path.path))
        lookup marked bootstrap atLock := by
    unfold run
    rcases observed.admission.lockGuard with ⟨_, _, missing⟩ | ⟨metadata, present, regular, privateFile⟩
    · have lock :
          (optionalMetadataWith (pure (observed.admission.lookup (directory.file .lock))) : EStateM IO.Error RawOpenState _) first =
            .ok none first := by simp [optionalMetadataWith, missing, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
      rw [DiskTable.withOpenAdmission_lockOpen _ _ _ _ resolved flat lock (by simp), observed.opened]
    · have lock :
          (optionalMetadataWith (pure (observed.admission.lookup (directory.file .lock))) : EStateM IO.Error RawOpenState _) first =
            .ok (some metadata) first := by simp [optionalMetadataWith, present, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
      have safe : (metadata.type == .file && metadata.numLinks == 1) = true := by rw [regular, privateFile]; rfl
      rw [DiskTable.withOpenAdmission_lockOpen _ _ _ _ resolved flat lock
        (fun _ equal => Option.some.inj equal ▸ safe), observed.opened]
  rw [route, runAdmittedCachedOpenAt, observed.failure.acquired]
  exact observed.failure.nativeFailure.run_error _

def sameObjects (lock root : Nat) : Prop :=
  observed.view.modelObject observed.lock.child = lock ∧ observed.view.modelObject observed.root = root

def afterDrops (drops : List LockReferenceDrop) : CensusOpenState :=
  let reached := observed.failure.reached
  let files := observed.failure.projectedFailure.after
  (reached.afterDrops drops, match observed.failure.unlock with
    | .success => files
    | .failure _ _ => reached.dropLockState observed.failure.owner.description drops directory files)

def availableAfter (drops : List LockReferenceDrop) : Bool :=
  match observed.failure.unlock with
  | .success => true
  | .failure _ _ => ((observed.afterDrops drops).1.references observed.failure.owner.description).isEmpty

theorem censusInodes (drops : List LockReferenceDrop) : (observed.afterDrops drops).1.inode = before.1.inode := by
  have entry : observed.failure.initial.inode = before.1.inode := by rw [observed.identity]; rfl
  exact observed.failure.census.inodes.trans entry

/-- A successful local unlock leaves admission available. If it failed,
only a last reported drop of the same description allows the next
attempt. In either case selected file bytes and other locks stay fixed. -/
theorem disposes (drops : List LockReferenceDrop) :
    (observed.afterDrops drops).2.image = before.2.image ∧
    (TryLockObserves (observed.afterDrops drops).2.owners directory (.ok true) ↔ observed.availableAfter drops = true) ∧
    ∀ path, path ≠ directory.file .lock → (observed.afterDrops drops).2.owners path = before.2.owners path := by
  let failed := observed.failure.projectedFailure
  have beforeOther (path : FilePath) (other : path ≠ directory.file .lock) :
      failed.after.owners path = before.2.owners path := by
    simp [failed, CachedOpenPrefixFailure.after, LockOwners.set, other]
  cases cleanup : observed.failure.unlock with
  | success =>
    have vacant : TryLockObserves failed.after.owners directory (.ok true) := by
      intro _
      simp [failed, DirectoryCacheOpenErrorReports.projectedFailure, CachedOpenPrefixFailure.projectFiles,
        DirectoryCacheOpenErrorReports.nativeFailure, CachedOpenPrefixFailure.after, cleanup, LockOwners.set]
    simp only [afterDrops, cleanup, availableAfter, iff_true, failed] at *
    exact ⟨rfl, vacant, beforeOther⟩
  | failure cause released =>
    have owned : failed.after.owners.Owns directory observed.failure.owner.description := by
      simp [failed, DirectoryCacheOpenErrorReports.projectedFailure, CachedOpenPrefixFailure.projectFiles,
        DirectoryCacheOpenErrorReports.nativeFailure, CachedOpenPrefixFailure.after, cleanup, LockOwners.set, LockOwners.Owns]
    have live : observed.failure.reached.references observed.failure.owner.description ≠ [] := by
      rw [observed.failure.census.lockReferences observed.failure.lockLive]
      exact List.ne_nil_of_mem (observed.failure.initial.mem_references.mpr
        ⟨observed.failure.owner, observed.failure.lockLive, rfl, rfl⟩)
    let disposed := (LockCensusTrace.start owned live).drops drops
    have result := disposed.reached.2.2
    have vacant := disposed.freshFlockAllowed
    simp only [afterDrops, availableAfter, cleanup, List.isEmpty_iff]
    refine ⟨?_, vacant, ?_⟩
    · exact (congrArg LockedFileState.image result).trans (by split <;> rfl)
    · intro path other
      have same := congrArg (fun files : LockedFileState FileImage => files.owners path) result
      split at same
      · exact same.trans (by simpa only [LockOwners.set, ite_eq_right other] using beforeOther path other)
      · exact same.trans (beforeOther path other)

end NativeCacheOpenRejection
end Alvoki.Storage.DiskSession
