import Alvoki.Storage.Disk.BootstrapZeroKeeperCustody
import Alvoki.Storage.Disk.LockCensusTrace

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

private abbrev Handle := DescriptorInventory × DescriptorSlot × Nat
private abbrev BootstrapCensus := DescriptorInventory × LockedFileState WalSegmentRotation.State
private abbrev BootstrapWorker := Cache Handle × BootstrapCensus
private abbrev keeperPath (directory : DiskDirectory) := directory.file (.walSegment 0)

variable {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
  {calls : BootstrapOpenCalls (Cache Handle) directory before}
  {captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls} {listed : BootstrapCheckedListing captured}

private def held (before : LockedFileState WalSegmentRotation.State) (directory : DiskDirectory) (slot : DescriptorSlot) :=
  { before with owners := before.owners.set (directory.file .lock) (some slot.description) }

private def projectCreate : EStateM.Result IO.Error BootstrapWorker Unit → EStateM.Result IO.Error WalSegmentRotation.State Unit
  | .ok value reached => .ok value reached.2.2.image
  | .error cause reached => .error cause reached.2.2.image

/-- The markerless worker has checked the listing and canonical segment-zero
absence. The exclusive create reports a no-effect error at that path. The
same returned raw error supplies the actual `SyncFiles.create` callback. -/
structure BootstrapZeroCreateError (listed : BootstrapCheckedListing captured) where
  empty : before.image = ⟨DirectoryPublication.Image.settled ⟨none, none⟩, .absent⟩
  lookup : FilePath → Except IO.Error IO.FS.Metadata
  absent : ∃ name message, lookup (keeperPath directory) = .error (.noFileOrDirectory name 2 message)
  zeroProbe : calls.readEmpty (keeperPath directory) =
    WalSegmentRotation.readEmptyWith (.ok (lookup (keeperPath directory))) (keeperPath directory) WAL.Boundary.missingOpenMarker
  keeperMissing : captured.view.child captured.root (renderWalSegmentName 0) = none
  markerMissing : captured.view.child captured.root "WAL.commit" = none
  stageMissing : captured.view.child captured.root "WAL.commit.next" = none
  afterView : DirectoryReadNamespace
  unchanged : afterView = captured.view
  openExclusive : FilePath → EStateM IO.Error BootstrapCensus Handle
  cause : IO.Error
  failed : openExclusive (keeperPath directory) (listed.scan.afterClose, held before directory calls.slot) =
    .error cause (listed.scan.afterClose, held before directory calls.slot)
  projected : calls.createEmpty captured.cache (keeperPath directory) before.image =
    projectCreate (stageFreshWithCache (keeperPath directory) ByteArray.empty (fun path _ => openExclusive path)
      (captured.cache, listed.scan.afterClose, held before directory calls.slot))

namespace BootstrapZeroCreateError

private theorem missingKeeper (seen : BootstrapZeroCreateError listed) :
    calls.readEmpty (keeperPath directory) = .ok none := by
  obtain ⟨_, _, lookup⟩ := seen.absent
  rw [seen.zeroProbe]
  have absent : optionalMetadataWith (.ok (seen.lookup (keeperPath directory))) =
      (Except.ok none : Except IO.Error (Option IO.FS.Metadata)) := by
    simp only [optionalMetadataWith, Bind.bind, Except.bind, lookup, Pure.pure, Except.pure]
  simp only [WalSegmentRotation.readEmptyWith, Bind.bind, Except.bind, absent, Pure.pure, Except.pure]

theorem create (seen : BootstrapZeroCreateError listed) :
    stageFreshWithCache (keeperPath directory) ByteArray.empty (fun path _ => seen.openExclusive path)
      (captured.cache, listed.scan.afterClose, held before directory calls.slot) =
    .error seen.cause (captured.cache, listed.scan.afterClose, held before directory calls.slot) :=
  stageFreshWithCache_error _ _ _ _ seen.failed

/-- The absent zero keeper triggers the actual creation schedule. The
first error stops the worker before either sync or marker publication. -/
theorem worker (seen : BootstrapZeroCreateError listed) :
    calls.bootstrapAt directory captured.cache before.image = .error seen.cause before.image := by
  have empty : before.image.observeSuccessor = none := Except.ok.inj (calls.zeroRead.symm.trans seen.missingKeeper)
  have failed : calls.createEmpty captured.cache (keeperPath directory) before.image = .error seen.cause before.image := by
    rw [seen.projected, seen.create]
    rfl
  rw [calls.reachesPublication captured.cache listed.entries.1 listed.entries.2, empty]
  simp only [bootstrapEmptyWith, bootstrapEmptyWithMarker, WalSegmentRotation.runAt_fileEffects, WalSegmentRotation.observeSuccessorWith,
    Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, Bool.false_eq_true, ↓reduceIte, failed]

/-- The original owner is still live when the failed create hands control
back to `openWithLock`. The actual local unlock supplies the disposition
of that same slot and the reached files and inventory. -/
structure Cleanup (seen : BootstrapZeroCreateError listed) where
  unlock : DescriptorSlot → Unit → EStateM IO.Error BootstrapCensus Unit
  localFlock : calls.unlock.LocalFlock
  returned : unlock calls.slot () (listed.scan.afterClose, held before directory calls.slot) =
    match calls.unlock with
    | .success => .ok () (listed.scan.afterClose,
        { before with owners := before.owners.set (directory.file .lock) none })
    | .failure cause _ => .error cause (listed.scan.afterClose, held before directory calls.slot)

def final (_seen : BootstrapZeroCreateError listed) : LockedFileState WalSegmentRotation.State :=
  { before with owners := before.owners.set (directory.file .lock) (match calls.unlock with
    | .success => none
    | .failure _ _ => some calls.slot.description) }

def diagnostic (seen : BootstrapZeroCreateError listed) : IO.Error :=
  match calls.unlock with
  | .success => seen.cause
  | .failure cause _ => cause

/-- Interpret the held create and unlock continuation at the census
reached by the checked listing. A failure never calls `continuation`. -/
noncomputable def runCleanup (seen : BootstrapZeroCreateError listed) (cleanup : seen.Cleanup)
    (continuation : EStateM IO.Error BootstrapWorker SegmentedSession) :
    EStateM.Result IO.Error BootstrapWorker SegmentedSession :=
  (tryCatchThe IO.Error
    (stageFreshWithCache (keeperPath directory) ByteArray.empty (fun path _ => seen.openExclusive path) >>= fun _ => continuation)
    fun cause => do
      (fun (cache, state) => match cleanup.unlock calls.slot () state with
        | .ok () reached => .ok () (cache, reached)
        | .error cause reached => .error cause (cache, reached))
      throw cause) (captured.cache, listed.scan.afterClose, held before directory calls.slot)

theorem cleanupReturns (seen : BootstrapZeroCreateError listed) (cleanup : seen.Cleanup)
    (continuation : EStateM IO.Error BootstrapWorker SegmentedSession) :
    seen.runCleanup cleanup continuation = .error seen.diagnostic (captured.cache, listed.scan.afterClose, seen.final) := by
  have returned := cleanup.returned
  cases outcome : calls.unlock <;> simp only [outcome] at returned
  all_goals
    simp only [runCleanup, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch, Bind.bind, EStateM.bind,
      throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.Backtrackable.restore, EStateM.dummyRestore,
      seen.create, returned, final, diagnostic, outcome] <;> rfl

theorem admits (seen : BootstrapZeroCreateError listed) :
    TryLockObserves seen.final.owners directory (.ok true) ↔ calls.unlock = .success := by
  cases unlock : calls.unlock <;> simp [final, unlock, TryLockObserves, LockOwners.set]

/-- A failed unlock can be followed by reported descriptor events. The
next acquisition becomes available only after this owner's last reference
is gone. Those events leave the empty bootstrap file image intact. -/
theorem admitsAfterDrops (seen : BootstrapZeroCreateError listed)
    {reached : DescriptorInventory} {retry : LockedFileState WalSegmentRotation.State}
    (drops : LockCensusTrace directory calls.slot.description listed.scan.afterClose seen.final reached retry) :
    retry.image = before.image ∧ BootstrapValid retry.image ∧ reached.inode = listed.scan.afterClose.inode ∧
      (TryLockObserves retry.owners directory (.ok true) ↔ reached.references calls.slot.description = []) := by
  have image := congrArg LockedFileState.image drops.reached.2.2
  have same : retry.image = before.image := by split at image <;> exact image
  exact ⟨same, (same.trans seen.empty).symm ▸ bootstrap_fresh, drops.reached.2.1, drops.freshFlockAllowed⟩

/-- Native open returns no session after the failed zero-keeper creation.
Its raw error handoff and the file-state projection use the same observed
local unlock. The untouched empty data image and original captured
objects are available to the next reported admission. -/
theorem returns {input : FilePath} (seen : BootstrapZeroCreateError listed) (cleanup : seen.Cleanup)
    (admission : OpenAdmissionReports input directory calls.slot) :
    calls.run admission = .error seen.diagnostic seen.final ∧
    (∀ continuation, seen.runCleanup cleanup continuation =
      .error seen.diagnostic (captured.cache, listed.scan.afterClose, seen.final)) ∧
    seen.final.image = before.image ∧ BootstrapValid seen.final.image ∧
    seen.afterView.child captured.root (renderWalSegmentName 0) = none ∧
    seen.afterView.child captured.root "WAL.commit" = none ∧ seen.afterView.child captured.root "WAL.commit.next" = none ∧
    calls.slot ∈ listed.scan.afterClose.slots ∧ captured.cached ∈ listed.scan.afterClose.slots ∧
    (TryLockObserves seen.final.owners directory (.ok true) ↔ calls.unlock = .success) := by
  have raw := runOpenWithInstallation_acquiredRecoveryError directory calls.slot.description calls.nextRef calls.unlock
    (calls.bootstrapAt directory captured.cache) before seen.worker
  refine ⟨?_, seen.cleanupReturns cleanup, rfl, seen.empty.symm ▸ bootstrap_fresh, seen.unchanged.symm ▸ seen.keeperMissing,
    seen.unchanged.symm ▸ seen.markerMissing, seen.unchanged.symm ▸ seen.stageMissing,
    listed.retained.1, listed.retained.2.1, seen.admits⟩
  rw [calls.runMarkerless admission captured.captures.1, raw]
  cases outcome : calls.unlock with
  | success => simp [final, diagnostic, outcome]
  | failure cause released =>
    have stayedHeld : released = false := by simpa [UnlockReport.LocalFlock, outcome] using cleanup.localFlock
    subst released
    simp [final, diagnostic, outcome]

end BootstrapZeroCreateError

end Alvoki.Storage.DiskSession
