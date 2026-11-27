import Alvoki.Storage.Disk.Proofs.Bootstrap.BootstrapExecution
import Alvoki.Storage.Disk.Proofs.Bootstrap.BootstrapZeroCreateError
import Alvoki.Storage.Disk.LockCensusOpenAdmission

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

private abbrev Handle := DescriptorInventory × DescriptorSlot × Nat
private abbrev BootstrapFiles := LockedFileState WalSegmentRotation.State

variable {directory : DiskDirectory} {before : BootstrapFiles}
  {calls : BootstrapOpenCalls (Cache Handle) directory before}
  {captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls}

/-- Match a bootstrap worker's cache to the exact stateful append-open,
flock and directory open in the shared native admission schedule. The
worker's projected admission uses the same reached primitive results. -/
structure CapturedBootstrapAdmission {input : FilePath} (capture : BootstrapCacheOpen calls.toBootstrapAdmissionCalls)
    (admission : OpenAdmissionReports input directory calls.slot) (entry : DescriptorInventory) where
  raw : CensusOpenAdmissionReports input directory entry before
  owner : raw.owner = calls.slot
  cached : raw.cached = capture.cached
  afterAppend : capture.initial = entry.insert raw.owner raw.free
  sameView : raw.view = capture.view
  sameRoot : raw.root = capture.root
  sameDirectoryOpen : raw.opened.opened directory.path (capture.initial, raw.held) =
    capture.opened.opened directory.path (capture.initial, raw.held)
  existingLock : raw.lockMetadata.isSome = true
  guardedLookup : ∀ path, path = directory.file .wal ∨ path = directory.file .lock →
    raw.lookup path (entry, before) = .ok (admission.lookup path) (entry, before)
  heldLookup : ∀ path, path = directory.file .wal ∨ path = directory.file .walBoundary →
    raw.lookup path (raw.reached, raw.held) = .ok (calls.lookup path) (raw.reached, raw.held)

namespace CapturedBootstrapAdmission

variable {input : FilePath} {admission : OpenAdmissionReports input directory calls.slot} {entry : DescriptorInventory}

theorem reached (report : CapturedBootstrapAdmission captured admission entry) :
    report.raw.reached = captured.reached := by
  have slots := congrArg DescriptorInventory.slots report.afterAppend
  have inodes := congrArg DescriptorInventory.inode report.afterAppend
  simp only [CensusOpenAdmissionReports.reached, BootstrapCacheOpen.reached,
    DescriptorInventory.insert, DescriptorInventory.mk.injEq, report.cached]
  exact ⟨congrArg (captured.cached :: ·) slots.symm, inodes.symm⟩

theorem cache (report : CapturedBootstrapAdmission captured admission entry) : report.raw.cache = captured.cache := by
  simp only [CensusOpenAdmissionReports.cache, BootstrapCacheOpen.cache, report.reached, report.cached]

/-- Use the same held worker and cleanup from the native schedule at this
entry. This exposes the exact admission reached by the ordinary open. -/
theorem admits {result : Type} (report : CapturedBootstrapAdmission captured admission entry)
    (recover : DiskDirectory → DescriptorSlot → CensusDirectoryCache →
      EStateM IO.Error (OpenCensus WalSegmentRotation.State) result) :
    report.raw.run recover =
      (tryCatchThe IO.Error (recover directory calls.slot captured.cache) fun cause => do
        report.raw.unlock calls.slot ()
        throw cause) (captured.reached, report.raw.held) := by
  rw [report.raw.run_reachesRecovery, report.owner, report.cache, report.reached]

private abbrev Worker := DiskDirectory → CensusDirectoryCache → EStateM IO.Error (OpenCensus WalSegmentRotation.State) Reopened
private abbrev Install := DiskDirectory → DescriptorSlot → CensusDirectoryCache → Reopened →
  EStateM IO.Error (OpenCensus WalSegmentRotation.State) SegmentedSession

def run (report : CapturedBootstrapAdmission captured admission entry) (marked bootstrap : Worker)
    (install : Install) : EStateM.Result IO.Error (OpenCensus WalSegmentRotation.State) SegmentedSession :=
  report.raw.run fun resolved owner files => do
    let opened ← recoverSegmentedWalWith
      (rejectFlatWalWith resolved (optionalMetadataWith (report.raw.lookup (resolved.file .wal))))
      (optionalMetadataWith (report.raw.lookup (resolved.file .walBoundary)))
      (marked resolved files) (bootstrap resolved files)
    install resolved owner files opened

/-- The captured retry observes the canonical marker absent after it has
acquired the lock. The shared dispatcher enters that same cache's
bootstrap worker and bypasses the marked branch. -/
theorem dispatches (report : CapturedBootstrapAdmission captured admission entry)
    (marked bootstrap : Worker) (install : Install) :
    report.run marked bootstrap install =
      (tryCatchThe IO.Error
        (bootstrap directory captured.cache >>= install directory calls.slot captured.cache) fun cause => do
        report.raw.unlock calls.slot ()
        throw cause) (captured.reached, report.raw.held) := by
  have flat := report.heldLookup (directory.file .wal) (.inl rfl)
  have marker := report.heldLookup (directory.file .walBoundary) (.inr rfl)
  obtain ⟨_, _, flatAbsent⟩ := calls.flatAbsent
  obtain ⟨_, _, markerAbsent⟩ := calls.markerAbsent.2
  rw [report.reached] at flat marker
  simp only [run, report.admits, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch,
    recoverSegmentedWalWith, rejectFlatWalWith, Bind.bind, EStateM.bind,
    optionalMetadataWith, flat, marker, flatAbsent, markerAbsent, Pure.pure, EStateM.pure,
    Option.isSome_none, Bool.false_eq_true, ↓reduceIte]

end CapturedBootstrapAdmission

namespace BootstrapZeroCreateError

variable {listed : BootstrapCheckedListing captured}

/-- Before another open, either local unlock released this lock or the
last reported reference to its still-held owner was disposed. -/
inductive DisposedForRetry (failure : BootstrapZeroCreateError listed) :
    DescriptorInventory → BootstrapFiles → Prop where
  | unlocked (released : calls.unlock = .success) (drops : List LockReferenceDrop) :
      DisposedForRetry failure (listed.scan.afterClose.afterDrops drops) failure.final
  | dropped {inventory : DescriptorInventory} {files : BootstrapFiles}
      (observed : LockCensusTrace directory calls.slot.description listed.scan.afterClose failure.final inventory files)
      (last : inventory.references calls.slot.description = []) : DisposedForRetry failure inventory files

theorem DisposedForRetry.released {failure : BootstrapZeroCreateError listed}
    (disposed : failure.DisposedForRetry inventory files) :
    files.image = before.image ∧ inventory.inode = listed.scan.afterClose.inode ∧
    TryLockObserves files.owners directory (.ok true) := by
  cases disposed with
  | unlocked released drops => exact ⟨rfl, rfl, failure.admits.mpr released⟩
  | dropped observed last =>
    obtain ⟨same, _, inodes, available⟩ := failure.admitsAfterDrops observed
    exact ⟨same, inodes, available.mpr last⟩

private theorem lockAtListing {files : BootstrapFiles}
    {operation : BootstrapOpenCalls (Cache Handle) directory files}
    {cache : BootstrapCacheOpen operation.toBootstrapAdmissionCalls}
    (checked : BootstrapCheckedListing cache) :
    cache.view.child cache.root "LOCK" = some checked.lifetime.lock ∧
    cache.view.modelObject checked.lifetime.lock = checked.scan.afterClose.inode operation.slot.description := by
  have child := checked.lifetime.lockEntry
  have identified := checked.lifetime.identifiesLock
  rw [checked.sameView, checked.sameRoot] at child
  rw [checked.sameView] at identified
  rw [checked.scan.afterClose_eq]
  exact ⟨child, identified⟩

/-- Continue the bootstrap after the real first keeper-create error. The
next admitted call starts from the reached descriptor inventory and empty
files. Its capture sees the same directory and LOCK; its own successful
keeper and marker effects supply the first ready client prefix. -/
theorem reopensAfterCreateError {input nextInput : FilePath}
    (failure : BootstrapZeroCreateError listed) (cleanup : failure.Cleanup)
    (admission : OpenAdmissionReports input directory calls.slot)
    {inventory : DescriptorInventory} {files : BootstrapFiles}
    (disposed : failure.DisposedForRetry inventory files)
    {nextCalls : BootstrapOpenCalls (Cache Handle) directory files}
    {nextCapture : BootstrapCacheOpen nextCalls.toBootstrapAdmissionCalls}
    {nextList : BootstrapCheckedListing nextCapture}
    {nextKeeper : BootstrapZeroKeeperRoute nextList} {nextMarker : BootstrapMarkerCustody nextList}
    {opening : OpenAdmissionReports nextInput directory nextCalls.slot}
    (acquired : CapturedBootstrapAdmission nextCapture opening inventory)
    (namespaceView : nextCapture.view = failure.afterView) (root : nextCapture.root = captured.root)
    (publication : BootstrapKeeperMarkerHandoff nextKeeper nextMarker)
    (effects : BootstrapKeeperMarkerHandoff.ReturnedCensus nextMarker) :
    calls.run admission = .error failure.diagnostic failure.final ∧
    TryLockObserves files.owners directory (.ok true) ∧
    files.image = before.image ∧
    acquired.raw.reached.inode acquired.raw.owner.description = listed.scan.afterClose.inode calls.slot.description ∧
    acquired.raw.reached.inode acquired.raw.cached.description = listed.scan.afterClose.inode captured.cached.description ∧
    (∀ marked bootstrap install, acquired.run marked bootstrap install =
      (tryCatchThe IO.Error
        (bootstrap directory nextCapture.cache >>= install directory nextCalls.slot nextCapture.cache) fun cause => do
        acquired.raw.unlock nextCalls.slot ()
        throw cause) (nextCapture.reached, acquired.raw.held)) ∧
    ∃ returned : BootstrapClientStart directory nextCalls.slot.description (nextCalls.run opening),
      let state : NativeReadyState :=
        ⟨returned.session, returned.writer, effects.reached, nextCapture.cache, nextCalls.slot, nextCapture.cached⟩
      nextCalls.run opening = .ok state.session returned.final ∧
      state.files.owners = returned.final.owners ∧ state.files.image.directory = returned.final.image.metadata ∧
      publication.afterMarkerNames (renderWalSegmentName 0) = [some nextKeeper.keeperChild] ∧
      publication.afterMarkerNames "WAL.commit" = [some nextMarker.stageChild.child] ∧
      ((nextMarker.inodeState.completeFileSync nextMarker.inodeState.active).settleBinding).crashBytes
        nextKeeper.settledImage.active = [ByteArray.empty] ∧
      ((nextMarker.inodeState.completeFileSync nextMarker.inodeState.active).settleBinding).crashBytes
        nextMarker.inodeState.active = [WAL.Boundary.encode 0] ∧
      NativeReadyReadPrefix (.ok state.session (state.census, state.files)) state [] [] [] state := by
  obtain ⟨unchanged, _, available⟩ := disposed.released
  have oldLock := lockAtListing listed
  have nextLock := lockAtListing nextList
  have view := namespaceView.trans failure.unchanged
  have lockName := nextLock.1
  rw [view, root] at lockName
  have sameLock := Option.some.inj (lockName.symm.trans oldLock.1)
  have beforeLock := oldLock.2
  have afterLock := nextLock.2
  rw [view, sameLock, nextList.scan.afterClose_eq] at afterLock
  have oldRoot := captured.captures.2.2.2.2
  have nextRoot := nextCapture.captures.2.2.2.2
  rw [view, root] at nextRoot
  have lockObject := afterLock.symm.trans beforeLock
  have rootObject := nextRoot.symm.trans oldRoot
  obtain ⟨returned, ran, owners, directoryImage, _, _, keeperName, markerName, keeperBytes, markerBytes, ready⟩ :=
    publication.startsNativeReadPrefixFromEmpty opening (unchanged.trans failure.empty) effects
  refine ⟨(failure.returns cleanup admission).1, available, unchanged, ?_, ?_, acquired.dispatches, returned, ran,
    owners, directoryImage, keeperName, markerName, keeperBytes, markerBytes, ready⟩
  · rw [acquired.reached, acquired.owner]
    exact lockObject
  · rw [acquired.reached, acquired.cached, listed.scan.afterClose_eq]
    exact rootObject

end BootstrapZeroCreateError

end Alvoki.Storage.DiskSession
