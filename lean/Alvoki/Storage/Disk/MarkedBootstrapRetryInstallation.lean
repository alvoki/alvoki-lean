import Alvoki.Storage.Disk.ObservedBootstrapRetry
import Alvoki.Storage.Disk.HeldWalInstallation

namespace Alvoki.Storage.WalSegmentRepair

/-- A bootstrap image whose visible marker already names the durable empty
segment. The directory can still have older admitted crash choices. -/
structure BootstrapMarkedZero (state : WalSegmentRotation.State) : Prop where
  noManifest : state.metadata.active.manifest = none
  zeroMarker : state.metadata.active.walBoundary = some (WAL.Boundary.encode 0)
  keeperDurable : state.successor = .durable

theorem BootstrapValid.markedZero {state : WalSegmentRotation.State} (valid : BootstrapValid state)
    (visible : state.metadata.active.walBoundary ≠ none) : BootstrapMarkedZero state := by
  obtain ⟨manifest, marker⟩ := valid.nextSelection
  obtain ⟨zero, durable⟩ := marker.resolve_left visible
  exact ⟨manifest, zero, durable⟩

/-- Represent the same bootstrap image in the bounded marked repair model.
The directory image includes the reached metadata scratch and every crash
choice. The validated empty WAL is the keeper at absolute offset zero. -/
def BootstrapMarkedZero.files {state : WalSegmentRotation.State} (_ : BootstrapMarkedZero state) : FileImage :=
  ⟨state.metadata, fun _ => none, .settled (some ByteArray.empty), .settled []⟩

def BootstrapMarkedZero.checkpoint {state : WalSegmentRotation.State}
    (_ : BootstrapMarkedZero state) : CheckpointPublication.Image :=
  ⟨state.metadata.project .manifest, fun _ _ => none⟩

end Alvoki.Storage.WalSegmentRepair

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair
open WAL.Boundary (CheckpointRepresentsPrefix)

private abbrev Handle := DescriptorInventory × DescriptorSlot × Nat

def _root_.Alvoki.Storage.WalSegmentRepair.BootstrapMarkedZero.layout {state : WalSegmentRotation.State}
    (zero : BootstrapMarkedZero state) : CanonicalKeeperLayout zero.files [] where
  range := ⟨0, 0⟩
  decoded := by
    change state.metadata.active.walRange = _
    simp [DirectoryPublication.Bindings.walRange, zero.noManifest, zero.zeroMarker, selectedCheckpointWatermark,
      WAL.Boundary.decode_encode, Except.toOption, Bind.bind, Option.bind]
  through := rfl
  first := 0
  sealed := []
  keeper := ⟨0, 0, ByteArray.empty⟩
  chain := .cons (segment := ⟨0, 0, ByteArray.empty⟩) (Nat.le_refl 0) (fun _ => rfl) rfl .endOfHistory
  covers := Nat.le_refl 0
  tail := ByteArray.empty
  visible := rfl

private abbrev locked {before : LockedFileState WalSegmentRotation.State}
    (zero : BootstrapMarkedZero before.image) : LockedFileState FileImage :=
  ⟨zero.files, before.owners⟩

private def restore {before : LockedFileState WalSegmentRotation.State}
    (files : FileImage) : WalSegmentRotation.State :=
  { before.image with metadata := files.directory }

private def projectMarked {before : LockedFileState WalSegmentRotation.State} :
    EStateM.Result IO.Error FileImage Reopened → EStateM.Result IO.Error WalSegmentRotation.State Reopened
  | .ok opened files => .ok opened (restore (before := before) files)
  | .error cause files => .error cause (restore (before := before) files)

/-- The bootstrap route and the cached marked worker are two projections of
the same open. The boundary equation fixes the worker and its raw reports,
without requiring a successful result. The held observations supply the
empty keeper read and both reached synchronization callbacks. -/
structure BootstrapMarkedRetryOpen {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
    {retry : BootstrapAdmissionCalls (Cache Handle) directory before}
    (captured : BootstrapCacheOpen retry) (zero : BootstrapMarkedZero before.image) where
  calls : MarkedRetryChunkCalls (Cache Handle) directory (locked zero)
  sameSlot : calls.slot = retry.slot
  sameCache : calls.cache = captured.cache
  sameNextRef : calls.nextRef = retry.nextRef
  sameMarkerLookup : calls.lookup (directory.file .walBoundary) zero.files =
    .ok (retry.lookup (directory.file .walBoundary)) zero.files
  reads : HeldWalInstallReads zero.layout calls
  held : HeldDirectoryMarkedRetryReports reads.operations zero.checkpoint
  heldView : held.lifetime.namespaceView = captured.view
  heldRoot : held.lifetime.root = captured.root
  readView : reads.view = held.lifetime.namespaceView
  readRoot : reads.root = held.lifetime.root
  authorization : ListedDirectoryAuthorization held
  metadata : HeldMarkedMetadata held
  repair : ListedAlignedKeeperRepair authorization
  synced :
    let input : LockedFileState FileImage :=
      ⟨zero.files.syncDirectory, before.owners.set (directory.file .lock) (some retry.slot.description)⟩
    authorization.fsync (authorization.keeper.inventory, authorization.keeper.slot, 0) input =
      .ok () {input with image := input.image.syncKeeper}
  projected : retry.marked directory captured.cache before.image =
    projectMarked (before := before) (reads.operations.markedAt directory captured.cache zero.files)

namespace BootstrapMarkedRetryOpen

variable {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
  {retry : BootstrapAdmissionCalls (Cache Handle) directory before} {captured : BootstrapCacheOpen retry}
  {zero : BootstrapMarkedZero before.image}

/-- A marked bootstrap retry returns the exact empty installation with
the directory's settled zero marker and its acquired lock. -/
def Installed (directory : DiskDirectory) (descriptor : Nat)
    (result : EStateM.Result IO.Error (LockedFileState WalSegmentRotation.State) SegmentedSession) : Prop :=
  ∃ (session : SegmentedSession) (after : LockedFileState WalSegmentRotation.State),
    result = .ok session after ∧ session.directory = directory ∧ session.descriptor = descriptor ∧
    session.phase = .ready ⟨.empty, 0, 0, 0⟩ ∧ after.owners.Owns directory descriptor ∧ BootstrapReady after.image

/-- The held marked listing starts with the directory slot and census
captured by this next admitted open. -/
theorem capturedDirectory (observed : BootstrapMarkedRetryOpen captured zero) :
    observed.calls.descriptors = captured.reached ∧ observed.held.lifetime.directorySlot = captured.cached ∧
    observed.calls.bindings (directory.file .lock) = captured.bindings (directory.file .lock) := by
  have cache := observed.held.capturedDirectory
  rw [show observed.reads.operations.cache = captured.cache from observed.sameCache] at cache
  have slots := Prod.mk.inj (Option.some.inj cache)
  have descriptors : observed.calls.descriptors = captured.reached := slots.1.symm
  refine ⟨descriptors, (Prod.mk.inj slots.2).1.symm, ?_⟩
  rw [observed.calls.lockObject, captured.lockObject, descriptors, observed.sameSlot]
  rfl

/-- The native directory identity and namespace observation agree across
cache capture, listing and the marked reads. The canonical zero keeper
comes from that same checked listing. -/
theorem sharedPhysicalDirectory (observed : BootstrapMarkedRetryOpen captured zero) :
    observed.held.lifetime.namespaceView = captured.view ∧ observed.held.lifetime.root = captured.root ∧
    observed.reads.view = captured.view ∧ observed.reads.root = captured.root ∧
    renderWalSegmentName 0 ∈ observed.reads.inventory.inventory.names := by
  have atRoot := observed.reads.wal
  rw [observed.readView, observed.readRoot] at atRoot
  exact ⟨observed.heldView, observed.heldRoot, observed.readView.trans observed.heldView,
    observed.readRoot.trans observed.heldRoot, (observed.held.selectedWalListed atRoot).2⟩

/-- The held marked worker computes its installation from the canonical
empty keeper and no selected checkpoint, using the two reached barriers. -/
theorem installed {input : FilePath} (observed : BootstrapMarkedRetryOpen captured zero)
    (admission : OpenAdmissionReports input directory retry.slot) :
    let calls := observed.calls
    let ops := observed.reads.operations
    CachedRetryInstalled (before := locked zero) ops.reported calls.descriptors calls.slot calls.bindings
      zero.checkpoint calls.liveRefs (ops.runWithAdmission (observed.sameSlot.symm ▸ admission)) := by
  intro calls ops
  have keeper : zero.files.keeper.Valid zero.layout.target.Accepts :=
    Publication.Image.settled_valid zero.layout.target.acceptsTrimmed
  have later : zero.files.later.Beyond zero.layout.range.through := by
    simp [BootstrapMarkedZero.files, LaterNames.settled, LaterNames.Beyond]
  have accepted : zero.checkpoint.AcceptsVersioned 0 (CheckpointRepresentsPrefix [])
      zero.files.directory.active.manifest := by
    change zero.checkpoint.AcceptsVersioned 0 (CheckpointRepresentsPrefix []) before.image.metadata.active.manifest
    rw [zero.noManifest]
    exact trivial
  have exactSync := observed.synced
  rw [← observed.sameSlot] at exactSync
  exact observed.repair.installs observed.metadata exactSync (observed.sameSlot.symm ▸ admission) keeper later
    (by intro start member; cases member) accepted trivial

/-- The retry dispatches to that same marked worker after acquiring its
lock. Its exact result installs the empty ready table and restores the
settled metadata to the bootstrap model. -/
theorem installs {input : FilePath} (observed : BootstrapMarkedRetryOpen captured zero)
    (admission : OpenAdmissionReports input directory retry.slot) (valid : BootstrapValid before.image)
    (marker : BootstrapRetryMarker retry)
    (bootstrap : DiskDirectory → Cache Handle → EStateM IO.Error WalSegmentRotation.State Reopened) :
    Installed directory retry.slot.description (retry.run bootstrap admission) := by
  let ops := observed.reads.operations
  have installed := observed.installed admission
  dsimp only at installed
  obtain ⟨opened, checkpoint, _, session, final, ran, path, description, phase, _, _, _, _, held, _, _, _, ready, _,
    selected, replay, generation, bytes, keeper, _⟩ := installed
  have fromSlot : ops.reported.inventory.descriptor = retry.slot.description :=
    ops.inventoryDescription.trans (congrArg DescriptorSlot.description observed.sameSlot)
  have admitsMarked := ops.runWithAdmission_eq (observed.sameSlot.symm ▸ admission)
  have present : ops.MarkerPresent := by
    cases marker with
    | absent visible _ => rw [zero.zeroMarker] at visible; cases visible
    | @present metadata _ returned =>
      exact ⟨metadata, observed.sameMarkerLookup.trans (by rw [returned])⟩
  have actualMarked := (ops.run_selectsMarked present).symm.trans (admitsMarked.symm.trans ran)
  have absent : checkpoint = none := by
    have binding : zero.files.directory.active.manifest = none := zero.noManifest
    change SelectedIntegrityCheckpoint zero.checkpoint.durable zero.files.directory.active.manifest checkpoint at selected
    rw [binding] at selected
    cases selected
    rfl
  have replayEmpty : recoverSelected .empty (WAL.encode []) = .ok .empty :=
    recoverSelected_encoded .empty [] [] trivial rfl
  rw [absent, show (none : Option (PackedTable × UInt64)).getD (.empty, 0) = (.empty, 0) from rfl,
    replayEmpty] at replay
  have empty : opened.table = .empty := (Except.ok.inj replay).symm
  have payload : session.phase = .ready ⟨.empty, 0, 0, 0⟩ := by
    rw [phase]
    simp [Reopened.installed, empty, generation, absent, bytes, keeper, BootstrapMarkedZero.layout]
  let after : LockedFileState WalSegmentRotation.State := ⟨restore (before := before) final.image, final.owners⟩
  have bootReady : BootstrapReady after.image := by
    refine ⟨zero.keeperDurable, ?_, ?_, ?_⟩
    · change final.image.directory.active.manifest = none
      rw [ready.selected]
      exact zero.noManifest
    · change final.image.directory.active.walBoundary = some (WAL.Boundary.encode 0)
      rw [ready.selected]
      exact zero.zeroMarker
    · change final.image.directory.crashImages = [final.image.directory.active]
      rw [ready.settled, ready.selected]
  have selection := captured.retrySelects admission valid marker bootstrap
  obtain ⟨_, _, branch⟩ := selection.2.2.resolve_left (fun missing => by
    rw [zero.zeroMarker] at missing
    cases missing.1)
  refine ⟨session, after, ?_, path, description.trans fromSlot, payload, (description.trans fromSlot) ▸ held, bootReady⟩
  rw [branch, runOpenWithInstallation_outcome, runOpenWithImage_acquired, observed.projected]
  rw [runOpenWithInstallation_outcome, runOpenWithImage_acquired] at actualMarked
  cases actual : ops.markedAt directory ops.cache (locked zero).image with
  | ok opened files =>
    rw [actual] at actualMarked
    obtain ⟨sameSession, sameFinal⟩ := EStateM.Result.ok.inj actualMarked
    have worker : observed.reads.operations.markedAt directory captured.cache zero.files = .ok opened files := by
      rw [← observed.sameCache]
      exact actual
    rw [worker, ← sameSession]
    dsimp only [after]
    rw [← sameFinal]
    have slotEq : ops.slot = retry.slot := observed.sameSlot
    have refEq : ops.nextRef = retry.nextRef := observed.sameNextRef
    simp [slotEq, refEq, projectMarked]
  | error error files =>
    rw [actual] at actualMarked
    cases report : ops.unlock <;> simp [report] at actualMarked

end BootstrapMarkedRetryOpen

/-- If a failed bootstrap publication has left the zero marker visible,
the next admitted attempt uses that exact reached state. The marked
worker validates its empty keeper and installs the exact empty session. -/
theorem BootstrapCheckedListing.installsMarkedZeroAfterPublicationError
    {input nextInput : FilePath} {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
    {calls : BootstrapOpenCalls (Cache Handle) directory before}
    {captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls}
    (listed : BootstrapCheckedListing captured) (admission : OpenAdmissionReports input directory calls.slot)
    (valid : BootstrapValid before.image) (localUnlock : calls.unlock.LocalFlock)
    (effects : BootstrapPublicationEffects calls captured.cache) {error : IO.Error}
    {after : LockedFileState WalSegmentRotation.State} (failed : calls.run admission = .error error after)
    {retry : BootstrapAdmissionCalls (Cache Handle) directory after}
    (nextCache : BootstrapCacheOpen retry) (nextAdmission : OpenAdmissionReports nextInput directory retry.slot)
    {metadata : IO.FS.Metadata} (marker : retry.lookup (directory.file .walBoundary) = .ok metadata)
    (visible : after.image.metadata.active.walBoundary ≠ none)
    (reports : ∀ zero : BootstrapMarkedZero after.image, Nonempty (BootstrapMarkedRetryOpen nextCache zero))
    (bootstrap : DiskDirectory → Cache Handle → EStateM IO.Error WalSegmentRotation.State Reopened) :
    BootstrapMarkedRetryOpen.Installed directory retry.slot.description (retry.run bootstrap nextAdmission) := by
  have reached := listed.validAfterPublicationError admission valid localUnlock effects failed
  obtain ⟨observed⟩ := reports (reached.markedZero visible)
  exact observed.installs nextAdmission reached (.present visible marker) bootstrap

/-- An admitted power-loss survivor with a visible marker carries the
durable empty keeper into the exact marked worker of the next open. -/
theorem BootstrapCheckedListing.installsMarkedZeroAfterPublicationCrash
    {input nextInput : FilePath} {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
    {calls : BootstrapOpenCalls (Cache Handle) directory before}
    {captured : BootstrapCacheOpen calls.toBootstrapAdmissionCalls}
    (listed : BootstrapCheckedListing captured) (admission : OpenAdmissionReports input directory calls.slot)
    (valid : BootstrapValid before.image) (localUnlock : calls.unlock.LocalFlock)
    (effects : BootstrapPublicationEffects calls captured.cache) {error : IO.Error}
    {after : LockedFileState WalSegmentRotation.State} (failed : calls.run admission = .error error after)
    {pair : DirectoryPublication.Bindings} (selected : pair ∈ after.image.metadata.crashImages)
    {keeperSurvives : Bool} (keeper : after.image.successor.MaySurvive keeperSurvives)
    {retry : BootstrapAdmissionCalls (Cache Handle) directory (bootstrapPowerLoss directory after pair keeperSurvives)}
    (nextCache : BootstrapCacheOpen retry) (nextAdmission : OpenAdmissionReports nextInput directory retry.slot)
    {metadata : IO.FS.Metadata} (marker : retry.lookup (directory.file .walBoundary) = .ok metadata)
    (visible : pair.walBoundary ≠ none)
    (reports : ∀ zero : BootstrapMarkedZero (bootstrapPowerLoss directory after pair keeperSurvives).image,
      Nonempty (BootstrapMarkedRetryOpen nextCache zero))
    (bootstrap : DiskDirectory → Cache Handle → EStateM IO.Error WalSegmentRotation.State Reopened) :
    BootstrapMarkedRetryOpen.Installed directory retry.slot.description (retry.run bootstrap nextAdmission) := by
  have reached := listed.validAfterPublicationCrash admission valid localUnlock effects failed selected keeper
  obtain ⟨observed⟩ := reports (reached.markedZero visible)
  exact observed.installs nextAdmission reached (.present visible marker) bootstrap

end Alvoki.Storage.DiskSession
