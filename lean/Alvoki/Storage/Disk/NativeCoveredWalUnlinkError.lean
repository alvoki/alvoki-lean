import Alvoki.Storage.Disk.NativeReadyWalCollectionError
import Alvoki.Storage.Disk.NativeReadRecoveryTrace

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

private abbrev UnlinkFiles := DescriptorInventory × WalSealedUnlinkImage

/-- The actual canonical schedule returns a classified unlink error
after some completed callbacks. The reported prefix can include a last
unlink whose effect occurred before it reported the error. -/
structure NativeCoveredWalUnlinkError (state : NativeReadyState) where
  calls : WalCollectionReads
  inventory : WalCollectionInventoryReport calls state.session.directory state.session.descriptor state.writer.wal
  startsAt : inventory.descriptors = state.census
  sameOwner : inventory.owner = state.owner
  sameDirectory : inventory.lifetime.directorySlot = state.directorySlot
  manifest : calls.paths.readOptional (state.session.directory.file .manifest) = .ok state.writer.target.pair.manifest
  marker : calls.paths.readOptional (state.session.directory.file .walBoundary) = .ok state.writer.target.pair.walBoundary
  remove : FilePath → EStateM IO.Error WalSealedUnlinkImage (Except IO.Error Unit)
  cause : IO.Error
  pending : List Nat
  afterView : DirectoryReadNamespace
  after : WalSealedUnlinkImage
  removed : List Nat
  unlinked : WalUnlinkPrefix state.session.directory inventory.lifetime.root remove state.writer.wal.collectionOffsets
    inventory.lifetime.namespaceView (.start state.writer.wal) pending (some cause) afterView after removed
  objects : afterView.modelObject = inventory.lifetime.namespaceView.modelObject
  drops : List LockReferenceDrop
  keepsSlots : ∀ slot ∈ state.census.slots,
    ∀ drop ∈ inventory.lifetime.drops ++ drops, drop.removes slot.reference = false
  rawRemove : FilePath → EStateM IO.Error UnlinkFiles (Except IO.Error Unit)
  rawReturned : ∀ path issue result reached, remove path issue = .ok result reached →
    rawRemove path (inventory.listing.afterClose, issue) =
      .ok result (inventory.listing.afterClose.afterDrops drops, reached)

namespace WalUnlinkPrefix

private theorem failedCall {directory : DiskDirectory} {root : DeviceInode} {removeFile}
    {offsets pending removed : List Nat} {view afterView : DirectoryReadNamespace} {before after : WalSealedUnlinkImage}
    {failure : Option IO.Error} {cause : IO.Error}
    (reported : WalUnlinkPrefix directory root removeFile offsets view before pending failure afterView after removed)
    (same : failure = some cause) :
    ∃ done first issue result,
      offsets = done ++ first :: pending ∧
      removeFile (directory.file (.walSegment first)) issue = .ok result after ∧
      RunCollection.ownedUnlinkResult result = .error cause := by
  induction reported with
  | pause => contradiction
  | @next first before result middle view middleView rest pending afterView after removed call effect accepted tail ih =>
    obtain ⟨done, target, issue, result, order, reached, returned⟩ := ih same
    exact ⟨first :: done, target, issue, result, congrArg (first :: ·) order, reached, returned⟩
  | failed call effect returned =>
    exact ⟨[], _, _, _, rfl, call, returned.trans (congrArg Except.error (Option.some.inj same))⟩
  | failedWithoutEffect call returned =>
    exact ⟨[], _, _, _, rfl, call, returned.trans (congrArg Except.error (Option.some.inj same))⟩

end WalUnlinkPrefix

namespace NativeCoveredWalUnlinkError

variable {state : NativeReadyState}

abbrev Files := CensusDirectoryCache × WalSealedUnlinkImage

def census (error : NativeCoveredWalUnlinkError state) : DescriptorInventory :=
  error.inventory.listing.afterClose.afterDrops error.drops

def closeState (error : NativeCoveredWalUnlinkError state) :
    CachedCloseState CheckpointOpenHandle WalSealedUnlinkImage :=
  ⟨.poisoned, ⟨(state.cache, error.after), state.files.owners⟩, error.census⟩

def session (error : NativeCoveredWalUnlinkError state) : SegmentedSession :=
  { state.session with phase := error.closeState.phase }

def run (error : NativeCoveredWalUnlinkError state) (barrier : FilePath → EStateM IO.Error Files Unit) :
    EStateM.Result IO.Error (Phase Installed × LockedFileState Files) Unit :=
  error.calls.collectWithCache state.session.directory error.remove barrier
    (state.session.phase, ⟨(state.cache, .start state.writer.wal), state.files.owners⟩)

/-- The non-ENOENT diagnostic comes from the actual last unlink. The
native suffix reaches neither the final fsync nor the ready assignment. -/
theorem returns (error : NativeCoveredWalUnlinkError state) (valid : state.Valid)
    (barrier : FilePath → EStateM IO.Error Files Unit) :
    error.run barrier = .error error.cause (error.closeState.phase, error.closeState.files) := by
  have planned := valid.retained.completeObservedWalPlan error.calls error.inventory error.manifest error.marker
  rw [run, WalCollectionReads.collectWithCache, valid.phase, WalCollectionReads.collectWithEffects_plan _ _ _ _ _ _ planned,
    error.unlinked.dispatchWithCache _ _ _ _]
  rfl

theorem failedCoveredCall (error : NativeCoveredWalUnlinkError state) :
    ∃ done first issue result,
      state.writer.wal.collectionOffsets = done ++ first :: error.pending ∧
      error.rawRemove (state.session.directory.file (.walSegment first)) (error.inventory.listing.afterClose, issue) =
        .ok result (error.census, error.after) ∧
      RunCollection.ownedUnlinkResult result = .error error.cause := by
  obtain ⟨done, first, issue, result, order, called, classified⟩ := error.unlinked.failedCall rfl
  exact ⟨done, first, issue, result, order, error.rawReturned _ _ _ _ called, classified⟩

theorem sameCensus (error : NativeCoveredWalUnlinkError state) : error.census = state.census :=
  (error.inventory.preservesCensus error.drops (fun slot live drop occurred =>
    error.keepsSlots slot (error.startsAt ▸ live) drop occurred)).trans error.startsAt

/-- Reaching the error changes availability on the original session.
Its old handles cannot serve new reads while the writer is poisoned. -/
theorem rejectsReads (error : NativeCoveredWalUnlinkError state) (sequence : UInt64) (sameSession : Bool)
    (read : PackedTable → Option α) :
    error.session.sessionRef = state.session.sessionRef ∧ error.session.phaseRef = state.session.phaseRef ∧
    error.session.runAcquireAt sequence = .error (IO.userError "publication failed; reopen the database") error.session ∧
    error.session.runSnapshotRead sameSession read =
      .error (IO.userError "publication failed; reopen the database") error.session :=
  ⟨rfl, rfl, rfl, SegmentedSession.runSnapshotRead_poisoned rfl sameSession read⟩

theorem retainsCustody (error : NativeCoveredWalUnlinkError state) (valid : state.Valid) :
    state.owner ∈ error.census.slots ∧ state.directorySlot ∈ error.census.slots ∧
    error.afterView.child error.inventory.lifetime.root "LOCK" = some error.inventory.lifetime.lock ∧
    error.afterView.modelObject error.inventory.lifetime.lock = error.census.inode state.owner.description ∧
    error.afterView.modelObject error.inventory.lifetime.root = error.census.inode state.directorySlot.description := by
  refine ⟨error.sameCensus.symm ▸ valid.ownerLive, error.sameCensus.symm ▸ valid.directoryLive,
    (error.unlinked.keepsOtherChild (fun offset _ => lock_ne_renderWalSegmentName offset)).trans
      error.inventory.lifetime.lockEntry, ?_, ?_⟩
  · rw [error.sameCensus, error.objects, ← error.sameOwner, ← error.startsAt]
    exact error.inventory.lifetime.identifiesLock
  · rw [error.sameCensus, error.objects, ← error.sameDirectory, ← error.startsAt]
    exact error.inventory.lifetime.identifiesDirectory

/-- The same selected marked read plan is available in the visible
namespace and every reported surviving seal list. -/
theorem selects (error : NativeCoveredWalUnlinkError state) (valid : state.Valid) :
    Nonempty (CoveredWalRetrySelection state.writer error.after.visible) ∧
    ∀ sealed ∈ error.after.crashSealed,
      Nonempty (CoveredWalRetrySelection state.writer { error.after.visible with sealed }) := by
  let ready := valid.retained
  have planned := ready.completeObservedWalPlan error.calls error.inventory error.manifest error.marker
  have bound (segment : WalSegment) (sealed : segment ∈ state.writer.wal.sealed) :
      (error.inventory.lifetime.namespaceView.child error.inventory.lifetime.root (renderWalSegmentName segment.first)).isSome = true := by
    rw [error.inventory.bound segment (List.mem_append_left _ sealed)]
    rfl
  obtain ⟨⟨projected, invariant⟩, survives, _, _, _⟩ := ready.reportedWalUnlinkPrefix error.calls planned
    (fun _ member => member) bound error.remove (fun _ => pure ()) error.unlinked
  exact ⟨ready.preparesCoveredWalRetry (invariant.visible.symm ▸ (invariant.trace.projects ready.layout).1),
    fun sealed member => ready.preparesCoveredWalRetry (survives sealed member)⟩

end NativeCoveredWalUnlinkError

/-- Stop the common native read prefix at the returned unlink diagnostic.
The exact poisoned files and earlier client replay support later recovery. -/
structure NativeReturnedCoveredWalUnlinkError (current : NativeReadPosition history log)
    (error : NativeCoveredWalUnlinkError current.state) : Prop where
  returned : ∀ barrier, error.run barrier = .error error.cause (error.closeState.phase, error.closeState.files)
  held : error.closeState.files.owners.Owns current.state.session.directory current.state.session.descriptor
  exactCensus : error.closeState.descriptors = current.state.census
  names : ∀ offset, error.afterView.child error.inventory.lifetime.root (renderWalSegmentName offset) =
    if error.removed.contains offset then none else
      error.inventory.lifetime.namespaceView.child error.inventory.lifetime.root (renderWalSegmentName offset)
  visible : Nonempty (CoveredWalRetrySelection current.state.writer error.after.visible)
  survivors : ∀ sealed ∈ error.after.crashSealed,
    Nonempty (CoveredWalRetrySelection current.state.writer { error.after.visible with sealed })
  sameHistory : current.state.writer.history = history
  replay : PendingClientReplay log current.reads history
  bounds : ∀ read ∈ current.reads, read.BoundedBy history.length

theorem NativeReadPosition.returnsCoveredWalUnlinkError (current : NativeReadPosition history log)
    (error : NativeCoveredWalUnlinkError current.state) : NativeReturnedCoveredWalUnlinkError current error := by
  obtain ⟨valid, sameHistory, replay⟩ := current.readPrefix.refines
  obtain ⟨visible, survivors⟩ := error.selects valid
  exact ⟨error.returns valid, valid.retained.held, error.sameCensus, error.unlinked.lookupAfter,
    visible, survivors, sameHistory, replay, current.readPrefix.readsBounded⟩

end Alvoki.Storage.DiskSession
