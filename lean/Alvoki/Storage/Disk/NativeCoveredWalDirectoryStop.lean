import Alvoki.Storage.Disk.NativeCoveredWalUnlinkStop
import Alvoki.Storage.Disk.Proofs.Collection.NativeReadyWalCollectionError
import Alvoki.Storage.Disk.Proofs.Read.NativeReadRecoveryTrace

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair
open WalCollectionInterruption (UnlinkFiles CollectionState CollectionM)

/-- All checked unlinks have returned. The next raw fsync uses the
original cached directory slot and stops without a callback result. -/
structure NativeCoveredWalDirectoryStop (state : NativeReadyState) where
  calls : WalCollectionReads
  inventory : WalCollectionInventoryReport calls state.session.directory state.session.descriptor state.writer.wal
  startsAt : inventory.descriptors = state.census
  sameOwner : inventory.owner = state.owner
  sameDirectory : inventory.lifetime.directorySlot = state.directorySlot
  manifest : calls.paths.readOptional (state.session.directory.file .manifest) = .ok state.writer.target.pair.manifest
  marker : calls.paths.readOptional (state.session.directory.file .walBoundary) = .ok state.writer.target.pair.walBoundary
  remove : FilePath → EStateM IO.Error WalSealedUnlinkImage (Except IO.Error Unit)
  rawRemove : FilePath → EStateM FilePath UnlinkFiles (Except IO.Error Unit)
  returned : ∀ path before result after, remove path before = .ok result after →
    rawRemove path (inventory.listing.afterClose, before) = .ok result (inventory.listing.afterClose, after)
  view : DirectoryReadNamespace
  beforeSync : WalSealedUnlinkImage
  detached : List Nat
  unlinked : WalUnlinkPrefix state.session.directory inventory.lifetime.root remove state.writer.wal.collectionOffsets
    inventory.lifetime.namespaceView (.start state.writer.wal) [] none view beforeSync detached
  objects : view.modelObject = inventory.lifetime.namespaceView.modelObject
  capture : DescriptorInventory
  cached : state.cache.directory = some (capture, state.directorySlot, 0)
  captureInode : capture.inode state.directorySlot.description = inventory.descriptors.inode state.directorySlot.description
  pathObject : FilePath → Option DeviceInode
  directoryPath : pathObject state.session.directory.path = some inventory.lifetime.root
  drops : List LockReferenceDrop
  keepsSlots : ∀ slot ∈ state.census.slots,
    ∀ drop ∈ inventory.lifetime.drops ++ drops, drop.removes slot.reference = false
  openRead : FilePath → EStateM IO.Error UnlinkFiles WalCollectionDirectoryHandle
  fsync : WalCollectionDirectoryHandle → EStateM FilePath UnlinkFiles (Except IO.Error Unit)
  applied : Bool
  stopped : fsync (capture, state.directorySlot, 0) (inventory.listing.afterClose, beforeSync) =
    .error state.session.directory.path (inventory.listing.afterClose.afterDrops drops,
      if applied then beforeSync.syncDirectory else beforeSync)

namespace NativeCoveredWalDirectoryStop

variable {state : NativeReadyState}

def census (stop : NativeCoveredWalDirectoryStop state) : DescriptorInventory :=
  stop.inventory.listing.afterClose.afterDrops stop.drops

def after (stop : NativeCoveredWalDirectoryStop state) : WalSealedUnlinkImage :=
  if stop.applied then stop.beforeSync.syncDirectory else stop.beforeSync

private def syncPath (stop : NativeCoveredWalDirectoryStop state) (path : FilePath) : CollectionM Unit :=
  ExceptT.mk fun (phase, files) =>
    match files.image.1.resolve state.session.directory.path path stop.openRead files.image.2 with
    | .error cause (cache, reached) => .ok (.error cause) (phase, ⟨(cache, reached), files.owners⟩)
    | .ok handle (cache, reached) =>
      match stop.fsync handle reached with
      | .ok result after => .ok result (phase, ⟨(cache, after), files.owners⟩)
      | .error atPath after => .error atPath (phase, ⟨(cache, after), files.owners⟩)

private def group (stop : NativeCoveredWalDirectoryStop state) (path : FilePath) : CollectionM Unit :=
  SyncPathGroup.run stop.syncPath #[path]

def run (stop : NativeCoveredWalDirectoryStop state) : EStateM.Result FilePath CollectionState (Except IO.Error Unit) :=
  WalCollectionInterruption.run state stop.calls stop.inventory.listing.afterClose
    (WalCollectionInterruption.perform state.session.directory stop.rawRemove stop.group)

theorem stops (stop : NativeCoveredWalDirectoryStop state) (valid : state.Valid) :
    stop.run = .error state.session.directory.path
      (.poisoned, ⟨(state.cache, stop.census, stop.after), state.files.owners⟩) := by
  let inventory := stop.inventory.listing.afterClose
  let action := WalCollectionInterruption.perform state.session.directory stop.rawRemove stop.group
  have planned := valid.retained.completeObservedWalPlan stop.calls stop.inventory stop.manifest stop.marker
  have groupStopped : (stop.group state.session.directory.path).run (WalCollectionInterruption.atFiles state inventory stop.beforeSync) =
      .error state.session.directory.path (.poisoned, ⟨(state.cache, stop.census, stop.after), state.files.owners⟩) := by
    simp [group, SyncPathGroup.run, ← Array.forIn_toList, List.forIn_cons, MonadExcept.tryCatch, MonadExceptOf.tryCatch,
      tryCatchThe, ExceptT.tryCatch, syncPath, WalCollectionInterruption.atFiles, inventory, Cache.resolve, stop.cached,
      Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk, EStateM.bind, stop.stopped, census, after]
  change stop.group state.session.directory.path (WalCollectionInterruption.atFiles state inventory stop.beforeSync) = _ at groupStopped
  have stopped : (RunCollection.run [] action).run (WalCollectionInterruption.atFiles state inventory stop.beforeSync) =
      .error state.session.directory.path (.poisoned, ⟨(state.cache, stop.census, stop.after), state.files.owners⟩) := by
    simp [RunCollection.run, RunCollection.steps, action, WalCollectionInterruption.perform, RunCollection.performPaths,
      List.forM_eq_forM, List.forM_cons, Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk, EStateM.bind, groupStopped]
  exact WalCollectionInterruption.stopsFromReady state stop.calls inventory action valid planned
    ((WalCollectionInterruption.runsCompleted state inventory stop.rawRemove stop.group stop.returned stop.unlinked rfl).trans stopped)

theorem sameCensus (stop : NativeCoveredWalDirectoryStop state) : stop.census = state.census :=
  (stop.inventory.preservesCensus stop.drops (fun slot live drop occurred =>
    stop.keepsSlots slot (stop.startsAt ▸ live) drop occurred)).trans stop.startsAt

structure Custody (stop : NativeCoveredWalDirectoryStop state) : Prop where
  path : stop.pathObject state.session.directory.path = some stop.inventory.lifetime.root
  captured : stop.capture.inode state.directorySlot.description = stop.census.inode state.directorySlot.description
  directory : stop.view.modelObject stop.inventory.lifetime.root = stop.census.inode state.directorySlot.description
  ownerLive : state.owner ∈ stop.census.slots
  directoryLive : state.directorySlot ∈ stop.census.slots
  lock : stop.view.child stop.inventory.lifetime.root "LOCK" = some stop.inventory.lifetime.lock
  lockObject : stop.view.modelObject stop.inventory.lifetime.lock = stop.census.inode state.owner.description

theorem retainsCustody (stop : NativeCoveredWalDirectoryStop state) (valid : state.Valid) : stop.Custody := by
  refine ⟨stop.directoryPath, ?_, ?_, stop.sameCensus.symm ▸ valid.ownerLive, stop.sameCensus.symm ▸ valid.directoryLive,
    (stop.unlinked.keepsOtherChild (fun offset _ => lock_ne_renderWalSegmentName offset)).trans stop.inventory.lifetime.lockEntry, ?_⟩
  · rw [stop.captureInode, stop.startsAt, stop.sameCensus]
  · rw [stop.objects, stop.sameCensus, ← stop.sameDirectory, ← stop.startsAt]
    exact stop.inventory.lifetime.identifiesDirectory
  · rw [stop.objects, stop.sameCensus, ← stop.sameOwner, ← stop.startsAt]
    exact stop.inventory.lifetime.identifiesLock

private theorem beforeEffect (stop : NativeCoveredWalDirectoryStop state) (valid : state.Valid) :
    ∃ projected, WalUnlinkInvariant state.writer.wal stop.inventory.lifetime.root stop.view stop.beforeSync projected := by
  have bound (segment : WalSegment) (sealed : segment ∈ state.writer.wal.sealed) :
      (stop.inventory.lifetime.namespaceView.child stop.inventory.lifetime.root (renderWalSegmentName segment.first)).isSome = true := by
    rw [stop.inventory.bound segment (List.mem_append_left _ sealed)]
    rfl
  exact (stop.unlinked.projects valid.retained.layout (WalUnlinkInvariant.start bound) (fun _ member => member)).1

/-- Before an effect, the unbarriered seal alternatives remain possible.
A completed effect settles their exact visible list without acknowledging
or changing the installed writer. -/
theorem settled (stop : NativeCoveredWalDirectoryStop state) (valid : state.Valid) :
    (stop.applied = false → stop.after = stop.beforeSync) ∧
    (stop.applied = true → stop.after.crashSealed = [stop.beforeSync.visible.sealed] ∧
      ∀ offset ∈ state.writer.wal.collectionOffsets, ∀ sealed ∈ stop.after.crashSealed, ∀ segment ∈ sealed, segment.first ≠ offset) := by
  refine ⟨fun no => by simp [after, no], ?_⟩
  intro applied
  have choices : stop.after.crashSealed = [stop.beforeSync.visible.sealed] := by simp [after, applied]; rfl
  refine ⟨choices, ?_⟩
  intro offset selected sealed member segment stored same
  obtain ⟨_, prior⟩ := stop.beforeEffect valid
  rw [choices] at member
  have found := prior.bound valid.retained.layout segment (List.mem_singleton.mp member ▸ stored)
  rw [same, stop.unlinked.completedNamesAbsent rfl rfl offset selected] at found
  contradiction

theorem selections (stop : NativeCoveredWalDirectoryStop state) (valid : state.Valid) :
    Nonempty (CoveredWalRetrySelection state.writer stop.after.visible) ∧
    ∀ sealed ∈ stop.after.crashSealed,
      Nonempty (CoveredWalRetrySelection state.writer { stop.after.visible with sealed }) := by
  obtain ⟨_, prior⟩ := stop.beforeEffect valid
  have reached := prior.afterDirectoryEffect stop.applied
  have retry := reached.trace.projects valid.retained.layout
  refine ⟨valid.retained.preparesCoveredWalRetry (reached.visible.symm ▸ retry.1), ?_⟩
  intro sealed member
  apply valid.retained.preparesCoveredWalRetry
  rw [after, reached.visible]
  exact retry.2 sealed (reached.survivors sealed member)

end NativeCoveredWalDirectoryStop

/-- The interrupted final covered-WAL barrier keeps the original held
writer, marked selection and read ledger at the reached callback. -/
structure NativeCoveredWalDirectoryStopped (current : NativeReadPosition history log)
    (stop : NativeCoveredWalDirectoryStop current.state) : Prop where
  stopped : stop.run = .error current.state.session.directory.path
    (.poisoned, ⟨(current.state.cache, stop.census, stop.after), current.state.files.owners⟩)
  held : current.state.files.owners.Owns current.state.session.directory current.state.session.descriptor
  census : stop.census = current.state.census
  custody : stop.Custody
  absent : ∀ offset ∈ current.state.writer.wal.collectionOffsets,
    stop.view.child stop.inventory.lifetime.root (renderWalSegmentName offset) = none
  beforeEffect : stop.applied = false → stop.after = stop.beforeSync
  afterEffect : stop.applied = true → stop.after.crashSealed = [stop.beforeSync.visible.sealed] ∧
    ∀ offset ∈ current.state.writer.wal.collectionOffsets, ∀ sealed ∈ stop.after.crashSealed,
      ∀ segment ∈ sealed, segment.first ≠ offset
  visible : Nonempty (CoveredWalRetrySelection current.state.writer stop.after.visible)
  survivors : ∀ sealed ∈ stop.after.crashSealed,
    Nonempty (CoveredWalRetrySelection current.state.writer { stop.after.visible with sealed })
  replay : PendingClientReplay log current.reads history
  bounds : ∀ read ∈ current.reads, read.BoundedBy history.length

theorem NativeReadPosition.stopsAtCoveredWalDirectory (current : NativeReadPosition history log)
    (stop : NativeCoveredWalDirectoryStop current.state) : NativeCoveredWalDirectoryStopped current stop := by
  obtain ⟨valid, _, replay⟩ := current.readPrefix.refines
  obtain ⟨visible, survivors⟩ := stop.selections valid
  obtain ⟨beforeEffect, afterEffect⟩ := stop.settled valid
  exact ⟨stop.stops valid, valid.retained.held, stop.sameCensus, stop.retainsCustody valid, stop.unlinked.completedNamesAbsent rfl rfl,
    beforeEffect, afterEffect, visible, survivors, replay, current.readPrefix.readsBounded⟩

end Alvoki.Storage.DiskSession
