import Alvoki.Storage.Disk.Proofs.Native.Checkpoint.NativeMarkedCheckpointHeap
import Alvoki.Storage.Disk.Proofs.Native.Open.NativeOpenReadyStorage

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair SyncHandleRouting

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write} {layout : CanonicalKeeperLayout retry.image history}
  {published : CheckpointPublication.Image} {checkpoint : Option (PackedTable × UInt64)}
  {admission : CensusOpenAdmissionReports input directory inventory retry}
  {vacant : TryLockObserves retry.owners directory (.ok true)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}
  {calls : CapturedAlignedCallbacks admission} {reads : CapturedMarkedReadReports admission layout published}
  {finish : CapturedAlignedFinish calls reads vacant selected} {heap : Type}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap} {cacheEntry entry : heap}
  {seed : OpenSyncCacheAllocations admission.opened view init cacheEntry} {callbacks : AlignedKeeperCacheCallbacks heap}

/-- Frame the actual keeper open, bounded reads, and pending insertion.
The bounded read uses the same chunk frame theorem as temporary reads. -/
theorem AlignedKeeperCacheReport.framesRemembered
    (seen : AlignedKeeperCacheReport finish view init cacheEntry seed callbacks entry) {frame : heap → heap → Prop}
    (refl : ∀ atHeap, frame atHeap atHeap)
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    (openFrame : callbacks.openRead (directory.file (.walSegment layout.keeper.first)) entry =
      .ok seen.keeper seen.opened → frame entry seen.opened)
    (chunkFrame : ∀ count atHeap, frame atHeap (reachedState (callbacks.readChunk seen.keeper count atHeap)))
    (rememberFrame : callbacks.modifyPending seed.pendingRef
      (pushPending (directory.file (.walSegment layout.keeper.first)) seen.keeper) seen.read =
      .ok () seen.remembered → frame seen.read seen.remembered) :
    frame entry seen.remembered := by
  have read := exactReadFrames refl trans (IO.userError "short or oversized WAL keeper read")
    (callbacks.readChunk seen.keeper) chunkFrame layout.keeper.bytes.size ByteArray.empty seen.opened
  rw [seen.rawRead] at read
  exact trans (openFrame seen.rawOpen) (trans read (rememberFrame seen.rawRemember))

/-- The descriptor issued to the final sync still identifies the inode
opened for the exact selected keeper. -/
theorem AlignedKeeperCacheReport.keeperIssueInode
    (seen : AlignedKeeperCacheReport finish view init cacheEntry seed callbacks entry) :
    (view.descriptors seen.consumed).inode (view.handle seen.consumed seen.keeper).2.1.description =
      reads.wal.keeper.observesFile.object := by
  rw [seen.sameKeeper, seen.rawKeeper, seen.consumeFrame.2, seen.authorizedCensus]
  exact reads.wal.keeper.observesFile.sameObject

/-- The full payload observed under the canonical name survives the
read, directory barrier and pending removal. The checked extent leaves
exactly the committed bytes at the actual keeper sync issue heap. -/
theorem AlignedKeeperCacheReport.keeperAtIssue
    (seen : AlignedKeeperCacheReport finish view init cacheEntry seed callbacks entry)
    (names : heap → FilePath → Option Nat) (visible : heap → Nat → ByteArray) :
    let path := directory.file (.walSegment layout.keeper.first)
    let live (atHeap : heap) : CheckpointSurvivingFiles := ⟨names atHeap, fun inode => [visible atHeap inode]⟩
    let object := reads.wal.keeper.observesFile.object
    names entry path = some object →
    visible entry object = layout.keeper.bytes ++ layout.tail →
    (live entry).Frames (· = path) (live seen.remembered) →
    (callbacks.sync seed.handle seen.remembered = .ok () seen.authorized →
      (live seen.remembered).Frames (· = path) (live seen.authorized)) →
    (callbacks.setPending seed.pendingRef [] seen.authorized = .ok () seen.consumed →
      (live seen.authorized).Frames (· = path) (live seen.consumed)) →
    let inode := (view.descriptors seen.consumed).inode (view.handle seen.consumed seen.keeper).2.1.description
    names seen.consumed path = some inode ∧ visible seen.consumed inode = layout.keeper.bytes := by
  intro path live object bound payload read directoryFrame consumeFrame inode
  have frames := read.trans ((directoryFrame seen.directorySync).trans (consumeFrame seen.consume))
  obtain ⟨sameName, sameBytes⟩ := frames path rfl
  have kept : [visible seen.consumed object] = [visible entry object] := sameBytes object bound
  have issued : inode = object := seen.keeperIssueInode
  rw [issued]
  exact ⟨sameName.trans bound, (List.cons.inj kept).1.trans (payload.trans finish.keeperPayload)⟩

/-- Physical laws for the three actual callbacks of an aligned repair.
Each law is local to its issue and return heaps. -/
structure AlignedKeeperCacheReport.StorageEffects
    (seen : AlignedKeeperCacheReport finish view init cacheEntry seed callbacks entry)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (state : NativeReadyState) : Prop where
  directorySync : callbacks.sync seed.handle seen.remembered = .ok () seen.authorized →
    (view.handle seen.remembered seed.handle).2.1 ∈ (view.descriptors seen.remembered).slots →
    (observe seen.remembered).files.names directory.path = some
      ((view.descriptors seen.remembered).inode (view.handle seen.remembered seed.handle).2.1.description) →
    (observe seen.remembered).files.Frames (fun path => ∃ file, path = directory.file file)
      (observe seen.authorized).files ∧
    (observe seen.remembered).Frames (· = state.session.directory.path) (observe seen.authorized) ∧
    ∀ names ∈ (observe seen.authorized).crashNames, ∀ file, names (state.session.directory.file file) =
      (observe seen.authorized).files.names (state.session.directory.file file)
  consume : callbacks.setPending seed.pendingRef [] seen.authorized = .ok () seen.consumed →
    (observe seen.authorized).Frames state.crashPath (observe seen.consumed)
  keeperSync : callbacks.sync seen.keeper seen.consumed = .ok () seen.reached →
    (view.handle seen.consumed seen.keeper).2.1 ∈ (view.descriptors seen.consumed).slots →
    let inode := (view.descriptors seen.consumed).inode (view.handle seen.consumed seen.keeper).2.1.description
    RegularFileSyncEffect inode [visible seen.consumed inode] (observe seen.consumed) (observe seen.reached) ∧
    visible seen.reached inode = visible seen.consumed inode

theorem CapturedAlignedFinish.sameCensusObjects (finish : CapturedAlignedFinish calls reads vacant selected) :
    finish.census.inode = admission.reached.inode := by
  unfold CapturedAlignedFinish.census
  rw [finish.sameKeeper]
  change reads.wal.keeper.calls.inventory.inode = _
  rw [finish.readCustody.opened]
  rfl

/-- With no later WAL to remove, the actual directory barrier settles the
selected child names. Consuming the remembered keeper reference frames
those names. Its subsequent fsync establishes the committed bytes at
the actual finisher heap, with the census that the marked installer uses. -/
theorem AlignedKeeperCacheReport.readyStorage
    (seen : AlignedKeeperCacheReport finish view init cacheEntry seed callbacks entry)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    {state : NativeReadyState}
    (sameDirectory : state.session.directory = directory) (sameCensus : state.census = finish.census)
    (sameSlot : state.directorySlot = admission.cached)
    (sameFirst : state.writer.wal.active.first = layout.keeper.first)
    (sameBytes : state.writer.wal.active.bytes = layout.keeper.bytes)
    (protectedFiles : NativeReadyProtectedStorage state (observe seen.remembered).files)
    (marker : (observe seen.remembered).files.Stored (state.session.directory.file .walBoundary)
      (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64))
    (rootSettled : ∀ names ∈ (observe seen.remembered).crashNames,
      names state.session.directory.path = (observe seen.remembered).files.names state.session.directory.path)
    (effects : seen.StorageEffects observe visible state)
    (keeperAtIssue :
      let inode := reads.wal.keeper.calls.inventory.inode reads.wal.keeper.calls.slot.description
      (observe seen.consumed).files.names (directory.file (.walSegment layout.keeper.first)) = some inode ∧
      visible seen.consumed inode = layout.keeper.bytes)
    (apart : ∀ path, path = state.session.directory.file .walBoundary ∨ state.writeFramePath path →
      (observe seen.remembered).files.names path ≠
        some (reads.wal.keeper.calls.inventory.inode reads.wal.keeper.calls.slot.description)) :
    view.descriptors seen.reached = state.census ∧ NativeReadyStorage state (observe seen.reached) ∧
    ∀ inode, (observe seen.reached).files.names (state.session.directory.file (.walSegment state.writer.wal.active.first)) =
      some inode → visible seen.reached inode = state.writer.wal.active.bytes := by
  have directoryLive : (view.handle seen.remembered seed.handle).2.1 ∈ (view.descriptors seen.remembered).slots := by
    rw [seen.sameDirectory, seen.rememberFrame.2, seen.readCensus]
    exact finish.readCustody.directoryRetained
  have root := protectedFiles.directoryBound
  rw [sameDirectory, sameCensus, sameSlot, finish.sameCensusObjects] at root
  obtain ⟨childFrame, parentFrame, children⟩ := effects.directorySync seen.directorySync directoryLive (by
    rw [seen.sameDirectory, seen.rememberFrame.2, seen.readCensus]
    change _ = some (reads.wal.keeper.calls.inventory.inode admission.cached.description)
    rw [finish.readCustody.opened]
    exact root)
  obtain ⟨directoryFrame, settled⟩ :=
    NativeReadyState.framesByDirectory sameDirectory parentFrame childFrame rootSettled children
  have keeperHandle := seen.sameKeeper.trans seen.rawKeeper
  have keeperCensus := seen.consumeFrame.2.trans seen.authorizedCensus
  have keeperRetained := finish.repair.barrierCensus.2.2.2.1
  rw [finish.sameKeeper, ← DescriptorInventory.afterDrops_append] at keeperRetained
  have issuing : (view.handle seen.consumed seen.keeper).2.1 ∈ (view.descriptors seen.consumed).slots := by
    rw [keeperHandle, keeperCensus]
    exact keeperRetained
  obtain ⟨bound, keeperLive⟩ := keeperAtIssue
  obtain ⟨synced, live⟩ := effects.keeperSync seen.keeperSync issuing
  rw [seen.keeperIssueInode, ← reads.wal.keeper.observesFile.sameObject] at synced live
  let keeperInode := reads.wal.keeper.calls.inventory.inode reads.wal.keeper.calls.slot.description
  change _ = some keeperInode at bound
  change RegularFileSyncEffect keeperInode [visible seen.consumed keeperInode] _ _ at synced
  rw [show visible seen.consumed keeperInode = layout.keeper.bytes from keeperLive, ← sameBytes] at synced
  have initialKeeper : (observe seen.consumed).files.names
      (state.session.directory.file (.walSegment state.writer.wal.active.first)) = some keeperInode := by
    rw [sameDirectory, sameFirst]
    exact bound
  refine ⟨seen.reachedCensus.trans sameCensus.symm,
    NativeReadyStorage.afterAlignedBarriers directoryFrame settled (effects.consume seen.consume)
      protectedFiles marker apart initialKeeper synced, ?_⟩
  intro inode after
  rw [synced.names, initialKeeper] at after
  obtain rfl := Option.some.inj after
  exact live.trans (keeperLive.trans sameBytes.symm)

end Alvoki.Storage.DiskSession
