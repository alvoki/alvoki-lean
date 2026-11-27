import Alvoki.Storage.Disk.Proofs.Bootstrap.NativeBootstrapMarkerPhysical

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair
open WAL.Boundary (WalInodeImage)

private abbrev stageName := "WAL.commit.next"
private abbrev markerName := "WAL.commit"
private abbrev keeperName := renderWalSegmentName 0
private abbrev markerBytes := WAL.Boundary.encode 0

structure BootstrapMarkerStageCalls (heap : Type) where
  tryCreate : FilePath → EStateM IO.Error heap (Except IO.Error IO.FS.Handle)
  statNoFollow : FilePath → EStateM IO.Error heap (Except IO.Error (IO.FS.Metadata × DeviceInode))
  unlink : FilePath → EStateM IO.Error heap (Except IO.Error Unit)
  create : FilePath → EStateM IO.Error heap IO.FS.Handle
  write : IO.FS.Handle → ByteArray → EStateM IO.Error heap Unit
  flush : IO.FS.Handle → EStateM IO.Error heap Unit

def BootstrapMarkerStageCalls.metadata (calls : BootstrapMarkerStageCalls heap) (path : FilePath) :
    EStateM IO.Error heap (Except IO.Error IO.FS.Metadata) :=
  (calls.statNoFollow path).map (Except.map Prod.fst)

noncomputable def BootstrapMarkerStageCalls.stage (calls : BootstrapMarkerStageCalls heap) (path : FilePath)
    (bytes : ByteArray) : EStateM IO.Error heap IO.FS.Handle :=
  writeFreshStagedWith calls.tryCreate (removeStaleStagingWith calls.metadata calls.unlink)
    calls.create calls.write calls.flush path bytes

variable {heap : Type} {directory : DiskDirectory} {before : LockedFileState WalSegmentRotation.State}
  {fileCalls : BootstrapOpenCalls (Cache CheckpointOpenHandle) directory before}
  {captured : BootstrapCacheOpen fileCalls.toBootstrapAdmissionCalls}
  {listed : BootstrapCheckedListing captured} {keeper : BootstrapZeroKeeperRoute listed}
  {marker : BootstrapMarkerCustody listed}
  {view : OpenCloseHeapView heap WalSegmentRotation.State} {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {seed : OpenSyncCacheAllocations captured.opened view init entry} {calls : FreshBootstrapCacheCalls heap}
  {stageEntry : heap} {observations : BootstrapMarkerStageCalls heap}

/-- The successful collision uses the actual marker stage at its reached
heap. A no-follow report identifies the existing regular child. The
unlink removes that name, and the second exclusive open supplies the
handle used for both the write and flush. -/
structure BootstrapMarkerCollisionHeap
    (publication : BootstrapMarkerPublicationHeap seed calls stageEntry)
    (keeper : BootstrapZeroKeeperRoute listed) (marker : BootstrapMarkerCustody listed)
    (observations : BootstrapMarkerStageCalls heap) (inodes : heap → WalInodeImage) where
  names : heap → DirectoryReadNamespace
  atEntry : names stageEntry = keeper.keeperView
  keeperInodes : inodes stageEntry = keeper.settledImage
  stale : RunChildLookup captured.root stageName (names stageEntry)
  missingMarker : (names stageEntry).child captured.root markerName = none
  causeName : String
  message : String
  conflict : observations.tryCreate (directory.file .stagedWalBoundary) stageEntry =
    .ok (.error (.alreadyExists causeName 17 message)) stageEntry
  metadata : IO.FS.Metadata
  checked : observations.statNoFollow (directory.file .stagedWalBoundary) stageEntry =
    .ok (.ok (metadata, stale.child)) stageEntry
  regular : metadata.type = .file
  afterDetach : heap
  detached : observations.unlink (directory.file .stagedWalBoundary) stageEntry = .ok (.ok ()) afterDetach
  unbound : (names afterDetach).child captured.root stageName = none
  otherNames : ∀ name, name ≠ stageName → (names afterDetach).child captured.root name = (names stageEntry).child captured.root name
  sameObjects : (names afterDetach).modelObject = (names stageEntry).modelObject
  otherPayloads : ∀ name child, name ≠ stageName → (names stageEntry).child captured.root name = some child →
    (inodes afterDetach).visible ((names stageEntry).modelObject child) =
      (inodes stageEntry).visible ((names stageEntry).modelObject child) ∧
    (inodes afterDetach).crashBytes ((names stageEntry).modelObject child) =
      (inodes stageEntry).crashBytes ((names stageEntry).modelObject child)
  unchangedDescriptors : view.descriptors afterDetach = view.descriptors stageEntry
  unchangedOwner : (view.files afterDetach).owners = (view.files stageEntry).owners
  handle : IO.FS.Handle
  created : heap
  recreated : observations.create (directory.file .stagedWalBoundary) afterDetach = .ok handle created
  replacement : RunChildLookup captured.root stageName (names created)
  object : (names created).modelObject replacement.child =
    (view.descriptors created).inode (view.handle created handle).2.1.description
  written : heap
  flushed : heap
  wrote : observations.write handle markerBytes created = .ok () written
  flushedRaw : observations.flush handle written = .ok () flushed
  sameSlot : (view.handle flushed handle).2.1 = (view.handle created handle).2.1
  stableName : (names flushed).child captured.root stageName = (names created).child captured.root stageName
  stableObject : (names flushed).modelObject replacement.child = (names created).modelObject replacement.child
  stageView : names flushed = marker.stageView
  source : calls.stage (directory.file .stagedWalBoundary) markerBytes =
    observations.stage (directory.file .stagedWalBoundary) markerBytes

namespace BootstrapMarkerCollisionHeap

variable {inodes : heap → WalInodeImage} {publication : BootstrapMarkerPublicationHeap seed calls stageEntry}

theorem detaches (seen : BootstrapMarkerCollisionHeap publication keeper marker observations inodes) :
    removeStaleStagingWith observations.metadata observations.unlink (directory.file .stagedWalBoundary) stageEntry =
      .ok () seen.afterDetach := by
  have regular : (seen.metadata.type == .file) = true := by rw [seen.regular]; rfl
  simp [removeStaleStagingWith, BootstrapMarkerStageCalls.metadata, EStateM.map, Bind.bind, EStateM.bind,
    Except.map, seen.checked, regular, seen.detached, RunCollection.ownedUnlinkResult, Pure.pure, EStateM.pure]

/-- The second exclusive create is the source of the existing raw
publication's stage return. Its pending entry uses the same descriptor. -/
theorem returnsAtStage (seen : BootstrapMarkerCollisionHeap publication keeper marker observations inodes) :
    calls.stage (directory.file .stagedWalBoundary) markerBytes stageEntry = .ok seen.handle seen.flushed ∧
    publication.marker.handle = seen.handle ∧ publication.marker.produced = seen.flushed := by
  have returned : calls.stage (directory.file .stagedWalBoundary) markerBytes stageEntry = .ok seen.handle seen.flushed := by
    rw [seen.source]
    simp [BootstrapMarkerStageCalls.stage, writeFreshStagedWith, withFreshStaging, Bind.bind, EStateM.bind,
      Pure.pure, EStateM.pure, seen.conflict, seen.detaches, seen.recreated, seen.wrote, seen.flushedRaw]
  have stageReturn : calls.stage (directory.file .stagedWalBoundary) markerBytes stageEntry =
      .ok publication.marker.handle publication.marker.produced := publication.marker.returnedHandle
  exact ⟨returned, EStateM.Result.ok.inj (stageReturn.symm.trans returned)⟩

/-- Detach clears the one stale staging name. The same root still holds
the empty keeper and the canonical marker is absent. Other links and
their payloads are included in the reported off-target frame. -/
theorem keepsKeeper (seen : BootstrapMarkerCollisionHeap publication keeper marker observations inodes) :
    (seen.names stageEntry).child captured.root stageName = some seen.stale.child ∧
    (seen.names seen.afterDetach).child captured.root stageName = none ∧
    (seen.names seen.afterDetach).child captured.root markerName = none ∧
    (seen.names seen.afterDetach).child captured.root keeperName = some keeper.keeperChild ∧
    (inodes seen.afterDetach).visible ((seen.names seen.afterDetach).modelObject keeper.keeperChild) = ByteArray.empty ∧
    (inodes seen.afterDetach).crashBytes ((seen.names seen.afterDetach).modelObject keeper.keeperChild) = [ByteArray.empty] ∧
    (seen.names seen.afterDetach).modelObject captured.root = (seen.names stageEntry).modelObject captured.root ∧
    view.descriptors seen.afterDetach = view.descriptors stageEntry ∧
    (view.files seen.afterDetach).owners = (view.files stageEntry).owners := by
  obtain ⟨_, _, bound, object⟩ := keeper.settledCustody
  have before : (seen.names stageEntry).child captured.root keeperName = some keeper.keeperChild := seen.atEntry ▸ bound
  obtain ⟨visible, durable⟩ := seen.otherPayloads keeperName keeper.keeperChild (by decide) before
  rw [seen.keeperInodes, seen.atEntry, keeper.keeperObjects, object] at visible durable
  have staleName := seen.stale.binds
  rw [seen.stale.atRoot, seen.stale.atName] at staleName
  rw [seen.sameObjects]
  refine ⟨staleName, seen.unbound, (seen.otherNames markerName (by decide)).trans seen.missingMarker,
    (seen.otherNames keeperName (by decide)).trans before, ?_, ?_, rfl, seen.unchangedDescriptors, seen.unchangedOwner⟩
  · rw [seen.atEntry, keeper.keeperObjects, object]
    exact visible.trans keeper.settledVisible
  · rw [seen.atEntry, keeper.keeperObjects, object]
    exact durable.trans keeper.settledEmpty.2

/-- The common marker publication uses the child and slot reported by
the second exclusive create. -/
theorem replacesChild (seen : BootstrapMarkerCollisionHeap publication keeper marker observations inodes) :
    seen.replacement.child = marker.stageChild.child ∧
    (view.handle publication.marker.produced publication.marker.handle).2.1 = (view.handle seen.created seen.handle).2.1 ∧
    marker.inodeState.active = (view.descriptors seen.created).inode (view.handle seen.created seen.handle).2.1.description := by
  have binding := seen.replacement.binds
  rw [seen.replacement.atRoot, seen.replacement.atName] at binding
  have held := seen.stableName.trans binding
  rw [seen.stageView] at held
  have sameChild := (marker.stageChild.child_eq held).symm
  have slots : (view.handle publication.marker.produced publication.marker.handle).2.1 =
      (view.handle seen.created seen.handle).2.1 := by
    rw [seen.returnsAtStage.2.1, seen.returnsAtStage.2.2]
    exact seen.sameSlot
  refine ⟨sameChild, slots, ?_⟩
  rw [marker.stageInode, ← sameChild, ← seen.stageView, seen.stableObject]
  exact seen.object

/-- The actual replacement goes through the common pending-file and
directory barriers. They publish the exact inode opened by the second
create, alongside the unchanged empty keeper. -/
theorem publishes (seen : BootstrapMarkerCollisionHeap publication keeper marker observations inodes)
    {handoff : BootstrapKeeperMarkerHandoff keeper marker} {effects : BootstrapKeeperMarkerHandoff.ReturnedCensus marker}
    (physical : publication.Physical inodes handoff effects)
    (keeperReady : (view.files stageEntry).image = ⟨before.image.metadata.syncDirectory, .durable⟩) :
    let final := publication.markerDirectory.reached
    let inode := (view.descriptors seen.created).inode (view.handle seen.created seen.handle).2.1.description
    calls.publishZeroMarker directory seed.directoryRef seed.activeRef seed.pendingRef stageEntry =
      .ok ⟨.empty, 0, 0, 0⟩ final ∧
    handoff.afterMarkerNames keeperName = [some keeper.keeperChild] ∧
    handoff.afterMarkerNames markerName = [some seen.replacement.child] ∧
    (inodes final).crashBytes keeper.settledImage.active = [ByteArray.empty] ∧
    (inodes final).crashBytes inode = [markerBytes] ∧
    view.pending final seed.pendingRef = [] ∧
    view.descriptors final = effects.reached ∧
    (view.descriptors final).references marker.slot.description = [] ∧
    fileCalls.slot ∈ (view.descriptors final).slots ∧ captured.cached ∈ (view.descriptors final).slots := by
  intro final inode
  obtain ⟨ran, _, pending⟩ := publication.returns
  obtain ⟨_, _, _, _, _, _, keeperName, markerName, keeperBytes, markerBytes, census, released, owner, cached⟩ :=
    physical.settles keeperReady seen.keeperInodes
  obtain ⟨child, _, object⟩ := seen.replacesChild
  rw [← child] at markerName
  have payload : (inodes final).crashBytes inode = [WAL.Boundary.encode 0] := by
    dsimp only [inode]
    rw [← object]
    exact markerBytes
  exact ⟨ran, keeperName, markerName, keeperBytes, payload, pending, census, released, owner, cached⟩

end BootstrapMarkerCollisionHeap

end Alvoki.Storage.DiskSession
