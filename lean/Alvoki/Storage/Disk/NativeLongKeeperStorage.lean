import Alvoki.Storage.Disk.NativeLongKeeperSettlementHeap
import Alvoki.Storage.Disk.NativeOpenReadyStorage
import Alvoki.Storage.Disk.NativeWalPublicationTail
import Alvoki.Storage.Disk.NativeRetainedOpenStorage

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair CheckpointPublication
open WAL.Boundary (WalInodeImage)

section Replacement

variable {heap : Type}

/-- An already synced staging inode becomes the keeper at the successful
rename. Loading the cached root carries the selected paths and scratch
name to the actual directory issue heap. That barrier settles the
children; the root's own name stays settled in its parent separately. -/
theorem NativeReadyStorage.afterKeeperReplacement
    (state : NativeReadyState)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    {stageIssued stageSynced renamed rootIssued reached : heap} {old replacement : Nat}
    (stageBinding : (observe stageIssued).files.names (state.session.directory.file .stagedWal) = some replacement)
    (stagedPrefix : visible stageIssued replacement = state.writer.wal.active.bytes)
    (fileSync : RegularFileSyncEffect replacement [visible stageIssued replacement]
      (observe stageIssued) (observe stageSynced))
    (fileSyncVisible : visible stageSynced replacement = visible stageIssued replacement)
    (oldBinding : (observe stageSynced).files.names
      (state.session.directory.file (.walSegment state.writer.wal.active.first)) = some old)
    (distinct : replacement ≠ old)
    (moved : (observe renamed).files.names (state.session.directory.file (.walSegment state.writer.wal.active.first)) =
      (observe stageSynced).files.names (state.session.directory.file .stagedWal))
    (detached : (observe renamed).files.names (state.session.directory.file .stagedWal) = none)
    (renameBytes : (observe renamed).files.bytes replacement = (observe stageSynced).files.bytes replacement)
    (renameVisible : visible renamed replacement = visible stageSynced replacement)
    (protectedFiles : NativeReadyProtectedStorage state (observe renamed).files)
    (marker : (observe renamed).files.Stored (state.session.directory.file .walBoundary)
      (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64))
    (rootSettled : ∀ names ∈ (observe renamed).crashNames,
      names state.session.directory.path = (observe renamed).files.names state.session.directory.path)
    (load : (observe renamed).Frames (fun path => state.crashPath path ∨ path = state.session.directory.file .stagedWal)
      (observe rootIssued))
    (loadVisible : visible rootIssued replacement = visible renamed replacement)
    (children : WalRootSyncEffect state.session.directory true (observe rootIssued) (observe reached))
    (parent : (observe rootIssued).Frames (· = state.session.directory.path) (observe reached))
    (directoryVisible : visible reached replacement = visible rootIssued replacement) :
    let directory := state.session.directory
    let keeper := directory.file (.walSegment state.writer.wal.active.first)
    let scratch := directory.file .stagedWal
    NativeReadyStorage state (observe reached) ∧
      (observe reached).files.names keeper = some replacement ∧
      (observe reached).files.names keeper ≠ (observe stageSynced).files.names keeper ∧
      (observe reached).files.names scratch = none ∧
      (∀ names ∈ (observe reached).crashNames, names keeper = some replacement ∧ names scratch = none) ∧
      ∀ inode, (observe reached).files.names keeper = some inode → visible reached inode = state.writer.wal.active.bytes := by
  intro directory keeper scratch
  have rootScope : state.crashPath directory.path := .inl rfl
  have markerScope : state.crashPath (directory.file .walBoundary) :=
    NativeReadyState.crashPath_iff_write.mpr (.inl rfl)
  have keeperScope : state.crashPath keeper := NativeReadyState.crashPath_iff_write.mpr (.inr (.inl rfl))
  have rootAtIssue := (load.weaken (scope := (· = directory.path)) (fun path equal => .inl (equal.symm ▸ rootScope))).settledFrom
    (fun names member path equal => equal.symm ▸ rootSettled names member)
  have childFiles : (observe rootIssued).files.Frames
      (fun path => ∃ file, path = directory.file file) (observe reached).files := by
    rintro _ ⟨file, rfl⟩
    exact ⟨children.visible file, fun inode named =>
      children.bytes _ (.inl rfl) file inode ((children.visible file).trans named)⟩
  obtain ⟨directoryFrame, settled⟩ := NativeReadyState.framesByDirectory rfl parent childFiles
    (fun names member => rootAtIssue names member _ rfl) (children.settled rfl)
  have selected := (load.weaken (fun _ kept => Or.inl kept)).visible.trans directoryFrame
  have syncedBinding : (observe stageSynced).files.names scratch = some replacement :=
    (congrFun fileSync.names scratch).trans stageBinding
  have renamedBinding : (observe renamed).files.names keeper = some replacement := moved.trans syncedBinding
  have persisted : (observe stageSynced).files.bytes replacement = [state.writer.wal.active.bytes] := by
    simpa [stagedPrefix] using fileSync.bytes replacement
  have keeperAtRename : (observe renamed).files.Stored keeper state.writer.wal.active.bytes :=
    ⟨replacement, renamedBinding, renameBytes.trans persisted⟩
  have named : (observe reached).files.names keeper = some replacement :=
    (selected keeper keeperScope).1.trans renamedBinding
  have gone : (observe reached).files.names scratch = none :=
    (children.visible .stagedWal).trans ((load.visible scratch (.inr rfl)).1.trans detached)
  refine ⟨⟨protectedFiles.frame (fun path kept => selected path
    (NativeReadyState.crashPath_iff_write.mpr (.inr (.inr kept)))), selected.stored markerScope marker,
    selected.stored keeperScope keeperAtRename, settled⟩, named, ?_, gone, ?_, ?_⟩
  · intro unchanged
    exact distinct (Option.some.inj (named.symm.trans (unchanged.trans oldBinding)))
  · intro names member
    exact ⟨(children.settled rfl names member (.walSegment state.writer.wal.active.first)).trans named,
      (children.settled rfl names member .stagedWal).trans gone⟩
  · intro inode held
    obtain rfl := Option.some.inj (held.symm.trans named)
    exact directoryVisible.trans (loadVisible.trans (renameVisible.trans (fileSyncVisible.trans stagedPrefix)))

end Replacement

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout retry.image history} {published : CheckpointPublication.Image}
  {admission : CensusOpenAdmissionReports input directory inventory retry}
  {vacant : TryLockObserves retry.owners directory (.ok true)} {checkpoint : Option (PackedTable × UInt64)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}
  {calls : CapturedAlignedCallbacks admission} {reads : CapturedMarkedReadReports admission layout published}
  {heap : Type} {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {finish : CapturedLongKeeperFinish calls reads vacant selected}
  {seed : OpenSyncCacheAllocations admission.opened view init entry}
  {reader : MarkedTemporaryReadCalls heap} {before : heap}
  {read : NativeLongKeeperReadHeap finish seed reader before} {sync : AlignedKeeperCacheCallbacks heap}
  {authorization : NativeLongKeeperAuthorizationHeap read sync}
  {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)}
  {suffix : NativeLongKeeperSuffixHeap authorization remove} {stage : LongKeeperStageCallbacks heap}

variable {staged : NativeLongKeeperFreshStageHeap suffix stage}
  {observe : heap → CheckpointStorageObservation} {visible : heap → Nat → ByteArray}
  {synced : NativeLongKeeperStagedSyncHeap staged (fun heap => (observe heap).files.names)}
  {rename : FilePath → FilePath → EStateM IO.Error heap Unit}
  {renamed : NativeLongKeeperRenameHeap synced rename}

local notation "replacement" => finish.stage.inventory.inode finish.stage.slot.description

private theorem NativeReadyState.stagedWalOutsideRetryFootprint (state : NativeReadyState) :
    ∀ path, state.selectedRetryPath path → path ≠ state.session.directory.file .stagedWal := by
  let directory := state.session.directory
  have basename {left right : DiskFile} (same : directory.file left = directory.file right) :=
    (String.append_right_inj (directory.path.toString ++ "/")).mp (congrArg FilePath.toString same)
  intro path retained same
  rcases retained with marker | held
  · have equal := basename (marker.symm.trans same)
    change "WAL.commit" = "WAL.next" at equal
    exact (by decide : "WAL.commit" ≠ "WAL.next") equal
  rcases held with root | lock | manifest | sealedPath | runPath
  · exact file_ne_directory directory .stagedWal (root.symm.trans same).symm
  · have equal := basename (lock.symm.trans same)
    change "LOCK" = "WAL.next" at equal
    exact (by decide : "LOCK" ≠ "WAL.next") equal
  · have equal := basename (manifest.symm.trans same)
    change "MANIFEST" = "WAL.next" at equal
    exact (by decide : "MANIFEST" ≠ "WAL.next") equal
  · obtain ⟨segment, _, equal⟩ := sealedPath
    obtain ⟨_, impossible⟩ := DiskDirectory.walSegment_exclusive (equal.symm.trans same).symm
    cases impossible
  · obtain ⟨_, metadata, index, _, _, _, equal⟩ := runPath
    have samePrefix := congrArg (fun name : String => name.toList.take 4) (basename (equal.symm.trans same))
    change ("run-" ++ metadata.header.generation.toNat.repr ++ "-" ++ index.repr ++ ".v3").toList.take 4 =
      "WAL.next".toList.take 4 at samePrefix
    simp [String.toList_append] at samePrefix


/-- A captured staging write can change its own inode, while its name
and every protected binding are disjoint. Project those local effects
to the selected retry footprint. -/
private theorem RunWriteInodeFrame.framesSelectedStage
    {state : NativeReadyState} {dir : DiskDirectory} {before after : WalInodeImage}
    {oldRuns newRuns : RunUnlinkImage} {inode : Nat}
    {entry : RunDirectoryInodeView dir before oldRuns} {reached : RunDirectoryInodeView dir after newRuns}
    (effect : RunWriteInodeFrame (dir.file .stagedWal) inode after entry reached)
    (sameDirectory : state.session.directory = dir)
    (apart : ∀ path, state.selectedRetryPath path → entry.visible path ≠ some inode) :
    state.SelectedRetryFrame entry.storageObservation reached.storageObservation before.visible after.visible := by
  have separate (path : FilePath) (held : state.selectedRetryPath path) : path ≠ dir.file .stagedWal := by
    rw [← sameDirectory]
    exact state.stagedWalOutsideRetryFootprint path held
  have distinct (path : FilePath) (held : state.selectedRetryPath path)
      (object : Nat) (bound : entry.visible path = some object) : object ≠ inode := by
    intro same
    exact apart path held (same ▸ bound)
  refine ⟨?_, ?_, ?_⟩
  · intro path held
    exact ⟨effect.visibleNames path (separate path held),
      fun object bound => congrArg (fun bytes => [bytes]) (effect.visibleBytes object (distinct path held object bound))⟩
  · intro path held
    exact ⟨effect.visibleNames path (separate path held), fun object bound => effect.crashBytes object (distinct path held object bound)⟩
  · have root : state.selectedRetryPath state.session.directory.path := .inr (.inl rfl)
    refine ⟨?_, ?_⟩
    · intro path same
      subst path
      exact ⟨effect.visibleNames _ (separate _ root),
        fun object bound => effect.crashBytes object (distinct _ root object bound)⟩
    · intro names chosen
      obtain ⟨prior, available, keeps⟩ := effect.crashNames names chosen
      exact ⟨prior, available, fun path same => keeps path (same.symm ▸ separate _ root)⟩

/-- On the actual staging path the winning exclusive create supplies the
new, disjoint inode. Its write and flush preserve the selected files.
The real fsync uses that same descriptor and makes its payload durable. -/
theorem NativeLongKeeperStagedSyncHeap.preservesSelectedStage
    (state : NativeReadyState) (sameDirectory : state.session.directory = directory)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (buffered : heap → IO.FS.Handle → ByteArray)
    (observation : ∀ atHeap, RunDirectoryInodeView directory (inodes atHeap) (runs atHeap))
    (seen : NativeLongKeeperStagedSyncHeap staged (fun atHeap => (observation atHeap).visible))
    (acquisition : stage.AcquisitionFrames (directory.file .stagedWal) suffix.reached
      (fun before after => state.SelectedRetryFrame (observation before).storageObservation
        (observation after).storageObservation (inodes before).visible (inodes after).visible))
    (freshFirst : ∀ {file opened}, stage.tryCreate (directory.file .stagedWal) suffix.reached = .ok (.ok file) opened →
      let inode := (view.descriptors opened).inode (view.handle opened file).2.1.description
      (∀ path, state.selectedRetryPath path → (observation opened).visible path ≠ some inode) ∧
      (inodes opened).visible inode = ByteArray.empty ∧ buffered opened file = ByteArray.empty)
    (freshRetry : ∀ {file before opened}, stage.create (directory.file .stagedWal) before = .ok file opened →
      let inode := (view.descriptors opened).inode (view.handle opened file).2.1.description
      (∀ path, state.selectedRetryPath path → (observation opened).visible path ≠ some inode) ∧
      (inodes opened).visible inode = ByteArray.empty ∧ buffered opened file = ByteArray.empty)
    (wrote : stage.write staged.descriptor layout.keeper.bytes staged.created = .ok () staged.written →
      stage.flush staged.descriptor staged.written = .ok () staged.flushed →
      RunWriteInodeFrame (directory.file .stagedWal) replacement (inodes staged.flushed)
        (observation staged.created) (observation staged.flushed))
    (writePayload : stage.write staged.descriptor layout.keeper.bytes staged.created = .ok () staged.written →
      (inodes staged.written).visible replacement ++ buffered staged.written staged.descriptor =
        ((inodes staged.created).visible replacement ++ buffered staged.created staged.descriptor) ++ layout.keeper.bytes)
    (flushPayload : stage.flush staged.descriptor staged.written = .ok () staged.flushed →
      (inodes staged.flushed).visible replacement =
        (inodes staged.written).visible replacement ++ buffered staged.written staged.descriptor)
    (stored : sync.modifyPending seed.pendingRef (pushPending (directory.file .stagedWal) staged.descriptor) staged.flushed =
      .ok () staged.recorded →
      state.SelectedRetryFrame (observation staged.flushed).storageObservation (observation staged.recorded).storageObservation
        (inodes staged.flushed).visible (inodes staged.recorded).visible ∧
      (inodes staged.recorded).visible replacement = (inodes staged.flushed).visible replacement)
    (consumed : sync.setPending seed.pendingRef [] staged.recorded = .ok () seen.consumed →
      state.SelectedRetryFrame (observation staged.recorded).storageObservation (observation seen.consumed).storageObservation
        (inodes staged.recorded).visible (inodes seen.consumed).visible ∧
      (inodes seen.consumed).visible replacement = (inodes staged.recorded).visible replacement)
    (fsync : sync.sync staged.descriptor seen.consumed = .ok () seen.reached →
      (view.handle seen.consumed staged.descriptor).2.1 ∈ (view.descriptors seen.consumed).slots →
      RegularFileSyncEffect ((view.handle seen.consumed staged.descriptor).1.inode
        (view.handle seen.consumed staged.descriptor).2.1.description) [(inodes seen.consumed).visible replacement]
        (observation seen.consumed).storageObservation (observation seen.reached).storageObservation ∧
      (inodes seen.reached).visible = (inodes seen.consumed).visible) :
    state.SelectedRetryFrame (observation suffix.reached).storageObservation (observation seen.reached).storageObservation
        (inodes suffix.reached).visible (inodes seen.reached).visible ∧
      (observation seen.reached).visible (directory.file .stagedWal) = some replacement ∧
      (inodes seen.reached).crashBytes replacement = [layout.keeper.bytes] ∧
      (inodes seen.reached).visible replacement = layout.keeper.bytes := by
  have opened := acquisition.keeps (fun atHeap => .refl _ _ _) NativeReadyState.SelectedRetryFrame.trans
  rw [staged.acquired] at opened
  have fresh := withFreshStaging_acquireProvides stage.tryCreate stage.detachStale stage.create
    (directory.file .stagedWal) (fun file atHeap =>
      let inode := (view.descriptors atHeap).inode (view.handle atHeap file).2.1.description
      (∀ path, state.selectedRetryPath path → (observation atHeap).visible path ≠ some inode) ∧
      (inodes atHeap).visible inode = ByteArray.empty ∧ buffered atHeap file = ByteArray.empty)
    staged.acquired freshFirst freshRetry
  obtain ⟨distinct, empty, noBuffered⟩ := fresh
  rw [staged.openedCensus, staged.openedSlot] at distinct empty
  have stageWritten := RunWriteInodeFrame.framesSelectedStage (wrote staged.wrote staged.flush) sameDirectory distinct
  obtain ⟨remembered, stagedVisible⟩ := stored staged.record
  obtain ⟨cleared, consumedVisible⟩ := consumed seen.cleared
  have inPending := stageWritten.trans (remembered.trans cleared)
  have bytes := consumedVisible.trans (stagedVisible.trans ((flushPayload staged.flush).trans (writePayload staged.wrote)))
  rw [empty, noBuffered, ByteArray.append_empty, ByteArray.empty_append] at bytes
  have apart (path : FilePath) (held : state.selectedRetryPath path)
      (object : Nat) (bound : (observation seen.consumed).visible path = some object) : object ≠ replacement := by
    intro same
    have preserved := (inPending.live path held).1
    exact distinct path held (preserved.symm.trans (same ▸ bound))
  obtain ⟨_, handleAtSync, live, named, _⟩ := seen.syncs
  obtain ⟨effect, sameContents⟩ := fsync seen.synced (by rw [handleAtSync]; exact live)
  rw [handleAtSync, bytes] at effect
  rw [seen.consumeCensus, staged.atSync] at named
  have durable := effect.frames (footprint := state.selectedRetryPath) apart
  have parent := durable.weaken (fun path equal => .inr (.inl equal))
  have kept : state.SelectedRetryFrame (observation seen.consumed).storageObservation
      (observation seen.reached).storageObservation (inodes seen.consumed).visible (inodes seen.reached).visible :=
    ⟨fun path held => ⟨(durable.visible path held).1, by rw [sameContents]; intros; rfl⟩, durable.visible, parent⟩
  exact ⟨opened.trans (inPending.trans kept), (congrFun effect.names _).trans named,
    by simpa [RunDirectoryInodeView.storageObservation] using effect.bytes replacement,
    sameContents ▸ bytes⟩

/-- The actual rename transfers the synced staging inode to the keeper
name. The old keeper and scratch names are outside the immutable paths. -/
theorem NativeLongKeeperRenameHeap.preservesSelectedReplacement
    (state : NativeReadyState) (valid : state.Valid) (sameDirectory : state.session.directory = directory)
    (keeperStart : state.writer.wal.active.first ≤ layout.keeper.first)
    (seen : NativeLongKeeperRenameHeap synced rename)
    (stagedBytes : (observe synced.reached).files.bytes replacement = [layout.keeper.bytes])
    (stagedVisible : visible synced.reached replacement = layout.keeper.bytes)
    (frame : rename (directory.file .stagedWal) (directory.file (.walSegment layout.keeper.first)) synced.reached =
      .ok () seen.reached →
      (∀ path, path ≠ directory.file .stagedWal → path ≠ directory.file (.walSegment layout.keeper.first) →
        (observe seen.reached).files.names path = (observe synced.reached).files.names path) ∧
      (∀ names ∈ (observe seen.reached).crashNames, ∃ prior ∈ (observe synced.reached).crashNames,
        ∀ path, path ≠ directory.file .stagedWal → path ≠ directory.file (.walSegment layout.keeper.first) →
          names path = prior path) ∧
      (∀ path, state.selectedRetryPath path ∨ path = directory.file .stagedWal →
        ∀ inode, (observe synced.reached).files.names path = some inode →
          (observe seen.reached).files.bytes inode = (observe synced.reached).files.bytes inode ∧
          visible seen.reached inode = visible synced.reached inode)) :
    state.SelectedRetryFrame (observe synced.reached) (observe seen.reached) (visible synced.reached) (visible seen.reached) ∧
      (observe seen.reached).files.names (directory.file (.walSegment layout.keeper.first)) = some replacement ∧
      (observe seen.reached).files.bytes replacement = [layout.keeper.bytes] ∧
      visible seen.reached replacement = layout.keeper.bytes := by
  obtain ⟨unchanged, survivors, payload⟩ := frame seen.renamed
  have offStage {path} (kept : state.selectedRetryPath path) : path ≠ directory.file .stagedWal := by
    rw [← sameDirectory]
    exact state.stagedWalOutsideRetryFootprint path kept
  have offKeeper {path} (kept : state.selectedRetryPath path) : path ≠ directory.file (.walSegment layout.keeper.first) := by
    rw [← sameDirectory]
    exact NativeReadyState.protectedPathNeWalFromActive valid kept keeperStart
  have durable : (observe synced.reached).Frames state.selectedRetryPath (observe seen.reached) := by
    refine ⟨?_, ?_⟩
    · intro path kept
      exact ⟨unchanged path (offStage kept) (offKeeper kept), fun inode named => (payload path (.inl kept) inode named).1⟩
    · intro names allowed
      obtain ⟨prior, admitted, stays⟩ := survivors names allowed
      exact ⟨prior, admitted, fun path kept => stays path (offStage kept) (offKeeper kept)⟩
  have live : (⟨(observe synced.reached).files.names, fun inode => [visible synced.reached inode]⟩ :
      CheckpointSurvivingFiles).Frames state.selectedRetryPath
      ⟨(observe seen.reached).files.names, fun inode => [visible seen.reached inode]⟩ :=
    fun path kept => ⟨(durable.visible path kept).1, fun inode named =>
      congrArg (fun bytes => [bytes]) (payload path (.inl kept) inode named).2⟩
  obtain ⟨source, _, _, _, moved, _⟩ := seen.movesStagedInode
  obtain ⟨durableStage, liveStage⟩ := payload (directory.file .stagedWal) (.inr rfl) replacement source
  exact ⟨⟨live, durable.visible, durable.weaken (fun _ root => .inr (.inl root))⟩,
    moved, durableStage.trans stagedBytes, liveStage.trans stagedVisible⟩

/-- The literal staged-file fsync stores the selected prefix. The
rename moves the same inode, and the final directory fsync settles
its keeper binding together with the other selected children. -/
theorem NativeLongKeeperSettlementHeap.readyStorage
    (seen : NativeLongKeeperSettlementHeap renamed)
    {state : NativeReadyState}
    (sameDirectory : state.session.directory = directory) (sameCensus : state.census = finish.census)
    (sameSlot : state.directorySlot = admission.cached) (sameFirst : state.writer.wal.active.first = layout.keeper.first)
    (sameBytes : state.writer.wal.active.bytes = layout.keeper.bytes)
    (protectedFiles : NativeReadyProtectedStorage state (observe renamed.reached).files)
    (marker : (observe renamed.reached).files.Stored (state.session.directory.file .walBoundary)
      (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64))
    (rootSettled : ∀ names ∈ (observe renamed.reached).crashNames,
      names state.session.directory.path = (observe renamed.reached).files.names state.session.directory.path)
    (stageLive : visible synced.consumed replacement = layout.keeper.bytes)
    (stageEffect : sync.sync staged.descriptor synced.consumed = .ok () synced.reached →
      (view.handle synced.consumed staged.descriptor).2.1 ∈ (view.descriptors synced.consumed).slots →
      RegularFileSyncEffect ((view.handle synced.consumed staged.descriptor).1.inode
        (view.handle synced.consumed staged.descriptor).2.1.description)
        [visible synced.consumed replacement] (observe synced.consumed) (observe synced.reached) ∧
      visible synced.reached replacement = visible synced.consumed replacement)
    (renameEffect : rename (directory.file .stagedWal) (directory.file (.walSegment layout.keeper.first))
      synced.reached = .ok () renamed.reached →
      (observe synced.reached).files.names (directory.file .stagedWal) = some replacement →
      (observe renamed.reached).files.bytes replacement = (observe synced.reached).files.bytes replacement ∧
      visible renamed.reached replacement = visible synced.reached replacement)
    (directoryEffect : sync.sync seed.handle renamed.reached = .ok () seen.reached →
      (view.handle renamed.reached seed.handle).2.1 ∈ (view.descriptors renamed.reached).slots →
      (observe renamed.reached).files.names directory.path = some
        ((view.handle renamed.reached seed.handle).1.inode (view.handle renamed.reached seed.handle).2.1.description) →
      WalRootSyncEffect directory true (observe renamed.reached) (observe seen.reached) ∧
      (observe renamed.reached).Frames (· = state.session.directory.path) (observe seen.reached) ∧
      visible seen.reached replacement = visible renamed.reached replacement) :
    view.descriptors seen.reached = state.census ∧ NativeReadyStorage state (observe seen.reached) ∧
    ∀ inode, (observe seen.reached).files.names (state.session.directory.file (.walSegment state.writer.wal.active.first)) =
      some inode → visible seen.reached inode = state.writer.wal.active.bytes := by
  have ran := seen.returns
  obtain ⟨_, stagedHandle, stagedLive, _, _⟩ := synced.syncs
  obtain ⟨persisted, stagedContents⟩ := stageEffect synced.synced (by rw [stagedHandle]; exact stagedLive)
  rw [stagedHandle] at persisted
  change RegularFileSyncEffect replacement [visible synced.consumed replacement]
    (observe synced.consumed) (observe synced.reached) at persisted
  obtain ⟨staging, oldBinding, differentBindings, detached, keeper, _⟩ := renamed.movesStagedInode
  obtain ⟨movedBytes, movedContents⟩ := renameEffect renamed.renamed staging
  have root := protectedFiles.directoryBound
  rw [sameDirectory, sameCensus, sameSlot, finish.sameCensusObjects] at root
  obtain ⟨children, parent, keptContents⟩ := directoryEffect seen.synced
    (by rw [ran.directoryAtIssue]; exact ran.directoryLive)
    (by rw [ran.directoryAtIssue]; exact root)
  have sourceAtIssue := (congrFun persisted.names (directory.file .stagedWal)).symm.trans staging
  have distinct : replacement ≠ finish.rename.original.active := by
    intro same
    exact differentBindings (staging.trans ((congrArg some same).trans oldBinding.symm))
  have ⟨ready, _, _, _, _, live⟩ := NativeReadyStorage.afterKeeperReplacement state observe visible
    (by simpa only [sameDirectory] using sourceAtIssue) (stageLive.trans sameBytes.symm)
    persisted stagedContents
    (by rw [sameDirectory, sameFirst]; exact oldBinding) distinct
    (by rw [sameDirectory, sameFirst]; exact keeper.trans staging.symm)
    (by rw [sameDirectory]; exact detached) movedBytes movedContents protectedFiles marker rootSettled
    (.refl _ _) rfl (sameDirectory.symm ▸ children) parent keptContents
  exact ⟨(congrArg (fun observed => observed.2.1) ran.final).trans sameCensus.symm, ready, live⟩

end Alvoki.Storage.DiskSession
