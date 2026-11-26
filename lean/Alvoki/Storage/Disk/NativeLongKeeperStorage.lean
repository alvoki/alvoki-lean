import Alvoki.Storage.Disk.NativeLongKeeperSettlementHeap
import Alvoki.Storage.Disk.NativeOpenReadyStorage
import Alvoki.Storage.Disk.NativeWalPublicationTail

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

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
  rw [stagedHandle, stageLive] at persisted
  change RegularFileSyncEffect replacement [layout.keeper.bytes] (observe synced.consumed) (observe synced.reached) at persisted
  obtain ⟨staging, _, _, _, keeper, _⟩ := renamed.movesStagedInode
  obtain ⟨movedBytes, movedContents⟩ := renameEffect renamed.renamed staging
  have root := protectedFiles.directoryBound
  rw [sameDirectory, sameCensus, sameSlot, finish.sameCensusObjects] at root
  obtain ⟨children, parent, keptContents⟩ := directoryEffect seen.synced
    (by rw [ran.directoryAtIssue]; exact ran.directoryLive)
    (by rw [ran.directoryAtIssue]; exact root)
  have childFiles : (observe renamed.reached).files.Frames
      (fun path => ∃ file, path = directory.file file) (observe seen.reached).files := by
    rintro _ ⟨file, rfl⟩
    exact ⟨children.visible file, fun inode named =>
      children.bytes _ (.inl rfl) file inode ((children.visible file).trans named)⟩
  obtain ⟨wholeFrame, settled⟩ := NativeReadyState.framesByDirectory sameDirectory parent childFiles rootSettled
    (by simpa only [sameDirectory] using children.settled rfl)
  have activeBytes := sameBytes.symm
  have keeperAtRename : (observe renamed.reached).files.Stored
      (state.session.directory.file (.walSegment state.writer.wal.active.first)) state.writer.wal.active.bytes := by
    refine ⟨replacement, ?_, ?_⟩
    · rw [sameDirectory, sameFirst]
      exact keeper
    · have bytes : (observe synced.reached).files.bytes replacement = [layout.keeper.bytes] := by
        simpa using persisted.bytes replacement
      exact movedBytes.trans (bytes.trans (congrArg (fun bytes => [bytes]) activeBytes))
  have protectedFrame (path) (scope : state.writeFramePath path) :=
    wholeFrame path (NativeReadyState.crashPath_iff_write.mpr (.inr (.inr scope)))
  have markerPath : state.crashPath (state.session.directory.file .walBoundary) :=
    NativeReadyState.crashPath_iff_write.mpr (.inl rfl)
  have keeperPath : state.crashPath (state.session.directory.file (.walSegment state.writer.wal.active.first)) :=
    NativeReadyState.crashPath_iff_write.mpr (.inr (.inl rfl))
  refine ⟨(congrArg (fun observed => observed.2.1) ran.final).trans sameCensus.symm, ⟨protectedFiles.frame protectedFrame, wholeFrame.stored markerPath marker,
    wholeFrame.stored keeperPath keeperAtRename, settled⟩, ?_⟩
  intro inode bound
  have sameInode : (observe seen.reached).files.names (directory.file (.walSegment layout.keeper.first)) = some replacement :=
    ran.keeperBound
  rw [sameDirectory, sameFirst, sameInode] at bound
  obtain rfl := Option.some.inj bound
  exact keptContents.trans (movedContents.trans (stagedContents.trans (stageLive.trans activeBytes)))

end Alvoki.Storage.DiskSession
