import Alvoki.Storage.Disk.NativeOpenReadyStorage
import Alvoki.Storage.Disk.Proofs.Keeper.NativePrunedAlignedKeeperCache

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write} {layout : CanonicalKeeperLayout retry.image history}
  {published : CheckpointPublication.Image}
  {admission : CensusOpenAdmissionReports input directory inventory retry}
  {vacant : TryLockObserves retry.owners directory (.ok true)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}
  {calls : CapturedAlignedCallbacks admission} {reads : CapturedMarkedReadReports admission layout published}
  {finish : CapturedPrunedAlignedFinish calls reads vacant selected} {heap : Type}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap} {cacheEntry entry : heap}
  {seed : OpenSyncCacheAllocations admission.opened view init cacheEntry} {callbacks : AlignedKeeperCacheCallbacks heap}
  {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)}

/-- The accepted drops and the temporary keeper insert leave the
admission's inode map unchanged. -/
theorem CapturedPrunedAlignedFinish.sameCensusObjects
    (finish : CapturedPrunedAlignedFinish calls reads vacant selected) :
    finish.census.inode = admission.reached.inode := by
  unfold CapturedPrunedAlignedFinish.census
  rw [finish.sameKeeper]
  change reads.wal.keeper.calls.inventory.inode = admission.reached.inode
  rw [finish.reader.opened]
  rfl

variable (seen : PrunedAlignedKeeperCacheReport finish view init cacheEntry seed callbacks remove entry)

local notation "keeperPath" => directory.file (DiskFile.walSegment layout.keeper.first)
local notation "keeperInode" =>
  DescriptorInventory.inode (OpenCloseHeapView.descriptors view (PrunedAlignedKeeperCacheReport.consumed seen))
    (DescriptorSlot.description (Prod.fst (Prod.snd (OpenCloseHeapView.handle view
      (PrunedAlignedKeeperCacheReport.consumed seen) (PrunedAlignedKeeperCacheReport.keeper seen)))))

/-- The second directory barrier settles the names left by the exact
ordered unlink pass. It preserves the parent binding and the selected
children. The final fsync makes the retained keeper durable. -/
theorem PrunedAlignedKeeperCacheReport.readyStorage
    (later : ∀ first ∈ retry.image.later.visible, layout.range.through < first)
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit) (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    {state : NativeReadyState}
    (sameDirectory : state.session.directory = directory) (sameCensus : state.census = finish.census)
    (sameSlot : state.directorySlot = admission.cached)
    (sameFirst : state.writer.wal.active.first = layout.keeper.first)
    (sameBytes : state.writer.wal.active.bytes = layout.keeper.bytes)
    (protectedFiles : NativeReadyProtectedStorage state (observe seen.pruned).files)
    (marker : (observe seen.pruned).files.Stored (state.session.directory.file .walBoundary)
      (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64))
    (rootSettled : ∀ names ∈ (observe seen.pruned).crashNames,
      names state.session.directory.path = (observe seen.pruned).files.names state.session.directory.path)
    (prunedBindings : ∀ first, first = layout.keeper.first ∨ first ∈ retry.image.later.visible →
      (observe seen.pruned).files.names (directory.file (.walSegment first)) =
        finish.prune.reached (directory.file (.walSegment first)))
    (suffixEffect : callbacks.sync seed.handle seen.pruned = .ok () seen.suffixSettled →
      (view.handle seen.pruned seed.handle).2.1 ∈ (view.descriptors seen.pruned).slots →
      (observe seen.pruned).files.names directory.path = some
        ((view.descriptors seen.pruned).inode (view.handle seen.pruned seed.handle).2.1.description) →
      (observe seen.pruned).files.Frames (fun path => ∃ file, path = directory.file file) (observe seen.suffixSettled).files ∧
      (observe seen.pruned).Frames (· = state.session.directory.path) (observe seen.suffixSettled) ∧
      ∀ names ∈ (observe seen.suffixSettled).crashNames, ∀ file, names (state.session.directory.file file) =
        (observe seen.suffixSettled).files.names (state.session.directory.file file))
    (consumeFrame : callbacks.setPending seed.pendingRef [] seen.suffixSettled = .ok () seen.consumed →
      (observe seen.suffixSettled).Frames (fun path => state.crashPath path ∨
        ∃ first ∈ retry.image.later.visible, path = directory.file (.walSegment first)) (observe seen.consumed))
    (keeperEffect : callbacks.sync seen.keeper seen.consumed = .ok () seen.reached →
      (view.handle seen.consumed seen.keeper).2.1 ∈ (view.descriptors seen.consumed).slots →
      (observe seen.consumed).files.names keeperPath = some keeperInode →
      RegularFileSyncEffect keeperInode [visible seen.consumed keeperInode] (observe seen.consumed) (observe seen.reached) ∧
      visible seen.reached keeperInode = visible seen.consumed keeperInode)
    (keeperBytes : visible seen.consumed keeperInode = layout.keeper.bytes)
    (apart : ∀ path, path = state.session.directory.file .walBoundary ∨ state.writeFramePath path →
      (observe seen.pruned).files.names path ≠ some keeperInode) :
    view.descriptors seen.reached = state.census ∧ NativeReadyStorage state (observe seen.reached) ∧
    (∀ inode, (observe seen.reached).files.names (state.session.directory.file (.walSegment state.writer.wal.active.first)) =
      some inode → visible seen.reached inode = state.writer.wal.active.bytes) ∧
    ∀ first ∈ retry.image.later.visible,
      (observe seen.reached).files.names (directory.file (.walSegment first)) = none ∧
      ∀ names ∈ (observe seen.reached).crashNames, names (directory.file (.walSegment first)) = none := by
  have ran := seen.returns later write rename
  have directoryLive : (view.handle seen.pruned seed.handle).2.1 ∈ (view.descriptors seen.pruned).slots := by
    rw [ran.directoryAtSuffix, ran.prunedCensus]
    have live := finish.repair.barrierCensus.2.2.2.2.2
    rw [finish.sameKeeper] at live
    rw [CapturedKeeperOpenReports.afterRead, DescriptorInventory.afterDrops_append]
    exact live
  have sameInodes : finish.census.inode = (view.descriptors seen.pruned).inode := by
    rw [ran.prunedCensus]
    simp only [CapturedPrunedAlignedFinish.census, CapturedKeeperOpenReports.afterRead, finish.sameKeeper]
    rfl
  have root := protectedFiles.directoryBound
  rw [sameDirectory, sameCensus, sameSlot, sameInodes] at root
  have bound : (observe seen.pruned).files.names directory.path = some
      ((view.descriptors seen.pruned).inode (view.handle seen.pruned seed.handle).2.1.description) := by
    rwa [ran.directoryAtSuffix]
  obtain ⟨childFrame, parentFrame, children⟩ := suffixEffect seen.suffixSync directoryLive bound
  have settledFrame := (consumeFrame seen.consume).weaken (fun _ inside => Or.inl inside)
  obtain ⟨selectedFrame, settled⟩ :=
    NativeReadyState.framesByDirectory sameDirectory parentFrame childFrame rootSettled children
  have toKeeperSync := selectedFrame.trans settledFrame.visible
  have keeperPathEq : state.session.directory.file (.walSegment state.writer.wal.active.first) = keeperPath := by
    rw [sameDirectory, sameFirst]
  have keeperSelected : state.crashPath keeperPath :=
    keeperPathEq ▸ (NativeReadyState.crashPath_iff_write.mpr (.inr (.inl rfl)))
  have namedAtIssue : (observe seen.consumed).files.names keeperPath = some keeperInode := by
    rw [(toKeeperSync _ keeperSelected).1, prunedBindings _ (.inl rfl), ran.keeperAtSync]
    exact ran.keeperBound
  obtain ⟨synced, live⟩ := keeperEffect seen.keeperSync (by rw [ran.keeperAtSync]; exact ran.keeperLive) namedAtIssue
  have activeBytes := keeperBytes.trans sameBytes.symm
  rw [activeBytes] at synced
  have initialKeeper : (observe seen.consumed).files.names
      (state.session.directory.file (.walSegment state.writer.wal.active.first)) = some keeperInode := by
    rwa [keeperPathEq]
  refine ⟨seen.reachedCensus.trans sameCensus.symm,
    NativeReadyStorage.afterAlignedBarriers selectedFrame settled settledFrame protectedFiles marker apart
      initialKeeper synced, ?_, ?_⟩
  · intro inode named
    rw [synced.names, initialKeeper] at named
    obtain rfl := Option.some.inj named
    exact live.trans activeBytes
  · intro first laterName
    let path := directory.file (.walSegment first)
    have absentAtPrune : (observe seen.pruned).files.names path = none :=
      (prunedBindings first (.inr laterName)).trans (ran.removed first laterName)
    have absentAtBarrier : (observe seen.suffixSettled).files.names path = none :=
      ((childFrame path ⟨.walSegment first, rfl⟩).1).trans absentAtPrune
    have laterFrame := (consumeFrame seen.consume).weaken
      (fun name (same : name = path) => .inr ⟨first, laterName, same⟩)
    refine ⟨(congrFun synced.names path).trans ((laterFrame.visible path rfl).1.trans absentAtBarrier), ?_⟩
    intro names allowed
    rw [synced.crashNames] at allowed
    have settled := laterFrame.settledFrom (by
      intro choice member name eq
      cases eq
      simpa only [sameDirectory] using children choice member (.walSegment first)) names allowed path rfl
    exact settled.trans ((laterFrame.visible path rfl).1.trans absentAtBarrier)

end Alvoki.Storage.DiskSession
