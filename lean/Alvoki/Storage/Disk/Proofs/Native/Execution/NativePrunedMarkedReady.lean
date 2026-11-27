import Alvoki.Storage.Disk.Proofs.Native.Execution.NativeAlignedMarkedReady
import Alvoki.Storage.Disk.Proofs.Keeper.NativePrunedKeeperStorage
import Alvoki.Storage.Disk.Proofs.Keeper.NativeMarkedKeeperLinks
import Alvoki.Storage.Disk.Proofs.Native.Open.NativeRetainedOpenStorage

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair CheckpointPublication

section

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write} {layout : CanonicalKeeperLayout retry.image history}
  {published : CheckpointPublication.Image} {checkpoint : Option (PackedTable × UInt64)}
  {admission : CensusOpenAdmissionReports input directory inventory retry}
  {vacant : TryLockObserves retry.owners directory (.ok true)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}
  {calls : CapturedAlignedCallbacks admission} {reads : CapturedMarkedReadReports admission layout published}
  {finish : CapturedPrunedAlignedFinish calls reads vacant selected} {heap : Type}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap} {cacheEntry entry : heap}
  {seed : OpenSyncCacheAllocations admission.opened view init cacheEntry} {callbacks : AlignedKeeperCacheCallbacks heap}
  {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)}

/-- The last file fsync uses the descriptor of the keeper actually opened
before pruning. Its issued slot still identifies that selected inode. -/
theorem PrunedAlignedKeeperCacheReport.keeperIssueInode
    (seen : PrunedAlignedKeeperCacheReport finish view init cacheEntry seed callbacks remove entry) :
    (view.descriptors seen.consumed).inode (view.handle seen.consumed seen.keeper).2.1.description =
      reads.wal.keeper.observesFile.object := by
  rw [seen.sameKeeper, seen.rawKeeper, seen.consumeFrame.2, seen.suffixCensus]
  have inodeMap : (finish.reader.afterRead.afterDrops finish.prune.afterAuthorization).inode =
      reads.wal.keeper.calls.inventory.inode := rfl
  rw [show ((finish.reader.afterRead.afterDrops finish.prune.afterAuthorization).afterDrops finish.repair.afterSuffix).inode =
    reads.wal.keeper.calls.inventory.inode from inodeMap]
  exact reads.wal.keeper.observesFile.sameObject

end

section

variable {heap stream : Type} {prior : NativeReadyState} {input : FilePath}
  {inventory : DescriptorInventory} {retry : LockedFileState FileImage}
  {vacant : TryLockObserves retry.owners prior.session.directory (.ok true)}
  {history : List WAL.Write} {layout : CanonicalKeeperLayout retry.image history}
  {selected : SelectedIntegrityCheckpoint prior.writer.published.durable
    retry.image.directory.active.manifest prior.writer.checkpoint}
  {opening : MarkedReadyOpenObservations input prior.session.directory inventory retry layout
    prior.writer.published vacant selected}
  {view : OpenCloseHeapView heap FileImage} {calls : RawOpenAdmissionCallbacks heap}
  {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}
  {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)} {stage : LongKeeperStageCallbacks heap}
  {rename : FilePath → FilePath → EStateM IO.Error heap Unit}

local notation "dir" => prior.session.directory

/-- Use the shared retained footprint and allocation proof after a
successful pruned repair. Only the accepted suffix unlinks, the
reused keeper slot, and the two final barriers are specific to this path. -/
theorem RawHealthyMarkedOpenEffects.SelectedReturn.readyAfterPrunedRepair
    {raw : RawHealthyMarkedOpenEffects opening view calls init entry phaseIdentity tokenIdentity
      allocatePhase allocateToken stream remove stage rename}
    {log : List DatabaseSubmissions} {reads : List RecordedSnapshotRead}
    {execute : (IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles) → EStateM.Result IO.Error heap DiskTable}
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    {ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool}
    (returned : raw.SelectedReturn log reads execute get set ptrEq)
    {finish : CapturedPrunedAlignedFinish opening.callbacks opening.reads vacant selected}
    (seen : PrunedAlignedKeeperCacheReport finish view init raw.raw.afterFlock raw.seed
      (raw.callbacks.withFileReads raw.fileCalls) remove raw.beforeKeeper)
    (pruned : (⟨opening.finish, raw.repaired, raw.keeper⟩ :
      Σ finish : CapturedKeeperFinish opening.callbacks opening.reads vacant selected, Σ reached : heap,
        NativeHealthyMarkedKeeperReport raw.seed raw.fileCalls raw.callbacks raw.beforeKeeper remove stage rename finish reached) =
      ⟨.prunedAligned finish, seen.reached, .prunedAligned seen⟩)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (priorReady : prior.Valid) (durable : prior.SelectedRetryDurability layout.target (observe entry))
    (kept : retry.image.kept = prior.writer.files.kept)
    (manifest : layout.target.pair.manifest = prior.writer.target.pair.manifest)
    (root : (observe entry).files.names (dir).path = some ((view.handle raw.seed.afterPending raw.seed.handle).1.inode
      (view.handle raw.seed.afterPending raw.seed.handle).2.1.description))
    (lock : (observe entry).files.names ((dir).file .lock) = some ((view.handle raw.raw.afterFlock raw.raw.lock).1.inode
      (view.handle raw.raw.afterFlock raw.raw.lock).2.1.description))
    (frames : (observe entry).Frames prior.selectedRetryPath (observe seen.pruned))
    (later : ∀ first ∈ retry.image.later.visible, layout.range.through < first) :
    let keeperPath := (dir).file (.walSegment layout.keeper.first)
    let object := opening.reads.wal.keeper.observesFile.object
    let inode := (view.descriptors seen.consumed).inode (view.handle seen.consumed seen.keeper).2.1.description
    let live (heap : heap) : CheckpointSurvivingFiles := ⟨(observe heap).files.names, fun inode => [visible heap inode]⟩
    (observe raw.beforeKeeper).files.names keeperPath = some object →
    visible raw.beforeKeeper object = layout.keeper.bytes ++ layout.tail →
    (live raw.beforeKeeper).Frames (· = keeperPath) (live seen.pruned) →
    (raw.callbacks.sync raw.seed.handle seen.pruned = .ok () seen.suffixSettled →
      (live seen.pruned).Frames (· = keeperPath) (live seen.suffixSettled)) →
    (raw.callbacks.setPending raw.seed.pendingRef [] seen.suffixSettled = .ok () seen.consumed →
      (live seen.suffixSettled).Frames (· = keeperPath) (live seen.consumed)) →
    (∀ {first start reached result}, first ∈ retry.image.later.visible →
      remove ((dir).file (.walSegment first)) start = .ok result reached → RunCollection.ownedUnlinkResult result = .ok () →
      (observe reached).files.names ((dir).file (.walSegment first)) = none ∧
      ∀ path, (path = (dir).path ∨ ∃ file, path = (dir).file file) →
        path ≠ (dir).file (.walSegment first) → (observe reached).files.names path = (observe start).files.names path) →
    (raw.callbacks.sync raw.seed.handle seen.pruned = .ok () seen.suffixSettled →
      (view.handle seen.pruned raw.seed.handle).2.1 ∈ (view.descriptors seen.pruned).slots →
      (observe seen.pruned).files.names (dir).path = some
        ((view.descriptors seen.pruned).inode (view.handle seen.pruned raw.seed.handle).2.1.description) →
      (observe seen.pruned).files.Frames (fun path => ∃ file, path = (dir).file file) (observe seen.suffixSettled).files ∧
      (observe seen.pruned).Frames (· = (dir).path) (observe seen.suffixSettled) ∧
      ∀ names ∈ (observe seen.suffixSettled).crashNames, ∀ file,
        names ((dir).file file) = (observe seen.suffixSettled).files.names ((dir).file file)) →
    (∀ next : NativeReadyState, next.session.directory = dir →
      raw.callbacks.setPending raw.seed.pendingRef [] seen.suffixSettled = .ok () seen.consumed →
      (observe seen.suffixSettled).Frames (fun path => next.crashPath path ∨
        ∃ first ∈ retry.image.later.visible, path = (dir).file (.walSegment first)) (observe seen.consumed)) →
    (raw.callbacks.sync seen.keeper seen.consumed = .ok () seen.reached →
      (view.handle seen.consumed seen.keeper).2.1 ∈ (view.descriptors seen.consumed).slots →
      (observe seen.consumed).files.names keeperPath = some inode →
      RegularFileSyncEffect inode [visible seen.consumed inode] (observe seen.consumed) (observe seen.reached) ∧
      visible seen.reached inode = visible seen.consumed inode) →
    RunOpenLinkCensus (path := keeperPath) (before := raw.listing.reached)
      raw.fileCalls.stat (observe raw.listing.reached).files.names object →
    (observe raw.listing.reached).files.Frames
      (fun path => path = (dir).path ∨ ∃ file, path = (dir).file file) (observe seen.authorized).files →
    (∀ (state : NativeReadyState) ref reached,
      allocatePhase (.ready state.writer.installed) raw.repaired = .ok ref reached →
      (observe raw.repaired).Frames state.crashPath (observe reached) ∧ visible reached = visible raw.repaired) →
    (∀ (state : NativeReadyState) before ref reached,
      allocateToken () before = .ok ref reached →
      (observe before).Frames state.crashPath (observe reached) ∧ visible reached = visible before) →
    raw.ReadyWriterReturn log reads execute get set observe visible := by
  intro keeperPath object inode live named payload readKeeper suffixLive consumeLive unlinked suffixEffect consumeEffect
    keeperEffect links privateFrame phaseFrames tokenFrames
  have prunedFinish : opening.finish = .prunedAligned finish := congrArg Sigma.fst pruned
  have repairHeap : raw.repaired = seen.reached := congrArg (fun route => route.2.1) pruned
  have sameObjects : opening.finish.census.inode = opening.admission.reached.inode := by
    simpa only [prunedFinish, CapturedKeeperFinish.census] using finish.sameCensusObjects
  have keeperPruned : (observe seen.pruned).files.names keeperPath = some object :=
    (readKeeper keeperPath rfl).1.trans named
  have keeperFrames := readKeeper.trans ((suffixLive seen.suffixSync).trans (consumeLive seen.consume))
  have keptBytes := (List.cons.inj ((keeperFrames keeperPath rfl).2 object named)).1
  have issued : inode = object := seen.keeperIssueInode
  have aligned := finish.repair.aligned
  rw [finish.sameKeeper] at aligned
  have measured := aligned.trans opening.reads.wal.keeper.observesFile.extent
  rw [ByteArray.size_append] at measured
  have empty : layout.tail = ByteArray.empty := ByteArray.size_eq_zero_iff.mp (by omega)
  have keeperBytes : visible seen.consumed inode = layout.keeper.bytes := by
    rw [issued, keptBytes, payload, empty, ByteArray.append_empty]
  let write := stage.stage raw.seed.pendingRef raw.callbacks.modifyPending
  let sync := raw.callbacks.syncPaths (dir).path raw.seed.directoryRef raw.seed.activeRef raw.seed.pendingRef
  have unlinkPass := (seen.unlinks.returns opening.admission.held seen.authorizedFiles layout.boundedPlan write sync rename).1
  have actualUnlinks := namesOfReturnedWalUnlinks (dir) layout.boundedPlan remove write sync rename
    (fun heap => (observe heap).files.names) (fun path => path = (dir).path ∨ ∃ file, path = (dir).file file)
    (fun first _ => .inr ⟨.walSegment first, rfl⟩) unlinked unlinkPass
  have ran := seen.returns later write rename
  have modelKeeper : finish.prune.reached keeperPath = some object := by
    rw [← issued]
    change finish.prune.reached keeperPath =
      some ((view.descriptors seen.consumed).inode (view.handle seen.consumed seen.keeper).2.1.description)
    rw [ran.keeperAtSync]
    exact ran.keeperBound
  have bindings (first : Nat) (kept : first = layout.keeper.first ∨ first ∈ retry.image.later.visible) :
      (observe seen.pruned).files.names ((dir).file (.walSegment first)) =
        finish.prune.reached ((dir).file (.walSegment first)) := by
    rcases kept with rfl | listed
    · exact keeperPruned.trans modelKeeper.symm
    · exact (actualUnlinks.1 first listed).trans (ran.removed first listed).symm
  have keeperPrivate := raw.keeperPrivateBinding (names := fun heap => (observe heap).files.names) links
  refine returned.readyAfterRepair observe visible sameObjects ?_ phaseFrames tokenFrames
  intro next directory modeledCensus owner slot target retained published first bytes
  have valid := next.readPrefix.refines.1
  have census : next.state.census = finish.census := by
    simpa only [prunedFinish, CapturedKeeperFinish.census] using modeledCensus
  obtain ⟨protectedFiles, marker, parent⟩ :=
    raw.reopenedFootprintAt observe durable frames.visible (frames.weaken fun _ same => .inr (.inl same))
      root lock sameObjects priorReady valid directory modeledCensus owner slot target manifest published (retained.trans kept)
  have apart : ∀ path, next.state.selectedRetryPath path → (observe seen.pruned).files.names path ≠ some inode := by
    intro path selectedPath bound
    have child := NativeReadyState.crashPath_rootOrChild
      (NativeReadyState.crashPath_iff_write.mpr (selectedPath.imp id Or.inr))
    rw [directory] at child
    have apartFromSuffix (firstLater) (listed : firstLater ∈ retry.image.later.visible) :
        path ≠ (dir).file (.walSegment firstLater) := by
      rw [← directory]
      apply NativeReadyState.protectedPathNeWalFromActive valid selectedPath
      rw [first]
      exact Nat.le_trans layout.target.firstCovered (Nat.le_of_lt (later firstLater listed))
    have nameAfterAuthorization := (actualUnlinks.2 path child apartFromSuffix).symm.trans bound
    have canonical := privateFrame.privateBindingOn keeperPrivate path child
      (nameAfterAuthorization.trans (congrArg some issued))
    exact NativeReadyState.protectedPathNeWalFromActive valid selectedPath (Nat.le_refl _)
      (by rw [directory, first]; exact canonical)
  obtain ⟨_, repairReady, repairKeeper, _⟩ := seen.readyStorage later write rename observe visible
    directory census slot first bytes protectedFiles marker parent bindings
    (fun done live root => by simpa only [directory] using suffixEffect done live root)
    (consumeEffect next.state directory) keeperEffect keeperBytes apart
  exact ⟨repairHeap.symm ▸ repairReady, repairHeap.symm ▸ repairKeeper⟩

end
end Alvoki.Storage.DiskSession
