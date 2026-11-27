import Alvoki.Storage.Disk.NativeAlignedMarkedReady
import Alvoki.Storage.Disk.Proofs.Keeper.NativeLongKeeperStorage

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

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

/-- Follow the selected longer-keeper repair through its successful
replacement. The staged inode is the one written, synced, renamed,
and then observed at the actual returned writer's keeper path. -/
theorem RawHealthyMarkedOpenEffects.SelectedReturn.readyAfterLongerRetry
    {raw : RawHealthyMarkedOpenEffects opening view calls init entry phaseIdentity tokenIdentity
      allocatePhase allocateToken stream remove stage rename}
    {log : List DatabaseSubmissions} {reads : List RecordedSnapshotRead}
    {execute : (IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles) → EStateM.Result IO.Error heap DiskTable}
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    {ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool}
    (returned : raw.SelectedReturn log reads execute get set ptrEq)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    {finish : CapturedLongKeeperFinish opening.callbacks opening.reads vacant selected}
    {read : NativeLongKeeperReadHeap finish raw.seed raw.fileCalls raw.beforeKeeper}
    {authorization : NativeLongKeeperAuthorizationHeap read (raw.callbacks.withFileReads raw.fileCalls)}
    {suffix : NativeLongKeeperSuffixHeap authorization remove}
    {staged : NativeLongKeeperFreshStageHeap suffix stage}
    {synced : NativeLongKeeperStagedSyncHeap staged (fun heap => (observe heap).files.names)}
    {renamed : NativeLongKeeperRenameHeap synced rename}
    (seen : NativeLongKeeperSettlementHeap renamed)
    (longer : (⟨opening.finish, raw.repaired, raw.keeper⟩ :
      Σ finish : CapturedKeeperFinish opening.callbacks opening.reads vacant selected, Σ reached : heap,
        NativeHealthyMarkedKeeperReport raw.seed raw.fileCalls raw.callbacks raw.beforeKeeper remove stage rename finish reached) =
      ⟨.longer finish, seen.reached, .longer seen⟩)
    (priorReady : prior.Valid) (durable : prior.SelectedRetryDurability layout.target (observe entry))
    (kept : retry.image.kept = prior.writer.files.kept)
    (manifest : layout.target.pair.manifest = prior.writer.target.pair.manifest)
    (root : (observe entry).files.names (dir).path = some ((view.handle raw.seed.afterPending raw.seed.handle).1.inode
      (view.handle raw.seed.afterPending raw.seed.handle).2.1.description))
    (lock : (observe entry).files.names ((dir).file .lock) = some ((view.handle raw.raw.afterFlock raw.raw.lock).1.inode
      (view.handle raw.raw.afterFlock raw.raw.lock).2.1.description))
    (filesFrame : (observe entry).files.Frames prior.selectedRetryPath (observe renamed.reached).files)
    (parentFrame : (observe entry).Frames (· = (dir).path) (observe renamed.reached)) :
    let replacement := finish.stage.inventory.inode finish.stage.slot.description
    (stage.acquire ((dir).file .stagedWal) suffix.reached = .ok staged.descriptor staged.created →
      stage.write staged.descriptor layout.keeper.bytes staged.created = .ok () staged.written →
      stage.flush staged.descriptor staged.written = .ok () staged.flushed →
      visible staged.flushed ((view.handle staged.flushed staged.descriptor).1.inode
        (view.handle staged.flushed staged.descriptor).2.1.description) = layout.keeper.bytes) →
    (raw.callbacks.modifyPending raw.seed.pendingRef (pushPending ((dir).file .stagedWal) staged.descriptor)
      staged.flushed = .ok () staged.recorded → visible staged.recorded replacement = visible staged.flushed replacement) →
    (raw.callbacks.setPending raw.seed.pendingRef [] staged.recorded = .ok () synced.consumed →
      visible synced.consumed replacement = visible staged.recorded replacement) →
    (raw.callbacks.sync staged.descriptor synced.consumed = .ok () synced.reached →
      (view.handle synced.consumed staged.descriptor).2.1 ∈ (view.descriptors synced.consumed).slots →
      (observe synced.consumed).files.names ((dir).file .stagedWal) = some replacement →
      RegularFileSyncEffect ((view.handle synced.consumed staged.descriptor).1.inode
        (view.handle synced.consumed staged.descriptor).2.1.description)
        [visible synced.consumed replacement] (observe synced.consumed) (observe synced.reached) ∧
      visible synced.reached replacement = visible synced.consumed replacement) →
    (rename ((dir).file .stagedWal) ((dir).file (.walSegment layout.keeper.first))
      synced.reached = .ok () renamed.reached →
      (observe synced.reached).files.names ((dir).file .stagedWal) = some replacement →
      (observe renamed.reached).files.bytes replacement = (observe synced.reached).files.bytes replacement ∧
      visible renamed.reached replacement = visible synced.reached replacement) →
    (raw.callbacks.sync raw.seed.handle renamed.reached = .ok () seen.reached →
      (view.handle renamed.reached raw.seed.handle).2.1 ∈ (view.descriptors renamed.reached).slots →
      (observe renamed.reached).files.names (dir).path = some
        ((view.handle renamed.reached raw.seed.handle).1.inode (view.handle renamed.reached raw.seed.handle).2.1.description) →
      WalRootSyncEffect dir true (observe renamed.reached) (observe seen.reached) ∧
      (observe renamed.reached).Frames (· = (dir).path) (observe seen.reached) ∧
      visible seen.reached replacement = visible renamed.reached replacement) →
    (∀ (state : NativeReadyState) ref reached,
      allocatePhase (.ready state.writer.installed) raw.repaired = .ok ref reached →
      (observe raw.repaired).Frames state.crashPath (observe reached) ∧ visible reached = visible raw.repaired) →
    (∀ (state : NativeReadyState) before ref reached,
      allocateToken () before = .ok ref reached →
      (observe before).Frames state.crashPath (observe reached) ∧ visible reached = visible before) →
    raw.ReadyWriterReturn log reads execute get set observe visible := by
  intro replacement written recorded consumed stageSync renameEffect directoryEffect phaseFrames tokenFrames
  have flushed := written staged.acquired staged.wrote staged.flush
  rw [staged.captured] at flushed
  have stageLive : visible synced.consumed replacement = layout.keeper.bytes :=
    (consumed synced.cleared).trans ((recorded staged.record).trans flushed)
  have namedAtIssue := synced.syncs.2.2.2.1
  rw [synced.consumeCensus, staged.atSync] at namedAtIssue
  have longerFinish : opening.finish = .longer finish := congrArg Sigma.fst longer
  have repairHeap : raw.repaired = seen.reached := congrArg (fun route => route.2.1) longer
  have sameObjects : opening.finish.census.inode = opening.admission.reached.inode := by
    simpa only [longerFinish, CapturedKeeperFinish.census] using finish.sameCensusObjects
  refine returned.readyAfterRepair observe visible sameObjects ?_ phaseFrames tokenFrames
  intro next directory modeledCensus owner slot target retained published first bytes
  have census : next.state.census = finish.census := by
    simpa only [longerFinish, CapturedKeeperFinish.census] using modeledCensus
  obtain ⟨protectedFiles, marker, parent⟩ := raw.reopenedFootprintAt observe durable filesFrame parentFrame
    root lock sameObjects priorReady next.readPrefix.refines.1 directory modeledCensus owner slot target manifest
    published (retained.trans kept)
  obtain ⟨_, ready, keeper⟩ := seen.readyStorage directory census slot first bytes protectedFiles marker parent stageLive
    (fun synced live => stageSync synced live namedAtIssue) renameEffect
    (fun synced live root => by simpa only [directory] using directoryEffect synced live root)
  exact ⟨repairHeap.symm ▸ ready, repairHeap.symm ▸ keeper⟩

end Alvoki.Storage.DiskSession
