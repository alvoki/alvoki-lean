import Alvoki.Storage.Disk.NativeReadyReadPrefix
import Alvoki.Storage.Disk.WalCollectionCompletePlan

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

private abbrev CollectionFiles := CensusDirectoryCache × WalSealedUnlinkImage

private def removeWithCache
    (remove : FilePath → EStateM IO.Error WalSealedUnlinkImage (Except IO.Error Unit))
    (path : FilePath) : EStateM IO.Error CollectionFiles (Except IO.Error Unit) :=
  fun (cache, files) => withCache cache (remove path files)

/-- The reported ordered unlink prefix uses no synchronization handle.
Thread the writer's original cache to the same reached directory barrier. -/
private theorem WalUnlinkPrefix.carriesCache
    {directory : DiskDirectory} {root : DeviceInode}
    {remove : FilePath → EStateM IO.Error WalSealedUnlinkImage (Except IO.Error Unit)}
    {offsets pending removed : List Nat} {failure : Option IO.Error}
    {view afterView : DirectoryReadNamespace} {before after : WalSealedUnlinkImage}
    (unlinked : WalUnlinkPrefix directory root remove offsets view before pending failure afterView after removed)
    (success : failure = none) (sync : FilePath → EStateM IO.Error CollectionFiles Unit)
    (installed : Installed) (cache : CensusDirectoryCache) (owners : LockOwners) :
    WalCollectionReads.continueWithEffects directory (removeWithCache remove) sync installed offsets
      (.poisoned, ⟨(cache, before), owners⟩) =
    WalCollectionReads.continueWithEffects directory (removeWithCache remove) sync installed pending
      (.poisoned, ⟨(cache, after), owners⟩) := by
  induction unlinked with
  | pause => rfl
  | next call _ accepted _ ih =>
    have issued := congrArg (withCache cache) call
    rw [WalCollectionReads.continueWithEffects_unlink _ _ _ _ _ (by exact issued), accepted]
    exact ih success
  | failed | failedWithoutEffect => contradiction

private theorem WalUnlinkPrefix.keepsOtherChild
    {directory : DiskDirectory} {root : DeviceInode} {remove}
    {offsets pending removed : List Nat} {failure : Option IO.Error}
    {view afterView : DirectoryReadNamespace} {before after : WalSealedUnlinkImage}
    (unlinked : WalUnlinkPrefix directory root remove offsets view before pending failure afterView after removed)
    {name : String} (different : ∀ offset ∈ offsets, name ≠ renderWalSegmentName offset) :
    afterView.child root name = view.child root name := by
  induction unlinked with
  | pause | failedWithoutEffect => rfl
  | next _ effect _ _ ih =>
    exact (ih (fun offset member => different offset (List.mem_cons_of_mem _ member))).trans
      (effect.frame name (different _ List.mem_cons_self))
  | failed _ effect _ => exact effect.frame name (different _ List.mem_cons_self)

/-- A complete covered-WAL collection from this exact ready state.
Temporary planner reads and directory enumeration can open descriptors,
which are released by the time the checked listing has returned. The
drop reports frame the existing slots throughout this observed pass. -/
structure NativeReadyWalCollection (state : NativeReadyState) where
  calls : WalCollectionReads
  inventory : WalCollectionInventoryReport calls state.session.directory state.session.descriptor state.writer.wal
  startsAt : inventory.descriptors = state.census
  ownersMatch : inventory.owner = state.owner
  directoryMatches : inventory.lifetime.directorySlot = state.directorySlot
  manifest : calls.paths.readOptional (state.session.directory.file .manifest) = .ok state.writer.target.pair.manifest
  marker : calls.paths.readOptional (state.session.directory.file .walBoundary) = .ok state.writer.target.pair.walBoundary
  remove : FilePath → EStateM IO.Error WalSealedUnlinkImage (Except IO.Error Unit)
  reachedView : DirectoryReadNamespace
  atBarrier : WalSealedUnlinkImage
  removed : List Nat
  unlinked : WalUnlinkPrefix state.session.directory inventory.lifetime.root remove state.writer.wal.collectionOffsets
    inventory.lifetime.namespaceView (.start state.writer.wal) [] none reachedView atBarrier removed
  barrier : WalCollectionDirectoryFsync state.session.directory inventory.lifetime.root inventory.lifetime.namespaceView
    reachedView state.session.descriptor atBarrier
  originalCache : barrier.cache = state.cache
  sameWriter : barrier.writerSlot = state.owner
  completed : barrier.outcome = .completed
  barrierEntry : barrier.inventory = inventory.listing.afterClose
  reachedObjects : reachedView.modelObject = inventory.lifetime.namespaceView.modelObject
  afterBarrier : List LockReferenceDrop
  keepsSlots : ∀ slot ∈ state.census.slots,
    ∀ event ∈ inventory.lifetime.drops ++ barrier.drops ++ afterBarrier, event.removes slot.reference = false

namespace NativeReadyWalCollection

variable {state : NativeReadyState}

theorem reachesBarrier (reported : NativeReadyWalCollection state) :
    reported.barrier.reached = reported.inventory.listing.afterClose.afterDrops reported.barrier.drops :=
  congrArg (fun inventory => inventory.afterDrops reported.barrier.drops) reported.barrierEntry

def census (reported : NativeReadyWalCollection state) : DescriptorInventory :=
  reported.barrier.reached.afterDrops reported.afterBarrier

theorem censusPreserved (reported : NativeReadyWalCollection state) : reported.census = state.census := by
  let drops := reported.inventory.lifetime.drops ++ reported.barrier.drops ++ reported.afterBarrier
  have previous : reported.census = reported.inventory.descriptors.afterDrops drops := by
    simp only [census, reported.reachesBarrier, reported.inventory.listing.afterClose_eq,
      DescriptorInventory.afterDrops_append, drops]
  refine previous.trans ((congrArg (fun census => census.afterDrops drops) reported.startsAt).trans ?_)
  cases reached : state.census with
  | mk slots distinct inode =>
    simp only [DescriptorInventory.afterDrops, DescriptorInventory.mk.injEq, and_true]
    apply List.filter_eq_self.mpr
    intro slot member
    apply List.all_eq_true.mpr
    intro event seen
    have present : slot ∈ state.census.slots := by simpa only [reached] using member
    simp [reported.keepsSlots slot present event seen]

/-- Run the original planner and shared publication schedule at the
reached phase, using the original cache for the final grouped sync. -/
def run (reported : NativeReadyWalCollection state) :
    EStateM.Result IO.Error (Phase Installed × LockedFileState CollectionFiles) Unit :=
  reported.calls.collectWithEffects state.session.directory (removeWithCache reported.remove)
    reported.barrier.group (state.session.phase, ⟨(state.cache, .start state.writer.wal), state.files.owners⟩)

/-- The session cells and cache stay in place. Only the physical
projection of its covered seals changes. -/
def next (reported : NativeReadyWalCollection state) : NativeReadyState :=
  { state with writer := state.writer.afterWalCollection reported.barrier.after, census := reported.census }

theorem runs (reported : NativeReadyWalCollection state) (valid : state.Valid) :
    reported.run = .ok () (reported.next.session.phase,
      ⟨(reported.next.cache, reported.barrier.after), reported.next.files.owners⟩) := by
  have plan := valid.retained.completeObservedWalPlan reported.calls reported.inventory reported.manifest reported.marker
  have group := reported.barrier.groupReturns
  rw [reported.completed, reported.originalCache] at group
  rw [run, valid.phase, WalCollectionReads.collectWithEffects_plan _ _ _ _ _ _ plan,
    reported.unlinked.carriesCache rfl _ _ _ _, WalCollectionReads.continueWithEffects_barrier, group]
  simp [next, NativeReadyState.files, SegmentedWriterState.afterWalCollection, valid.phase]

/-- The final fsync uses the exact cached description for the root.
The writer and directory slots are live in the reached returned census. -/
theorem retainsCustody (reported : NativeReadyWalCollection state) (valid : state.Valid) :
    reported.barrier.handle.2.1 = state.directorySlot ∧
      reported.barrier.handle.1.inode state.directorySlot.description = state.census.inode state.directorySlot.description ∧
      state.owner ∈ reported.next.census.slots ∧ state.directorySlot ∈ reported.next.census.slots := by
  obtain ⟨capture, cached⟩ := valid.captured
  have cache := (congrArg Cache.directory reported.originalCache).trans cached
  have same := Option.some.inj (reported.barrier.captured.symm.trans cache)
  have slot := congrArg (fun handle : WalCollectionDirectoryHandle => handle.2.1) same
  let entry := reported.inventory.lifetime.directorySlot
  have object := reported.inventory.lifetime.identifiesDirectory.trans
    (congrArg (fun census => census.inode entry.description) reported.startsAt)
  change _ = state.census.inode reported.inventory.lifetime.directorySlot.description at object
  rw [reported.directoryMatches] at object
  refine ⟨slot, ?_, ?_, ?_⟩
  · exact (congrArg (fun own : DescriptorSlot => reported.barrier.handle.1.inode own.description) slot.symm).trans
      (reported.barrier.captureInode.symm.trans object)
  · simpa only [next, reported.censusPreserved] using valid.ownerLive
  · simpa only [next, reported.censusPreserved] using valid.directoryLive

/-- The complete listing and ensuing unlinks use the held writer's root.
Every unlink preserves the lock binding read under the original owner. -/
theorem retainsLock (reported : NativeReadyWalCollection state) :
    reported.barrier.writerSlot = state.owner ∧
    reported.reachedView.child reported.inventory.lifetime.root "LOCK" = some reported.inventory.lifetime.lock ∧
    reported.reachedView.modelObject reported.inventory.lifetime.lock =
      reported.barrier.reached.inode state.owner.description := by
  have directoryLock : ∀ offset ∈ state.writer.wal.collectionOffsets, "LOCK" ≠ renderWalSegmentName offset := by
    intro offset _ same
    have lengths := congrArg String.length same
    simp only [renderWalSegmentName, String.length_append] at lengths
    have lockLength : "LOCK".length = 4 := by decide
    have walPrefixLength : "WAL-segment-".length = 12 := by decide
    omega
  let owner := reported.inventory.owner
  have object := reported.inventory.lifetime.identifiesLock.trans
    (congrArg (fun census => census.inode owner.description) reported.startsAt)
  refine ⟨reported.sameWriter, (reported.unlinked.keepsOtherChild directoryLock).trans
    reported.inventory.lifetime.lockEntry, ?_⟩
  calc
    reported.reachedView.modelObject reported.inventory.lifetime.lock =
        reported.inventory.lifetime.namespaceView.modelObject reported.inventory.lifetime.lock :=
      congrFun reported.reachedObjects _
    _ = state.census.inode state.owner.description :=
      object.trans (congrArg (fun slot : DescriptorSlot => state.census.inode slot.description) reported.ownersMatch)
    _ = reported.inventory.descriptors.inode state.owner.description :=
      congrArg (fun inventory => inventory.inode state.owner.description) reported.startsAt.symm
    _ = reported.barrier.reached.inode state.owner.description := by
      have listing := reported.inventory.listing.afterClose_eq
      exact (congrArg (fun inventory => inventory.inode state.owner.description)
        (reported.reachesBarrier.trans (congrArg (fun inventory => inventory.afterDrops reported.barrier.drops) listing))).symm

end NativeReadyWalCollection

/-- A complete native collection after the reached read prefix keeps
the same ready phase, installed table, checkpoint, cache and ledger.
The reported barrier durably removes every seal covered by the plan. -/
theorem NativeReadyReadPrefix.collectsCoveredWal
    {opened : EStateM.Result IO.Error CensusOpenState SegmentedSession}
    {initial state : NativeReadyState} {history : List WAL.Write}
    {log : List DatabaseSubmissions} {reads : List RecordedSnapshotRead}
    (prior : NativeReadyReadPrefix opened initial history log reads state)
    (reported : NativeReadyWalCollection state) :
    reported.run = .ok () (reported.next.session.phase,
      ⟨(reported.next.cache, reported.barrier.after), reported.next.files.owners⟩) ∧
    reported.next.Valid ∧
    reported.next.session = state.session ∧ reported.next.cache = state.cache ∧ reported.next.census = state.census ∧
    reported.next.writer.installed = state.writer.installed ∧
    reported.next.writer.checkpoint = state.writer.checkpoint ∧
    reported.next.writer.wal.active = state.writer.wal.active ∧
    reported.next.writer.wal.readDescriptors state.writer.target.range.watermark =
      state.writer.wal.readDescriptors state.writer.target.range.watermark ∧
    reported.next.writer.history = history ∧
    reported.barrier.writerSlot = state.owner ∧
    reported.reachedView.child reported.inventory.lifetime.root "LOCK" = some reported.inventory.lifetime.lock ∧
    reported.barrier.handle.2.1 = state.directorySlot ∧
    reported.barrier.handle.1.inode state.directorySlot.description = state.census.inode state.directorySlot.description ∧
    reported.barrier.reached = reported.inventory.listing.afterClose.afterDrops reported.barrier.drops ∧
    state.directorySlot ∈ reported.barrier.reached.slots ∧ state.owner ∈ reported.barrier.reached.slots ∧
    reported.reachedView.modelObject reported.inventory.lifetime.lock = reported.barrier.reached.inode state.owner.description ∧
    reported.barrier.after.crashSealed = [reported.next.writer.wal.sealed] ∧
    (∀ offset ∈ state.writer.wal.collectionOffsets,
      reported.reachedView.child reported.inventory.lifetime.root (renderWalSegmentName offset) = none) ∧
    (∀ segment ∈ state.writer.wal.sealed, state.writer.wal.Eligible segment →
      segment ∉ reported.next.writer.wal.sealed) ∧
    InstalledClientReplay log reads history reported.next.writer.installed reported.next.session := by
  obtain ⟨valid, sameHistory, _⟩ := prior.refines
  have ready := valid.retained
  have plan := ready.completeObservedWalPlan reported.calls reported.inventory reported.manifest reported.marker
  have bound (segment : WalSegment) (stored : segment ∈ state.writer.wal.sealed) :
      (reported.inventory.lifetime.namespaceView.child reported.inventory.lifetime.root
        (renderWalSegmentName segment.first)).isSome = true := by
    rw [reported.inventory.bound segment (List.mem_append_left _ stored)]
    rfl
  obtain ⟨_, _, retries, settled, readyAfter, _⟩ := ready.reportedWalCollectionBarrier reported.calls plan
    (fun _ member => member) bound reported.remove reported.unlinked reported.barrier
  have after := readyAfter reported.completed
  have effective : reported.barrier.outcome.effective = true := by rw [reported.completed]; rfl
  obtain ⟨names, absent⟩ := settled effective
  have crash : reported.barrier.after.crashSealed = [reported.barrier.after.visible.sealed] :=
    names.trans (congrArg (fun sealed => [sealed]) reported.barrier.effect.sealed.symm)
  have retry := retries _ (crash.symm ▸ List.mem_singleton_self _)
  have selected : reported.barrier.after.visible.Selects state.writer.target.pair :=
    List.mem_cons.mpr (.inl after.walPair.symm)
  have stillReads := retry.keepsReadDescriptors selected state.writer.target.decoded
  obtain ⟨directory, object, ownerLive, directoryLive⟩ := reported.retainsCustody valid
  obtain ⟨owner, lock, lockObject⟩ := reported.retainsLock
  have directoryAtIssue := directory ▸ reported.barrier.directoryLive
  have ownerAtIssue := owner ▸ reported.barrier.writerLive
  have nextValid : reported.next.Valid :=
    ⟨valid.phase, valid.owner, ownerLive, directoryLive, valid.captured, after⟩
  refine ⟨reported.runs valid, nextValid, rfl, rfl, reported.censusPreserved, rfl, rfl, retry.keepsActive,
    stillReads, sameHistory, owner, lock, directory, object, reported.reachesBarrier, directoryAtIssue, ownerAtIssue,
    lockObject, crash, reported.unlinked.completedNamesAbsent rfl rfl, ?_,
    prior.guardedReplay⟩
  intro segment stored eligible present
  have offset : segment.first ∈ state.writer.wal.collectionOffsets := List.mem_map.mpr
    ⟨segment, List.mem_filter.mpr ⟨stored, WalSegmentImage.canRemove_iff.mpr eligible⟩, rfl⟩
  exact absent segment.first offset _ (crash.symm ▸ List.mem_singleton_self _) segment present rfl

end Alvoki.Storage.DiskSession
