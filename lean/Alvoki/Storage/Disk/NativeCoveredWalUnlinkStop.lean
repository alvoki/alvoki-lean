import Alvoki.Storage.Disk.Proofs.Collection.NativeReadyWalCollection

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

namespace WalCollectionInterruption

abbrev UnlinkFiles := DescriptorInventory × WalSealedUnlinkImage
abbrev CollectionState := Phase Installed × LockedFileState (CensusDirectoryCache × UnlinkFiles)
abbrev CollectionM := ExceptT IO.Error (EStateM FilePath CollectionState)

def atFiles (state : NativeReadyState) (inventory : DescriptorInventory) (image : WalSealedUnlinkImage) : CollectionState :=
  (.poisoned, ⟨(state.cache, inventory, image), state.files.owners⟩)

private def setPhase (phase : Phase Installed) : CollectionM Unit :=
  ExceptT.mk fun (_, files) => .ok (.ok ()) (phase, files)

def unlink (remove : FilePath → EStateM FilePath UnlinkFiles (Except IO.Error Unit)) (path : FilePath) :
    CollectionM (Except IO.Error Unit) :=
  ExceptT.mk fun (phase, files) =>
    match remove path files.image.2 with
    | .ok value reached => .ok (.ok value) (phase, ⟨(files.image.1, reached), files.owners⟩)
    | .error atPath reached => .error atPath (phase, ⟨(files.image.1, reached), files.owners⟩)

def perform (directory : DiskDirectory) (remove : FilePath → EStateM FilePath UnlinkFiles (Except IO.Error Unit))
    (barrier : FilePath → CollectionM Unit) : RunCollection.Step Nat → CollectionM Unit :=
  RunCollection.performPaths (unlink remove) barrier throw (fun first => directory.file (.walSegment first)) directory.path

/-- Lift the exact ordered sequence of returned unlinks into the outer
interruption model without changing their reached census or visibility. -/
theorem runsCompleted (state : NativeReadyState) (inventory : DescriptorInventory)
    (rawRemove : FilePath → EStateM FilePath UnlinkFiles (Except IO.Error Unit)) (barrier : FilePath → CollectionM Unit)
    {removeFile : FilePath → EStateM IO.Error WalSealedUnlinkImage (Except IO.Error Unit)}
    (returned : ∀ path before result after, removeFile path before = .ok result after →
      rawRemove path (inventory, before) = .ok result (inventory, after))
    {root : DeviceInode} {offsets pending removed : List Nat} {view afterView : DirectoryReadNamespace}
    {before after : WalSealedUnlinkImage} {failure : Option IO.Error}
    (completed : WalUnlinkPrefix state.session.directory root removeFile offsets view
      before pending failure afterView after removed) (success : failure = none) :
    (RunCollection.run offsets (perform state.session.directory rawRemove barrier)).run (atFiles state inventory before) =
      (RunCollection.run pending (perform state.session.directory rawRemove barrier)).run (atFiles state inventory after) := by
  induction completed with
  | pause => rfl
  | next call _ accepted _ ih =>
    have raw := returned _ _ _ _ call
    simpa only [RunCollection.run, RunCollection.steps, List.map_cons, List.cons_append, List.forM_eq_forM,
      List.forM_cons, perform, RunCollection.performPaths, unlink, atFiles, Bind.bind, ExceptT.bind,
      ExceptT.bindCont, ExceptT.mk, ExceptT.run, EStateM.bind, Pure.pure, ExceptT.pure, EStateM.pure, raw,
      accepted] using ih success
  | failed | failedWithoutEffect => contradiction

/-- The checked plan and publication phase of the actual collector,
viewed with a separate channel for a callback that has not returned. -/
def run (state : NativeReadyState) (calls : WalCollectionReads) (inventory : DescriptorInventory)
    (action : RunCollection.Step Nat → CollectionM Unit) : EStateM.Result FilePath CollectionState (Except IO.Error Unit) :=
  (do
    let installed ← state.session.phase.installed
    let selected ← (ExceptT.mk (fun (phase, files) => .ok (calls.plan state.session.directory installed)
      (phase, ⟨(files.image.1, inventory, files.image.2.2), files.owners⟩)) : CollectionM (List Nat))
    publishPrepared setPhase (RunCollection.run selected action) (setPhase (.ready installed))).run
    (state.session.phase, ⟨(state.cache, state.census, .start state.writer.wal), state.files.owners⟩)

theorem stopsFromReady (state : NativeReadyState) (calls : WalCollectionReads) (inventory : DescriptorInventory)
    (action : RunCollection.Step Nat → CollectionM Unit) (valid : state.Valid)
    (planned : calls.plan state.session.directory state.writer.installed = .ok state.writer.wal.collectionOffsets)
    {path : FilePath} {after : CollectionState}
    (stopped : (RunCollection.run state.writer.wal.collectionOffsets action).run
      (atFiles state inventory (.start state.writer.wal)) = .error path after) :
    run state calls inventory action = .error path after := by
  change RunCollection.run state.writer.wal.collectionOffsets action (atFiles state inventory (.start state.writer.wal)) = _ at stopped
  unfold atFiles at stopped
  simp [run, valid.phase, Phase.installed, planned, publishPrepared, setPhase, Bind.bind, ExceptT.bind,
    ExceptT.bindCont, ExceptT.mk, ExceptT.run, EStateM.bind, Pure.pure, ExceptT.pure, EStateM.pure, stopped]

end WalCollectionInterruption

open WalCollectionInterruption (UnlinkFiles CollectionState CollectionM)

/-- An issued covered WAL unlink stops before returning after any
completed prefix. Earlier returns and the stop use one raw callback. -/
structure NativeCoveredWalUnlinkStop (state : NativeReadyState) where
  calls : WalCollectionReads
  inventory : WalCollectionInventoryReport calls state.session.directory state.session.descriptor state.writer.wal
  startsAt : inventory.descriptors = state.census
  sameOwner : inventory.owner = state.owner
  sameDirectory : inventory.lifetime.directorySlot = state.directorySlot
  manifest : calls.paths.readOptional (state.session.directory.file .manifest) = .ok state.writer.target.pair.manifest
  marker : calls.paths.readOptional (state.session.directory.file .walBoundary) = .ok state.writer.target.pair.walBoundary
  first : Nat
  rest : List Nat
  completedRemove : FilePath → EStateM IO.Error WalSealedUnlinkImage (Except IO.Error Unit)
  issueView : DirectoryReadNamespace
  issue : WalSealedUnlinkImage
  detached : List Nat
  completed : WalUnlinkPrefix state.session.directory inventory.lifetime.root completedRemove
    state.writer.wal.collectionOffsets inventory.lifetime.namespaceView (.start state.writer.wal)
    (first :: rest) none issueView issue detached
  afterView : DirectoryReadNamespace
  after : WalSealedUnlinkImage
  effect : WalUnlinkPhysicalEffect inventory.lifetime.root first issueView issue afterView after
  objects : afterView.modelObject = inventory.lifetime.namespaceView.modelObject
  drops : List LockReferenceDrop
  keepsSlots : ∀ slot ∈ state.census.slots,
    ∀ drop ∈ inventory.lifetime.drops ++ drops, drop.removes slot.reference = false
  remove : FilePath → EStateM FilePath UnlinkFiles (Except IO.Error Unit)
  returned : ∀ path before result after, completedRemove path before = .ok result after →
    remove path (inventory.listing.afterClose, before) = .ok result (inventory.listing.afterClose, after)
  stopped : remove (state.session.directory.file (.walSegment first))
    (inventory.listing.afterClose, issue) =
      .error (state.session.directory.file (.walSegment first)) (inventory.listing.afterClose.afterDrops drops, after)

namespace WalUnlinkPrefix

private theorem completedOrder {directory : DiskDirectory} {root : DeviceInode} {removeFile}
    {offsets pending removed : List Nat} {view afterView : DirectoryReadNamespace} {before after : WalSealedUnlinkImage}
    {failure : Option IO.Error}
    (reported : WalUnlinkPrefix directory root removeFile offsets view before pending failure afterView after removed)
    (success : failure = none) :
    ∃ done, offsets = done ++ pending ∧ ∀ offset ∈ removed, offset ∈ done := by
  induction reported with
  | pause => exact ⟨[], rfl, fun _ seen => seen⟩
  | @next first before result middle view middleView rest pending afterView after removed call effect accepted tail ih =>
    obtain ⟨done, order, detached⟩ := ih success
    refine ⟨first :: done, congrArg (first :: ·) order, ?_⟩
    intro offset included
    rcases List.mem_append.mp included with head | tail
    · cases effect.removed <;> simp_all
    · exact List.mem_cons_of_mem _ (detached offset tail)
  | failed | failedWithoutEffect => contradiction

theorem framesWal {directory : DiskDirectory} {root : DeviceInode} {removeFile}
    {offsets pending removed : List Nat} {view afterView : DirectoryReadNamespace} {before after : WalSealedUnlinkImage}
    {failure : Option IO.Error}
    (reported : WalUnlinkPrefix directory root removeFile offsets view before pending failure afterView after removed) :
    after.visible.directory = before.visible.directory ∧ after.visible.active = before.visible.active := by
  refine ⟨reported.keepsDirectory, ?_⟩
  induction reported with
  | pause | failedWithoutEffect => rfl
  | next _ effect _ _ ih => exact ih.trans effect.keeper
  | failed _ effect _ => exact effect.keeper

end WalUnlinkPrefix

namespace NativeCoveredWalUnlinkStop

variable {state : NativeReadyState}

def path (stop : NativeCoveredWalUnlinkStop state) : FilePath :=
  state.session.directory.file (.walSegment stop.first)

def census (stop : NativeCoveredWalUnlinkStop state) : DescriptorInventory :=
  stop.inventory.listing.afterClose.afterDrops stop.drops

def run (stop : NativeCoveredWalUnlinkStop state) (barrier : FilePath → CollectionM Unit) :
    EStateM.Result FilePath CollectionState (Except IO.Error Unit) :=
  WalCollectionInterruption.run state stop.calls stop.inventory.listing.afterClose
    (WalCollectionInterruption.perform state.session.directory stop.remove barrier)

theorem stops (stop : NativeCoveredWalUnlinkStop state) (valid : state.Valid) (barrier : FilePath → CollectionM Unit) :
    stop.run barrier = .error stop.path (.poisoned, ⟨(state.cache, stop.census, stop.after), state.files.owners⟩) := by
  let inventory := stop.inventory.listing.afterClose
  let action := WalCollectionInterruption.perform state.session.directory stop.remove barrier
  have planned := valid.retained.completeObservedWalPlan stop.calls stop.inventory stop.manifest stop.marker
  have stopped : (RunCollection.run (stop.first :: stop.rest) action).run
      (WalCollectionInterruption.atFiles state inventory stop.issue) =
        .error stop.path (.poisoned, ⟨(state.cache, stop.census, stop.after), state.files.owners⟩) := by
    simp [action, inventory, RunCollection.run, RunCollection.steps, WalCollectionInterruption.perform,
      RunCollection.performPaths, WalCollectionInterruption.unlink, WalCollectionInterruption.atFiles, List.forM_eq_forM,
      List.forM_cons, Bind.bind, ExceptT.bind, ExceptT.mk, ExceptT.run, EStateM.bind, stop.stopped, path, census]
  exact WalCollectionInterruption.stopsFromReady state stop.calls inventory action valid planned
    ((WalCollectionInterruption.runsCompleted state inventory stop.remove barrier stop.returned stop.completed rfl).trans stopped)

theorem member (stop : NativeCoveredWalUnlinkStop state) : stop.first ∈ state.writer.wal.collectionOffsets := by
  obtain ⟨done, order, _⟩ := stop.completed.completedOrder rfl
  rw [order]
  exact List.mem_append_right _ List.mem_cons_self

theorem intact (stop : NativeCoveredWalUnlinkStop state) :
    stop.after.visible.directory = state.writer.wal.directory ∧ stop.after.visible.active = state.writer.wal.active :=
  ⟨stop.effect.metadata.trans stop.completed.framesWal.1, stop.effect.keeper.trans stop.completed.framesWal.2⟩

theorem frameChild (stop : NativeCoveredWalUnlinkStop state) {name : String}
    (different : ∀ offset ∈ state.writer.wal.collectionOffsets, name ≠ renderWalSegmentName offset) :
    stop.afterView.child stop.inventory.lifetime.root name =
      stop.inventory.lifetime.namespaceView.child stop.inventory.lifetime.root name :=
  (stop.effect.frame _ (different stop.first stop.member)).trans (stop.completed.keepsOtherChild different)

theorem inspectedSeal (stop : NativeCoveredWalUnlinkStop state) (valid : state.Valid) :
    ∃ (segment : WalSegment) (sealed : segment ∈ state.writer.wal.sealed),
      segment.first = stop.first ∧ state.writer.wal.Eligible segment ∧
      stop.effect.target = some (stop.inventory.extent segment (List.mem_append_left _ sealed)).child.child := by
  obtain ⟨segment, sealed, same⟩ := (valid.retained.layout.collectionOffsets_approved stop.member).1
  obtain ⟨done, order, detached⟩ := stop.completed.completedOrder rfl
  have strict : state.writer.wal.collectionOffsets.Pairwise (· < ·) := by
    have sealed := (List.pairwise_append.mp valid.retained.layout.ordered).1.imp (fun order => order.1)
    exact List.pairwise_map.mpr (sealed.filter state.writer.wal.canRemove)
  rw [order] at strict
  have untouched : stop.first ∉ stop.detached := fun included =>
    Nat.lt_irrefl _ ((List.pairwise_append.mp strict).2.2 _ (detached _ included) _ List.mem_cons_self)
  have issue := stop.completed.lookupAfter stop.first
  rw [show stop.detached.contains stop.first = false from by simp [untouched]] at issue
  have original : stop.issueView.child stop.inventory.lifetime.root (renderWalSegmentName stop.first) =
      stop.inventory.lifetime.namespaceView.child stop.inventory.lifetime.root (renderWalSegmentName stop.first) := by
    simpa only [Bool.false_eq_true, ite_false] using issue
  let child := (stop.inventory.extent segment (List.mem_append_left _ sealed)).child.child
  have binding : stop.inventory.lifetime.namespaceView.child stop.inventory.lifetime.root
      (renderWalSegmentName segment.first) = some child := stop.inventory.bound segment _
  exact ⟨segment, sealed, same, (valid.retained.layout.collectionOffsets_approved stop.member).2 segment sealed same,
    stop.effect.lookup.symm.trans (original.trans ((congrArg (fun offset => stop.inventory.lifetime.namespaceView.child
      stop.inventory.lifetime.root (renderWalSegmentName offset)) same).symm.trans binding))⟩

theorem projects (stop : NativeCoveredWalUnlinkStop state) (valid : state.Valid) :
    ∃ projected, WalUnlinkInvariant state.writer.wal stop.inventory.lifetime.root stop.afterView stop.after projected := by
  have bound (segment : WalSegment) (sealed : segment ∈ state.writer.wal.sealed) :
      (stop.inventory.lifetime.namespaceView.child stop.inventory.lifetime.root (renderWalSegmentName segment.first)).isSome = true := by
    rw [stop.inventory.bound segment (List.mem_append_left _ sealed)]
    rfl
  obtain ⟨⟨_, prior⟩, _, _⟩ := stop.completed.projects valid.retained.layout (WalUnlinkInvariant.start bound) (fun _ member => member)
  exact ⟨_, prior.unlink valid.retained.layout stop.member stop.effect⟩

theorem selections (stop : NativeCoveredWalUnlinkStop state) (valid : state.Valid) :
    WalSegmentCollectionRetry state.writer.wal stop.after.visible ∧
      ∀ sealed ∈ stop.after.crashSealed, WalSegmentCollectionRetry state.writer.wal { stop.after.visible with sealed } := by
  obtain ⟨projected, invariant⟩ := stop.projects valid
  have retried := invariant.trace.projects valid.retained.layout
  refine ⟨invariant.visible.symm ▸ retried.1, ?_⟩
  intro sealed survives
  rw [invariant.visible]
  exact retried.2 sealed (invariant.survivors sealed survives)

private theorem keepsCensus (stop : NativeCoveredWalUnlinkStop state) (drops : List LockReferenceDrop)
    (keeps : ∀ slot ∈ state.census.slots,
      ∀ drop ∈ stop.inventory.lifetime.drops ++ drops, drop.removes slot.reference = false) :
    stop.inventory.listing.afterClose.afterDrops drops = state.census := by
  exact (stop.inventory.preservesCensus drops
    (fun slot live drop occurred => keeps slot (stop.startsAt ▸ live) drop occurred)).trans stop.startsAt

theorem sameCensus (stop : NativeCoveredWalUnlinkStop state) :
    stop.inventory.listing.afterClose = state.census ∧ stop.census = state.census := by
  refine ⟨?_, stop.keepsCensus _ stop.keepsSlots⟩
  have keep := stop.keepsCensus [] (fun slot live event occurs =>
    stop.keepsSlots slot live event (List.mem_append_left _ (by simpa using occurs)))
  simpa [DescriptorInventory.afterDrops, List.filter_eq_self.mpr (fun _ _ => rfl)] using keep

theorem retainsCustody (stop : NativeCoveredWalUnlinkStop state) (valid : state.Valid) :
    state.owner ∈ stop.census.slots ∧ state.directorySlot ∈ stop.census.slots ∧
    stop.afterView.modelObject stop.inventory.lifetime.root = stop.census.inode state.directorySlot.description ∧
    stop.afterView.child stop.inventory.lifetime.root "LOCK" = some stop.inventory.lifetime.lock ∧
    stop.afterView.modelObject stop.inventory.lifetime.lock = stop.census.inode state.owner.description := by
  refine ⟨stop.sameCensus.2.symm ▸ valid.ownerLive, stop.sameCensus.2.symm ▸ valid.directoryLive, ?_,
    (stop.frameChild (fun offset _ => lock_ne_renderWalSegmentName offset)).trans stop.inventory.lifetime.lockEntry, ?_⟩
  · rw [stop.objects, stop.sameCensus.2, ← stop.sameDirectory, ← stop.startsAt]
    exact stop.inventory.lifetime.identifiesDirectory
  · rw [stop.objects, stop.sameCensus.2, ← stop.sameOwner, ← stop.startsAt]
    exact stop.inventory.lifetime.identifiesLock

end NativeCoveredWalUnlinkStop

end Alvoki.Storage.DiskSession
