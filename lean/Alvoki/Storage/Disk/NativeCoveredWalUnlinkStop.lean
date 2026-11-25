import Alvoki.Storage.Disk.NativeReadyWalCollection

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

private abbrev UnlinkFiles := DescriptorInventory × WalSealedUnlinkImage
private abbrev CollectionState := Phase Installed × LockedFileState (CensusDirectoryCache × UnlinkFiles)
private abbrev CollectionM := ExceptT IO.Error (EStateM FilePath CollectionState)

/-- The first selected covered WAL unlink reports a physical effect and
stops before returning. No later unlink or directory sync is required. -/
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
  order : state.writer.wal.collectionOffsets = first :: rest
  afterView : DirectoryReadNamespace
  after : WalSealedUnlinkImage
  effect : WalUnlinkPhysicalEffect inventory.lifetime.root first inventory.lifetime.namespaceView
    (.start state.writer.wal) afterView after
  objects : afterView.modelObject = inventory.lifetime.namespaceView.modelObject
  drops : List LockReferenceDrop
  keepsSlots : ∀ slot ∈ state.census.slots,
    ∀ drop ∈ inventory.lifetime.drops ++ drops, drop.removes slot.reference = false
  remove : FilePath → EStateM FilePath UnlinkFiles (Except IO.Error Unit)
  stopped : remove (state.session.directory.file (.walSegment first))
    (inventory.listing.afterClose, .start state.writer.wal) =
      .error (state.session.directory.file (.walSegment first)) (inventory.listing.afterClose.afterDrops drops, after)

namespace NativeCoveredWalUnlinkStop

variable {state : NativeReadyState}

def path (stop : NativeCoveredWalUnlinkStop state) : FilePath :=
  state.session.directory.file (.walSegment stop.first)

def census (stop : NativeCoveredWalUnlinkStop state) : DescriptorInventory :=
  stop.inventory.listing.afterClose.afterDrops stop.drops

private def setPhase (phase : Phase Installed) : CollectionM Unit :=
  ExceptT.mk fun (_, files) => .ok (.ok ()) (phase, files)

private def unlink (stop : NativeCoveredWalUnlinkStop state) (path : FilePath) : CollectionM (Except IO.Error Unit) :=
  ExceptT.mk fun (phase, files) =>
    match stop.remove path files.image.2 with
    | .ok value reached => .ok (.ok value) (phase, ⟨(files.image.1, reached), files.owners⟩)
    | .error atPath reached => .error atPath (phase, ⟨(files.image.1, reached), files.owners⟩)

/-- Use the production collector's checked plan, publication phase and
shared dispatcher with an outer no-return channel for raw callbacks. -/
def run (stop : NativeCoveredWalUnlinkStop state) (barrier : FilePath → CollectionM Unit) :
    EStateM.Result FilePath CollectionState (Except IO.Error Unit) :=
  (do
    let installed ← state.session.phase.installed
    let selected ← (ExceptT.mk (fun (phase, files) => .ok (stop.calls.plan state.session.directory installed)
      (phase, ⟨(files.image.1, stop.inventory.listing.afterClose, files.image.2.2), files.owners⟩)) : CollectionM (List Nat))
    publishPrepared setPhase
      (RunCollection.run selected (RunCollection.performPaths stop.unlink barrier throw
        (fun first => state.session.directory.file (.walSegment first)) state.session.directory.path))
      (setPhase (.ready installed))).run
    (state.session.phase, ⟨(state.cache, state.census, .start state.writer.wal), state.files.owners⟩)

theorem stops (stop : NativeCoveredWalUnlinkStop state) (valid : state.Valid) (barrier : FilePath → CollectionM Unit) :
    stop.run barrier = .error stop.path (.poisoned, ⟨(state.cache, stop.census, stop.after), state.files.owners⟩) := by
  have planned := valid.retained.completeObservedWalPlan stop.calls stop.inventory stop.manifest stop.marker
  rw [stop.order] at planned
  simp [run, valid.phase, Phase.installed, planned, publishPrepared, setPhase, RunCollection.run, RunCollection.steps,
    RunCollection.performPaths, unlink, List.forM_eq_forM, List.forM_cons, Bind.bind, ExceptT.bind,
    ExceptT.bindCont, ExceptT.mk, ExceptT.run, EStateM.bind, Pure.pure, ExceptT.pure, EStateM.pure,
    stop.stopped, path, census]

private theorem member (stop : NativeCoveredWalUnlinkStop state) : stop.first ∈ state.writer.wal.collectionOffsets := by
  rw [stop.order]
  exact List.mem_cons_self

theorem inspectedSeal (stop : NativeCoveredWalUnlinkStop state) (valid : state.Valid) :
    ∃ (segment : WalSegment) (sealed : segment ∈ state.writer.wal.sealed),
      segment.first = stop.first ∧ state.writer.wal.Eligible segment ∧
      stop.effect.target = some (stop.inventory.extent segment (List.mem_append_left _ sealed)).child.child := by
  obtain ⟨segment, sealed, same⟩ := (valid.retained.layout.collectionOffsets_approved stop.member).1
  let child := (stop.inventory.extent segment (List.mem_append_left _ sealed)).child.child
  have binding : stop.inventory.lifetime.namespaceView.child stop.inventory.lifetime.root
      (renderWalSegmentName segment.first) = some child := stop.inventory.bound segment _
  exact ⟨segment, sealed, same, (valid.retained.layout.collectionOffsets_approved stop.member).2 segment sealed same,
    stop.effect.lookup.symm.trans ((congrArg (fun offset => stop.inventory.lifetime.namespaceView.child
      stop.inventory.lifetime.root (renderWalSegmentName offset)) same).symm.trans binding)⟩

theorem projects (stop : NativeCoveredWalUnlinkStop state) (valid : state.Valid) :
    ∃ projected, WalUnlinkInvariant state.writer.wal stop.inventory.lifetime.root stop.afterView stop.after projected := by
  have bound (segment : WalSegment) (sealed : segment ∈ state.writer.wal.sealed) :
      (stop.inventory.lifetime.namespaceView.child stop.inventory.lifetime.root (renderWalSegmentName segment.first)).isSome = true := by
    rw [stop.inventory.bound segment (List.mem_append_left _ sealed)]
    rfl
  exact ⟨_, (WalUnlinkInvariant.start bound).unlink valid.retained.layout stop.member stop.effect⟩

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
    (stop.effect.frame _ (lock_ne_renderWalSegmentName stop.first)).trans stop.inventory.lifetime.lockEntry, ?_⟩
  · rw [stop.objects, stop.sameCensus.2, ← stop.sameDirectory, ← stop.startsAt]
    exact stop.inventory.lifetime.identifiesDirectory
  · rw [stop.objects, stop.sameCensus.2, ← stop.sameOwner, ← stop.startsAt]
    exact stop.inventory.lifetime.identifiesLock

end NativeCoveredWalUnlinkStop

end Alvoki.Storage.DiskSession
