import Alvoki.Storage.Disk.NativeRawRotationErrorClose
import Alvoki.Storage.Disk.NativeRotationWalWindow
import Alvoki.Storage.Disk.NativeDurableWriteReboot
import Alvoki.Storage.Disk.NativeAlignedWriteRecovery

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair
open WAL.Boundary (WalInodeImage)

section

variable {heap stream : Type} {opened : NativeOpenedHandle heap}
  {current : NativeOpenedPosition opened} {cause : IO.Error} {failed released : heap}
  {view : OpenCloseHeapView heap RotationCreateFiles}
  {storage : heap → CheckpointStorageObservation}

local notation "old" => current.current.ready.state
local notation "dir" => current.current.ready.state.session.directory
local notation "limit" => current.current.ready.state.writer.history.length
local notation "newStart" => current.current.ready.state.writer.rotationInstalled.activeFirst
local notation "names" => fun h => CheckpointSurvivingFiles.names (CheckpointStorageObservation.files (storage h))
local notation "visible" => fun h =>
  WalInodeImage.visible (RotationCreateFiles.inodes (LockedFileState.image (OpenCloseHeapView.files view h)))

/-- The child names inspected by the checkpoint-free live reader. -/
def RotationCreateFiles.liveWalReadChild (through : Nat) (name : String) : Prop :=
  name ∈ ["LOCK", "MANIFEST", "WAL.commit"] ∨ ∃ start ≤ through, name = renderWalSegmentName start

/-- Close preserves the visible successor even if the failed directory
barrier left it absent from a crash map. The same rooted close observation
supplies the WAL reads of a successful literal reopen. -/
theorem OpenCloseHeapView.ClosedFrom.readsAfterRotationDirectoryError
    (failure : NativeRotationDirectoryFailure old (some cause))
    (cache : OpenSyncCacheRefs opened.files opened.directory.path)
    {drops : CloseCacheField → List LockReferenceDrop}
    (closed : view.ClosedFrom opened.phase cache.active cache.pending cache.directory dir drops failed released)
    (atFailure : view.Matches opened.phase cache.active cache.pending cache.directory failed failure.closeState)
    (prior : NativeReadyProtectedStorage old ⟨names current.reached, fun inode => [failure.parent.files.inodes.visible inode]⟩)
    (catalog : (old).writer.wal.NamespaceWindow dir 0 limit (names current.reached))
    (atEntry : ∀ name, RotationCreateFiles.liveWalReadChild limit name →
      names current.reached ⟨(dir).path.toString ++ "/" ++ name⟩ =
        (failure.parent.files.view.child failure.parent.root name).map failure.parent.files.view.modelObject)
    (atClose : ∀ name, RotationCreateFiles.liveWalReadChild limit name →
      names released ⟨(dir).path.toString ++ "/" ++ name⟩ =
        ((view.files released).image.view.child failure.parent.root name).map (view.files released).image.view.modelObject)
    (rootPath : names released (dir).path =
      (failure.reported.pathObject (dir).path).map (view.files released).image.view.modelObject)
    (images : heap → FileImage)
    (pairAt : (images released).directory.active =
      ⟨(names released ((dir).file .manifest)).map (visible released),
        (names released ((dir).file .walBoundary)).map (visible released)⟩)
    (keeperAt : (images released).keeper.active =
      (names released ((dir).file (.walSegment newStart))).map (visible released))
    (noManifest : (old).writer.target.pair.manifest = none)
    (source : RawMarkedOpenInterpreter heap stream) :
    let observed := (view.files released).image
    let openView := view.withFileProjection (fun h => ⟨images h, (view.files h).owners⟩)
    TryLockObserves (view.files released).owners dir (.ok true) ∧
    names released (dir).path = some (observed.view.modelObject failure.parent.root) ∧
    (∀ start ≤ current.current.history.length,
      (observed.view.child failure.parent.root (renderWalSegmentName start)).map observed.view.modelObject =
        names released ((dir).file (.walSegment start))) ∧
    source.ReadsClientHistoryAtOpen openView dir storage visible released observed.view failure.parent.root
      current.current.submissions current.current.ready.reads current.current.history := by
  intro observed openView
  let valid := current.current.ready.readPrefix.refines.1
  let writer := (failure.liveState valid).writer
  have ready := failure.liveRetained valid
  have image : (view.files released).image = failure.reported.after := by
    rw [closed.2.2.1, atFailure.2.2.1]
    rfl
  have observedImage : observed = failure.reported.after := image
  obtain ⟨_, _, root, _, _, _, lockName, _, successor, _, _⟩ := failure.custody valid
  have present (name : String) (inScope : RotationCreateFiles.liveWalReadChild limit name)
      (apart : name ≠ renderWalSegmentName newStart) :
      names released ⟨(dir).path.toString ++ "/" ++ name⟩ =
        names current.reached ⟨(dir).path.toString ++ "/" ++ name⟩ := by
    rw [atClose name inScope, atEntry name inScope, image, failure.reported.view,
      failure.created.names name apart, failure.created.objects]
  have successorAtEnd : newStart = limit := valid.retained.rotationAtEnd
  have keeperFirst : writer.wal.active.first = newStart :=
    valid.retained.layout.activeEnd.trans successorAtEnd.symm
  have child (start : Nat) (bound : start ≤ limit) :=
    atClose (renderWalSegmentName start) (.inr ⟨start, bound, rfl⟩)
  have freshName : names released ((dir).file (.walSegment newStart)) =
      some (observed.view.modelObject failure.created.child.child) := by
    change _ = some (observed.view.modelObject failure.created.child.child)
    change failure.reported.after.view.child failure.parent.root (renderWalSegmentName newStart) =
      some failure.created.child.child at successor
    simpa only [DiskDirectory.walSegment_path, image, observedImage, successor, Option.map_some] using
      child newStart (Nat.le_of_eq successorAtEnd)
  have freshBytes : visible released (observed.view.modelObject failure.created.child.child) = ByteArray.empty := by
    change observed.inodes.visible (observed.view.modelObject failure.created.child.child) = _
    rw [observedImage, failure.reported.bytes, failure.reported.view, failure.created.inode]
    exact failure.created.empty
  have newStarts : writer.wal.segments.map WalSegment.first =
      (old).writer.wal.segments.map WalSegment.first ++ [newStart] := by
    change ((old).writer.wal.segments ++ [(⟨(old).writer.wal.active.last, (old).writer.wal.active.last,
      ByteArray.empty⟩ : WalSegment)]).map WalSegment.first = _
    simp only [List.map_append, List.map_cons, List.map_nil, valid.retained.layout.activeEnd, successorAtEnd]
  have newCatalog : writer.wal.NamespaceWindow dir 0 limit (names released) := by
    apply WalSegmentImage.namespaceWindowAfterRotation newStarts
    · simp only [freshName, Option.isSome_some]
    · intro start low bound apart
      have distinct : renderWalSegmentName start ≠ renderWalSegmentName newStart := by
        intro same
        exact apart (by simpa only [parseWalSegmentName_render, Option.some.injEq] using congrArg parseWalSegmentName same)
      rw [DiskDirectory.walSegment_path, present _ (.inr ⟨start, bound, rfl⟩) distinct, ← DiskDirectory.walSegment_path]
      exact catalog start low bound
  have manifestAbsent : names released ((dir).file .manifest) = none := by
    have kept := present "MANIFEST" (.inl (by simp))
      (by
        intro same
        have namesEq := congrArg (fun name : String => name.toList.take 4) same
        simp [renderWalSegmentName, String.toList_append] at namesEq)
    have originally := prior.manifest
    rw [noManifest] at originally
    exact kept.trans originally
  have lockBound : names released ((dir).file .lock) = some (observed.view.modelObject failure.parent.lock.child) := by
    change names released ⟨(dir).path.toString ++ "/" ++ "LOCK"⟩ = _
    simpa only [image, observedImage, lockName, Option.map_some] using atClose "LOCK" (.inl (by simp))
  obtain ⟨objects, keeperName, markerName, _, _, keeperBytes, _, markerBytes, _⟩ :=
    (RotationRawCreateEffect.afterOpen (failure.created.afterSync true)).keepsKeeperMarker
  change failure.created.files.view.modelObject = failure.parent.files.view.modelObject at objects
  change failure.created.files.view.child failure.parent.root (renderWalSegmentName (old).writer.installed.activeFirst) =
    some failure.parent.keeper.child at keeperName
  change failure.created.files.view.child failure.parent.root "WAL.commit" = some failure.parent.marker.child at markerName
  change (failure.created.afterSync true).files.inodes.visible (failure.parent.files.view.modelObject failure.parent.keeper.child) =
    (old).writer.wal.active.bytes at keeperBytes
  change (old).writer.wal.directory.active.walBoundary = some
    ((failure.created.afterSync true).files.inodes.visible (failure.parent.files.view.modelObject failure.parent.marker.child)) at markerBytes
  have marker : (names released ((dir).file .walBoundary)).map (visible released) = writer.target.pair.walBoundary := by
    change (names released ⟨(dir).path.toString ++ "/" ++ "WAL.commit"⟩).map (visible released) = _
    rw [atClose "WAL.commit" (.inl (by simp))]
    change ((observed.view.child failure.parent.root "WAL.commit").map observed.view.modelObject).map
      observed.inodes.visible = (old).writer.target.pair.walBoundary
    rw [observedImage, failure.reported.view, markerName, failure.reported.bytes, objects]
    simpa only [Option.map_some, valid.retained.walPair] using markerBytes.symm
  have pair : (images released).directory.active = writer.target.pair := by
    rw [pairAt, manifestAbsent, Option.map_none, marker]
    exact congrArg (fun manifest => DirectoryPublication.Bindings.mk manifest writer.target.pair.walBoundary) noManifest.symm
  have newKeeper : (images released).keeper.active = some writer.target.trimmed := by
    rw [keeperAt, freshName, Option.map_some, freshBytes] <;> rfl
  have oldKeep : (names released ((dir).file (.walSegment (old).writer.wal.active.first))).map (visible released) =
      some (old).writer.wal.active.bytes := by
    have first := valid.retained.resumed.keeper.trans valid.retained.active
    have bounded : (old).writer.wal.active.first ≤ limit :=
      valid.retained.layout.activeEnd ▸ valid.retained.layout.forward _ (List.mem_append_right _ (by simp))
    rw [DiskDirectory.walSegment_path, child _ bounded]
    change ((observed.view.child failure.parent.root (renderWalSegmentName (old).writer.wal.active.first)).map
      observed.view.modelObject).map observed.inodes.visible = _
    rw [observedImage, failure.reported.view, ← first, keeperName, failure.reported.bytes, objects]
    simpa only [Option.map_some] using congrArg some keeperBytes
  have previousSeals (segment : WalSegment) (member : segment ∈ (old).writer.wal.sealed) :
      (names released ((dir).file (.walSegment segment.first))).map (visible released) = some segment.bytes := by
    have rotating := valid.retained.rotationInput failure.parent.nonempty
    have activeEnd : (old).writer.wal.active.last = newStart :=
      valid.retained.layout.activeEnd.trans successorAtEnd.symm
    have below : segment.first < newStart := activeEnd ▸
      Nat.lt_trans (rotating.sealedBefore segment member) rotating.nonempty
    have within := Nat.le_trans (Nat.le_of_lt below) (Nat.le_of_eq successorAtEnd)
    have apart : renderWalSegmentName segment.first ≠ renderWalSegmentName newStart := by
      intro same
      exact (Nat.ne_of_lt below) (by simpa only [parseWalSegmentName_render, Option.some.injEq] using congrArg parseWalSegmentName same)
    obtain ⟨inode, named, payload⟩ := prior.sealedFiles segment member
    have binding := (atEntry _ (.inr ⟨segment.first, within, rfl⟩)).symm.trans named
    obtain ⟨object, atParent, modeled⟩ := Option.map_eq_some_iff.mp binding
    have distinct := modeled ▸ failure.created.freshObject _ _ atParent
    have priorName : names current.reached ⟨(dir).path.toString ++ "/" ++ renderWalSegmentName segment.first⟩ = some inode := named
    rw [DiskDirectory.walSegment_path, present _ (.inr ⟨segment.first, within, rfl⟩) apart, priorName, Option.map_some]
    have contents := (failure.created.bytes inode distinct).1.trans (List.cons.inj payload).1
    change some (observed.inodes.visible inode) = _
    rw [observedImage, failure.reported.bytes]
    exact congrArg some contents
  obtain ⟨layout, target, active, tail, descriptors, offsets⟩ := ready.visibleReopenLayout pair newKeeper
  have modeled := layout.modeledWindow _ offsets
  have onWal : layout.VisibleWal dir (names released) (visible released) := by
    refine ⟨fun start low high => (newCatalog start (Nat.zero_le _) (layout.through ▸ high)).trans (modeled.1 start low), ?_, ?_⟩
    · intro segment member
      have sealed := WalSegmentImage.selectedSeals_subset descriptors member
      change segment ∈ (old).writer.wal.sealed ++ [(old).writer.wal.active] at sealed
      rcases List.mem_append.mp sealed with prior | keeper
      · exact previousSeals segment prior
      · obtain rfl := List.mem_singleton.mp keeper
        exact oldKeep
    · rw [active, keeperFirst, freshName, Option.map_some, freshBytes, tail, ByteArray.append_empty] <;> rfl
  have noSelected := (congrArg (fun t : Target => t.pair.manifest) target).trans noManifest
  have selectedMarker := marker.trans (congrArg (fun t : Target => t.pair.walBoundary) target).symm
  have replay : source.ReplaysWalBeforeCheckpointAtOpen openView dir layout.keeper.first storage visible released
      observed.view failure.parent.root (old).writer.history :=
    @RawMarkedOpenInterpreter.replaysVisibleWalBeforeCheckpointAtOpen
      (source := source) (namespaceView := observed.view) (root := failure.parent.root)
      (view := openView) (directory := dir) (storage := storage) («visible» := visible) (entry := released)
      (history := (old).writer.history)
      (layout := layout) (lockBound := lockBound) (missing := noSelected) (manifestAbsent := manifestAbsent)
      (markerBytes := selectedMarker) (following := modeled.2)
      (ordered := ready.resumed.ordered) (wal := onWal)
  obtain ⟨_, history, pending⟩ := current.current.ready.readPrefix.refines
  have finalReplay := @Eq.mp _ _ (congrArg
    (fun writes => source.ReplaysWalBeforeCheckpointAtOpen openView dir layout.keeper.first
      storage visible released observed.view failure.parent.root writes) history) (@replay)
  have retainedChild : ∀ start ≤ current.current.history.length,
      (observed.view.child failure.parent.root (renderWalSegmentName start)).map observed.view.modelObject =
        names released ((dir).file (.walSegment start)) :=
    fun start bound => (child start (by simpa only [history] using bound)).symm
  refine ⟨?_, rootPath.trans (congrArg (Option.map observed.view.modelObject) root), retainedChild, ?_⟩
  · rw [closed.2.2.1]
    simp [TryLockObserves, LockOwners.set]
  · intro input returnedAt table admission reads _ absent initializes keeps returned
    exact (@RawMarkedOpenInterpreter.ReplaysWalBeforeCheckpointAtOpen.recordsReads
      (opened := finalReplay) (pending := pending)) admission reads retainedChild absent initializes keeps returned

end

end Alvoki.Storage.DiskSession
