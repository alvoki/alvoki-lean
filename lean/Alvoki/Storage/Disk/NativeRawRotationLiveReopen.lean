import Alvoki.Storage.Disk.NativeRawRotationErrorClose
import Alvoki.Storage.Disk.NativeRotationWalWindow
import Alvoki.Storage.Disk.NativeDurableWriteReboot
import Alvoki.Storage.Disk.NativeAlignedWriteRecovery

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair
open WAL.Boundary (WalInodeImage)

section

variable {heap stream : Type} {opened : NativeOpenedHandle heap}
  {current : NativeOpenedPosition opened} {failed released : heap}
  {view : OpenCloseHeapView heap RotationCreateFiles}
  {storage : heap → CheckpointStorageObservation}

local notation "old" => current.current.ready.state
local notation "dir" => current.current.ready.state.session.directory
local notation "limit" => current.current.ready.state.writer.history.length
local notation "newStart" => current.current.ready.state.writer.rotationInstalled.activeFirst
local notation "names" => fun h => CheckpointSurvivingFiles.names (CheckpointStorageObservation.files (storage h))
local notation "visible" => fun h =>
  WalInodeImage.visible (RotationCreateFiles.inodes (LockedFileState.image (OpenCloseHeapView.files view h)))

/-- Live reopen uses the empty successor observed in the actual failed
rotation and the framed, already acknowledged WAL. The directory barrier
may have left a different set of crash alternatives. -/
theorem OpenCloseHeapView.ClosedFrom.readsAfterRotationDirectoryError
    (cache : OpenSyncCacheRefs opened.files opened.directory.path)
    {drops : CloseCacheField → List LockReferenceDrop}
    (closed : view.ClosedFrom opened.phase cache.active cache.pending cache.directory dir drops failed released)
    (nonempty : (old).writer.installed.activeFirst < (old).writer.installed.walBytes / WAL.frameSize)
    (root child : DeviceInode)
    (created : (view.files failed).image.view.child root (renderWalSegmentName newStart) = some child)
    (empty : visible failed ((view.files failed).image.view.modelObject child) = ByteArray.empty)
    (kept : RotationCreateFiles.FramesLiveChildren root
      (fun name => checkpointFreeWalChild limit name ∧ name ≠ renderWalSegmentName newStart)
      (view.files current.reached).image (view.files failed).image)
    (prior : NativeReadyStorage old (storage current.reached))
    (keeperVisible : ∀ inode, names current.reached ((dir).file (.walSegment (old).writer.wal.active.first)) = some inode →
      visible current.reached inode = (old).writer.wal.active.bytes)
    (markerVisible : (old).ObservesLiveWalMarker (storage current.reached) (visible current.reached))
    (sealedVisible : ∀ segment ∈ (old).writer.wal.sealed,
      ∀ inode, names current.reached ((dir).file (.walSegment segment.first)) = some inode →
      visible current.reached inode ∈ (storage current.reached).files.bytes inode)
    (catalog : (old).writer.wal.NamespaceWindow dir 0 limit (names current.reached))
    (atEntry : ∀ name, checkpointFreeWalChild limit name →
      names current.reached ⟨(dir).path.toString ++ "/" ++ name⟩ =
        ((view.files current.reached).image.view.child root name).map (view.files current.reached).image.view.modelObject)
    (atClose : ∀ name, checkpointFreeWalChild limit name →
      names released ⟨(dir).path.toString ++ "/" ++ name⟩ =
        ((view.files released).image.view.child root name).map (view.files released).image.view.modelObject)
    (images : heap → FileImage)
    (noManifest : (old).writer.target.pair.manifest = none)
    (source : RawMarkedOpenInterpreter heap stream) :
    let observed := (view.files released).image
    let openView := view.withFileProjection (fun h => ⟨images h, (view.files h).owners⟩)
    TryLockObserves (view.files released).owners dir (.ok true) ∧
    source.ReadsClientHistoryAtOpen (openView.withObservedWalFiles dir newStart names visible) dir storage visible released observed.view root
      current.current.submissions current.current.ready.reads current.current.history := by
  intro observed openView
  let valid := current.current.ready.readPrefix.refines.1
  let writer := (old).writer.rotated valid.retained.rotationTarget
  have ready : writer.RetainedReady dir (old).session.descriptor :=
    valid.retained.rotates nonempty ⟨rfl, rfl, rfl⟩
  have sameImage : (view.files released).image = (view.files failed).image := by
    rw [closed.2.2.1]
  have present (name : String) (inScope : checkpointFreeWalChild limit name)
      (apart : name ≠ renderWalSegmentName newStart) :
      let path : FilePath := ⟨(dir).path.toString ++ "/" ++ name⟩
      names released path = names current.reached path ∧
      ∀ inode, names current.reached path = some inode → visible released inode = visible current.reached inode := by
    obtain ⟨binding, bytes⟩ := kept name ⟨inScope, apart⟩
    refine ⟨?_, ?_⟩
    · rw [atClose name inScope, sameImage]
      exact binding.trans (atEntry name inScope).symm
    · intro inode found
      have atStart := (atEntry name inScope).symm.trans found
      change (view.files released).image.inodes.visible inode = _
      rw [sameImage]
      exact bytes inode atStart
  have pathPayload (name : String) (inScope : checkpointFreeWalChild limit name)
      (apart : name ≠ renderWalSegmentName newStart) :
      let path : FilePath := ⟨(dir).path.toString ++ "/" ++ name⟩
      (names released path).map (visible released) = (names current.reached path).map (visible current.reached) := by
    have carried := present name inScope apart
    exact (congrArg (Option.map (visible released)) carried.1).trans (Option.map_congr carried.2)
  have successorAtEnd : newStart = limit := valid.retained.rotationAtEnd
  have keeperFirst : writer.wal.active.first = newStart :=
    valid.retained.layout.activeEnd.trans successorAtEnd.symm
  have childAtClose (start : Nat) (bound : start ≤ limit) :=
    atClose (renderWalSegmentName start) (.inr ⟨start, bound, rfl⟩)
  have freshName : names released ((dir).file (.walSegment newStart)) =
      some (observed.view.modelObject child) := by
    change _ = some ((view.files released).image.view.modelObject child)
    rw [DiskDirectory.walSegment_path, childAtClose _ (Nat.le_of_eq successorAtEnd), sameImage, created, Option.map_some]
  have freshBytes : visible released (observed.view.modelObject child) = ByteArray.empty := by
    change (view.files released).image.inodes.visible ((view.files released).image.view.modelObject child) = _
    rw [sameImage]
    exact empty
  have fixedName (name : String) (administrative : name ∈ ["LOCK", "MANIFEST", "WAL.commit"]) :
      name ≠ renderWalSegmentName newStart := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at administrative
    rcases administrative with rfl | rfl | rfl <;> intro same <;>
      have pref := congrArg (fun name : String => name.toList.take 4) same <;>
      simp [renderWalSegmentName, String.toList_append] at pref
  have segmentName (start : Nat) (apart : start ≠ newStart) : renderWalSegmentName start ≠ renderWalSegmentName newStart := by
    intro same
    exact apart (by simpa only [parseWalSegmentName_render, Option.some.injEq] using congrArg parseWalSegmentName same)
  have newStarts : writer.wal.segments.map WalSegment.first =
      (old).writer.wal.segments.map WalSegment.first ++ [newStart] := by
    change ((old).writer.wal.segments ++ [(⟨(old).writer.wal.active.last, (old).writer.wal.active.last,
      ByteArray.empty⟩ : WalSegment)]).map WalSegment.first = _
    simp only [List.map_append, List.map_cons, List.map_nil, valid.retained.layout.activeEnd, successorAtEnd]
  have newCatalog : writer.wal.NamespaceWindow dir 0 limit (names released) := by
    apply WalSegmentImage.namespaceWindowAfterRotation newStarts
    · simp only [freshName, Option.isSome_some]
    · intro start low bound apart
      rw [DiskDirectory.walSegment_path,
        (present _ (.inr ⟨start, bound, rfl⟩) (segmentName start apart)).1, ← DiskDirectory.walSegment_path]
      exact catalog start low bound
  have manifestAbsent : names released ((dir).file .manifest) = none := by
    have absent := prior.manifest
    rw [noManifest] at absent
    exact (present "MANIFEST" (.inl (by simp)) (fixedName _ (by simp))).1.trans absent
  have lockBound : names released ((dir).file .lock) = some ((old).census.inode (old).owner.description) :=
    (present "LOCK" (.inl (by simp)) (fixedName _ (by simp))).1.trans prior.lockBound
  have marker : (names released ((dir).file .walBoundary)).map (visible released) = writer.target.pair.walBoundary :=
    (pathPayload "WAL.commit" (.inl (by simp)) (fixedName _ (by simp))).trans markerVisible
  have rotating := valid.retained.rotationInput nonempty
  have activeEnd : (old).writer.wal.active.last = newStart :=
    valid.retained.layout.activeEnd.trans successorAtEnd.symm
  have segmentPayload (segment : WalSegment) (below : segment.first < newStart) {inode : Nat}
      (bound : names current.reached ((dir).file (.walSegment segment.first)) = some inode)
      (bytes : visible current.reached inode = segment.bytes) :
      (names released ((dir).file (.walSegment segment.first))).map (visible released) = some segment.bytes := by
    have priorBytes : (names current.reached ((dir).file (.walSegment segment.first))).map (visible current.reached) =
        some segment.bytes := by rw [bound, Option.map_some, bytes]
    exact (pathPayload (renderWalSegmentName segment.first)
      (.inr ⟨segment.first, Nat.le_trans (Nat.le_of_lt below) (Nat.le_of_eq successorAtEnd), rfl⟩)
      (segmentName _ (Nat.ne_of_lt below))).trans priorBytes
  have oldKeep : (names released ((dir).file (.walSegment (old).writer.wal.active.first))).map (visible released) =
      some (old).writer.wal.active.bytes := by
    obtain ⟨inode, bound, _⟩ := prior.keeper
    exact segmentPayload _ (activeEnd ▸ rotating.nonempty) bound (keeperVisible inode bound)
  have previousSeals (segment : WalSegment) (member : segment ∈ (old).writer.wal.sealed) :
      (names released ((dir).file (.walSegment segment.first))).map (visible released) = some segment.bytes := by
    have below : segment.first < newStart := activeEnd ▸
      Nat.lt_trans (rotating.sealedBefore segment member) rotating.nonempty
    obtain ⟨inode, bound, bytes⟩ := (prior.sealedFiles segment member).samplesAtBinding
      (names current.reached) (visible current.reached) rfl (sealedVisible segment member)
    exact segmentPayload segment below bound bytes
  have seals (segment : WalSegment) (member : segment ∈ writer.wal.sealed) :
      (names released ((dir).file (.walSegment segment.first))).map (visible released) = some segment.bytes := by
    change segment ∈ (old).writer.wal.sealed ++ [(old).writer.wal.active] at member
    rcases List.mem_append.mp member with prior | keeper
    · exact previousSeals segment prior
    · obtain rfl := List.mem_singleton.mp keeper
      exact oldKeep
  have active : (names released ((dir).file (.walSegment writer.wal.active.first))).map (visible released) =
      some writer.wal.active.bytes := by
    rw [keeperFirst, freshName, Option.map_some, freshBytes]
    rfl
  have replay := @RawMarkedOpenInterpreter.replaysRetainedWalAtOpen
    (source := source) (namespaceView := observed.view) (root := root)
    (view := openView) (storage := storage) («visible» := visible) (entry := released)
    (ready := ready) (missing := noManifest)
    (files := ⟨⟨_, lockBound⟩, manifestAbsent, marker, newCatalog, seals, active⟩)
  obtain ⟨_, history, pending⟩ := current.current.ready.readPrefix.refines
  have finalReplay := @Eq.mp _ _ (congrArg
    (fun writes => source.ReplaysWalBeforeCheckpointAtOpen (openView.withObservedWalFiles dir writer.wal.active.first names visible) dir writer.wal.active.first
      storage visible released observed.view root writes) history) (@replay)
  rw [keeperFirst] at finalReplay
  have retainedChild : ∀ start ≤ current.current.history.length,
      (observed.view.child root (renderWalSegmentName start)).map observed.view.modelObject =
        names released ((dir).file (.walSegment start)) :=
    fun start bound => (childAtClose start (by simpa only [history] using bound)).symm
  refine ⟨?_, ?_⟩
  · rw [closed.2.2.1]
    simp [TryLockObserves, LockOwners.set]
  · intro input returnedAt table admission reads _ absent initializes keeps returned
    exact (@RawMarkedOpenInterpreter.ReplaysWalBeforeCheckpointAtOpen.recordsReads
      (opened := finalReplay) (pending := pending)) admission reads retainedChild absent initializes keeps returned

end

end Alvoki.Storage.DiskSession
