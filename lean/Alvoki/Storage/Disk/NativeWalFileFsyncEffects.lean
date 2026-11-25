import Alvoki.Storage.Disk.NativeCheckpointFsyncEffects
import Alvoki.Storage.Disk.NativeWalStage

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting
open WAL.Boundary (WalInodeImage)

/-- Invert success of the actual file group using the two dispatch
equations. A returned error from either fsync excludes group success,
even when the later fsync still ran. -/
theorem RawSyncCalls.groupedFileReturns {heap : Type} (calls : RawSyncCalls heap)
    {directory : DiskDirectory} {files : DiskTable.OpenSyncFiles}
    (cache : OpenSyncCacheRefs files directory.path) {first : Nat}
    {staged consumed reached : heap} {keeperHandle markerHandle : IO.FS.Handle}
    (keeper : calls.syncPath directory.path (directory.file (.walSegment first))
      cache.directory cache.active cache.pending staged = calls.fsync keeperHandle staged)
    (marker : calls.syncPath directory.path (directory.file .stagedWalBoundary)
      cache.directory cache.active cache.pending (reachedState (calls.fsync keeperHandle staged)) =
        calls.fsync markerHandle consumed)
    (grouped : calls.group directory.path cache.directory cache.active cache.pending
      #[directory.file (.walSegment first), directory.file .stagedWalBoundary] staged = .ok () reached) :
    calls.fsync keeperHandle staged = .ok () (reachedState (calls.fsync keeperHandle staged)) ∧
    calls.fsync markerHandle consumed = .ok () reached := by
  unfold group at grouped
  rw [SyncPathGroup.run_pair, keeper] at grouped
  cases firstCall : calls.fsync keeperHandle staged with
  | error cause atKeeper =>
    simp only [firstCall, reachedState] at marker
    cases secondCall : calls.fsync markerHandle consumed <;>
      simp [firstCall, marker, secondCall] at grouped
  | ok result atKeeper =>
    cases result
    simp only [firstCall, reachedState] at marker
    cases secondCall : calls.fsync markerHandle consumed with
    | error cause after => simp [firstCall, marker, secondCall] at grouped
    | ok result after =>
      cases result
      simp [firstCall, marker, secondCall] at grouped
      subst reached
      exact ⟨rfl, rfl⟩

/-- Each file sync can establish only its own bytes. Pending-reference
consumption has a separate frame because it can finalize handles.
Preserve one joint crash name choice for the unrelated footprint. -/
theorem RegularFileSyncEffect.pairedStored {entry afterKeeper atMarker reached : CheckpointStorageObservation}
    {keeperInode markerInode : Nat} {keeper staged : FilePath} {keeperBytes markerBytes : ByteArray}
    (syncKeeper : RegularFileSyncEffect keeperInode [keeperBytes] entry afterKeeper)
    (syncMarker : RegularFileSyncEffect markerInode [markerBytes] atMarker reached)
    (keeperBound : entry.files.names keeper = some keeperInode)
    (markerBound : atMarker.files.names staged = some markerInode)
    (distinct : keeperInode ≠ markerInode) {footprint : FilePath → Prop}
    (consumed : afterKeeper.Frames (fun path => path = keeper ∨ footprint path) atMarker)
    (unrelated : ∀ path, footprint path → ∀ inode, entry.files.names path = some inode →
      inode ≠ keeperInode ∧ inode ≠ markerInode) :
    reached.files.Stored keeper keeperBytes ∧ reached.files.Stored staged markerBytes ∧
      entry.Frames footprint reached := by
  have keeperAfter : afterKeeper.files.names keeper = some keeperInode :=
    (congrFun syncKeeper.names keeper).trans keeperBound
  have keeperAtMarker : atMarker.files.names keeper = some keeperInode :=
    ((consumed.visible keeper (.inl rfl)).1).trans keeperAfter
  have first : entry.Frames footprint afterKeeper :=
    syncKeeper.frames fun path kept inode named => (unrelated path kept inode named).1
  have preceding := first.trans (consumed.weaken fun _ kept => .inr kept)
  have last : atMarker.Frames (fun path => path = keeper ∨ footprint path) reached := by
    apply syncMarker.frames
    intro path kept inode named
    rcases kept with rfl | retained
    · exact (Option.some.inj (named.symm.trans keeperAtMarker)) ▸ distinct
    · exact (unrelated path retained inode (((preceding.visible path retained).1).symm.trans named)).2
  exact ⟨last.visible.stored (.inl rfl) (consumed.visible.stored (.inl rfl) (syncKeeper.stored keeperBound)),
    syncMarker.stored markerBound, preceding.trans (last.weaken fun _ kept => .inr kept)⟩

/-- A successful publication group yields the exact two durable file
payloads. The local fsync laws apply at different heaps, and the
pending-reference store frames the keeper and unrelated recovery paths. -/
theorem RawSyncCalls.groupedReturnedStorage {heap image : Type} (calls : RawSyncCalls heap)
    {directory : DiskDirectory} {files : DiskTable.OpenSyncFiles}
    (cache : OpenSyncCacheRefs files directory.path) (view : OpenCloseHeapView heap image) {first : Nat}
    {appended staged consumed reached : heap} {keeperHandle markerHandle : IO.FS.Handle}
    (keeperRoute : calls.syncPath directory.path (directory.file (.walSegment first))
      cache.directory cache.active cache.pending staged = calls.fsync keeperHandle staged)
    (markerRoute : calls.syncPath directory.path (directory.file .stagedWalBoundary)
      cache.directory cache.active cache.pending (reachedState (calls.fsync keeperHandle staged)) =
        calls.fsync markerHandle consumed)
    (grouped : calls.group directory.path cache.directory cache.active cache.pending
      #[directory.file (.walSegment first), directory.file .stagedWalBoundary] staged = .ok () reached)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ heap, RunDirectoryInodeView directory (inodes heap) (runs heap))
    (keeperTarget : RawFsyncTarget view appended staged keeperHandle)
    (markerTarget : RawFsyncTarget view staged consumed markerHandle)
    {keeperInode markerInode : Nat} {keeperBytes markerBytes : ByteArray}
    (keeperSelected : (view.handle appended keeperHandle).1.inode
      (view.handle appended keeperHandle).2.1.description = keeperInode)
    (markerSelected : (view.handle staged markerHandle).1.inode
      (view.handle staged markerHandle).2.1.description = markerInode)
    (keeperPayload : (inodes staged).visible keeperInode = keeperBytes)
    (markerPayload : (inodes consumed).visible markerInode = markerBytes)
    (keeperEffect : ∀ after, calls.fsync keeperHandle staged = .ok () after →
      let inode := (view.descriptors staged).inode (view.handle staged keeperHandle).2.1.description
      (observe staged).visible (directory.file (.walSegment first)) = some inode ∧
      inodes after = (inodes staged).completeFileSync inode ∧
      (observe after).visible = (observe staged).visible ∧
      (observe after).crashBindings = (observe staged).crashBindings)
    (markerEffect : calls.fsync markerHandle consumed = .ok () reached →
      let inode := (view.descriptors consumed).inode (view.handle consumed markerHandle).2.1.description
      (observe consumed).visible (directory.file .stagedWalBoundary) = some inode ∧
      inodes reached = (inodes consumed).completeFileSync inode ∧
      (observe reached).visible = (observe consumed).visible ∧
      (observe reached).crashBindings = (observe consumed).crashBindings)
    (distinct : keeperInode ≠ markerInode) {footprint : FilePath → Prop}
    (consumeFrame : (observe (reachedState (calls.fsync keeperHandle staged))).storageObservation.Frames
      (fun path => path = directory.file (.walSegment first) ∨ footprint path) (observe consumed).storageObservation)
    (unrelated : ∀ path, footprint path → ∀ inode, (observe staged).storageObservation.files.names path = some inode →
      inode ≠ keeperInode ∧ inode ≠ markerInode) :
    (observe reached).storageObservation.files.Stored (directory.file (.walSegment first)) keeperBytes ∧
    (observe reached).storageObservation.files.Stored (directory.file .stagedWalBoundary) markerBytes ∧
    (observe staged).storageObservation.Frames footprint (observe reached).storageObservation := by
  obtain ⟨keeperReturned, markerReturned⟩ := calls.groupedFileReturns cache keeperRoute markerRoute grouped
  have keeperEffect := keeperTarget.returnedFileEffect calls keeperReturned inodes runs observe
    (directory.file (.walSegment first)) (keeperEffect _)
  have markerEffect := markerTarget.returnedFileEffect calls markerReturned inodes runs observe
    (directory.file .stagedWalBoundary) markerEffect
  dsimp only at keeperEffect markerEffect
  rw [keeperSelected, keeperPayload] at keeperEffect
  rw [markerSelected, markerPayload] at markerEffect
  exact keeperEffect.2.pairedStored markerEffect.2 keeperEffect.1 markerEffect.1 distinct consumeFrame unrelated

/-- Move the synced staged inode to the canonical marker, then use the
same directory handle selected by the publication. Every selectable
crash map has the live keeper and marker bindings and no staged name. -/
theorem RawSyncCalls.publishedStorage {heap image : Type} (calls : RawSyncCalls heap)
    {directory : DiskDirectory} {files : DiskTable.OpenSyncFiles}
    (cache : OpenSyncCacheRefs files directory.path) (view : OpenCloseHeapView heap image)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit) (storage : heap → CheckpointStorageObservation)
    {grouped renamed issued reached : heap} {handle : IO.FS.Handle} {first : Nat} {keeperBytes markerBytes : ByteArray}
    (moved : rename (directory.file .stagedWalBoundary) (directory.file .walBoundary) grouped = .ok () renamed)
    (loaded : calls.readDirectory cache.directory renamed = .ok (some handle) issued)
    (returned : calls.fsync handle issued = .ok () reached)
    (target : RawFsyncTarget view renamed issued handle)
    (root : (storage renamed).files.names directory.path =
      some ((view.handle renamed handle).1.inode (view.handle renamed handle).2.1.description))
    (keeperStored : (storage grouped).files.Stored (directory.file (.walSegment first)) keeperBytes)
    (stagedStored : (storage grouped).files.Stored (directory.file .stagedWalBoundary) markerBytes)
    (stagedPrivate : ∀ inode, (storage grouped).files.names (directory.file .stagedWalBoundary) = some inode →
      (storage grouped).files.names (directory.file .walBoundary) ≠ some inode)
    (renameEffect : rename (directory.file .stagedWalBoundary) (directory.file .walBoundary) grouped =
      .ok () renamed → ∀ inode,
      (storage grouped).files.names (directory.file .stagedWalBoundary) = some inode →
      (storage grouped).files.names (directory.file .walBoundary) ≠ some inode →
      (storage renamed).files.names (directory.file .walBoundary) = some inode ∧
      (storage renamed).files.names (directory.file .stagedWalBoundary) = none ∧
      (storage renamed).files.bytes inode = (storage grouped).files.bytes inode)
    (renameFrame : rename (directory.file .stagedWalBoundary) (directory.file .walBoundary) grouped =
      .ok () renamed → (storage grouped).files.Frames
        (fun path => path ≠ directory.file .stagedWalBoundary ∧ path ≠ directory.file .walBoundary) (storage renamed).files)
    (loadFrame : calls.readDirectory cache.directory renamed = .ok (some handle) issued →
      (storage renamed).files.Frames (fun path => path = directory.path ∨ ∃ file, path = directory.file file)
        (storage issued).files)
    (syncEffect : calls.fsync handle issued = .ok () reached →
      (view.handle issued handle).2.1 ∈ (view.descriptors issued).slots →
      (storage issued).files.names directory.path =
        some ((view.descriptors issued).inode (view.handle issued handle).2.1.description) →
      (storage issued).files.Frames (fun path => path = directory.path ∨ ∃ file, path = directory.file file)
        (storage reached).files ∧ (storage reached).crashNames ≠ [] ∧
      ∀ names ∈ (storage reached).crashNames, ∀ file, names (directory.file file) =
        (storage reached).files.names (directory.file file)) :
    (storage reached).files.Stored (directory.file (.walSegment first)) keeperBytes ∧
    (storage reached).files.Stored (directory.file .walBoundary) markerBytes ∧
    (storage reached).crashNames ≠ [] ∧
    ∀ names ∈ (storage reached).crashNames,
      names (directory.file (.walSegment first)) = (storage reached).files.names (directory.file (.walSegment first)) ∧
      names (directory.file .walBoundary) = (storage reached).files.names (directory.file .walBoundary) ∧
      names (directory.file .stagedWalBoundary) = none := by
  obtain ⟨markerInode, staged, durable⟩ := stagedStored
  obtain ⟨markerNamed, detached, markerBytesAfterRename⟩ :=
    renameEffect moved markerInode staged (stagedPrivate markerInode staged)
  have readFrame := loadFrame loaded
  have issuedRoot := (readFrame directory.path (.inl rfl)).1.trans root
  rw [← target.inode] at issuedRoot
  obtain ⟨syncFrame, nonempty, settled⟩ := syncEffect returned target.live issuedRoot
  have frame := readFrame.trans syncFrame
  have keeperSeparate : directory.file (.walSegment first) ≠ directory.file .stagedWalBoundary ∧
      directory.file (.walSegment first) ≠ directory.file .walBoundary := by
    constructor <;> intro equal <;> have impossible := DiskDirectory.walSegment_exclusive equal.symm <;>
      obtain ⟨_, same⟩ := impossible <;> cases same
  have keeperFinal := frame.stored (.inr ⟨DiskFile.walSegment first, rfl⟩)
    ((renameFrame moved).stored keeperSeparate keeperStored)
  have markerFinal := frame.stored (.inr ⟨DiskFile.walBoundary, rfl⟩)
    (show (storage renamed).files.Stored (directory.file .walBoundary) markerBytes from
      ⟨markerInode, markerNamed, markerBytesAfterRename.trans durable⟩)
  have scratchGone := (frame _ (.inr ⟨DiskFile.stagedWalBoundary, rfl⟩)).1.trans detached
  exact ⟨keeperFinal, markerFinal, nonempty, fun names allowed =>
    ⟨settled names allowed (.walSegment first), settled names allowed .walBoundary,
      (settled names allowed .stagedWalBoundary).trans scratchGone⟩⟩

end Alvoki.Storage.DiskSession
