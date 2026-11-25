import Alvoki.Storage.Disk.NativeCheckpointFsyncEffects
import Alvoki.Storage.Disk.NativeWalStage

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting
open WAL.Boundary (WalInodeImage)

/-- Local storage law for a successful regular-file fsync on a literal
handle. The observed file sync preserves the namespace and live bytes. -/
abbrev RawSyncCalls.FileReturnEffect {heap image : Type} {directory : DiskDirectory}
    (calls : RawSyncCalls heap) (view : OpenCloseHeapView heap image) (inodes : heap → WalInodeImage)
    {runs : heap → RunUnlinkImage} (observe : ∀ heap, RunDirectoryInodeView directory (inodes heap) (runs heap))
    (path : FilePath) (handle : IO.FS.Handle) (issued reached : heap) : Prop :=
  calls.fsync handle issued = .ok () reached →
    let inode := (view.descriptors issued).inode (view.handle issued handle).2.1.description
    (observe issued).visible path = some inode ∧
    inodes reached = (inodes issued).completeFileSync inode ∧
    (observe reached).visible = (observe issued).visible ∧
    (observe reached).crashBindings = (observe issued).crashBindings

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
    (keeperEffect : ∀ after, calls.FileReturnEffect view inodes observe (directory.file (.walSegment first))
      keeperHandle staged after)
    (markerEffect : calls.FileReturnEffect view inodes observe (directory.file .stagedWalBoundary)
      markerHandle consumed reached)
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

/-- The keeper handle used by the successful grouped barrier supplies
the same live inode and bytes at its return. The two file fsyncs preserve
visible bytes. Consuming the pending cell needs its own local frame. -/
theorem RawSyncCalls.groupedKeeperVisible {heap image : Type} (calls : RawSyncCalls heap)
    {directory : DiskDirectory} {files : DiskTable.OpenSyncFiles}
    (cache : OpenSyncCacheRefs files directory.path) (view : OpenCloseHeapView heap image) {first : Nat}
    {staged consumed reached : heap} {keeperHandle markerHandle : IO.FS.Handle}
    (keeperRoute : calls.syncPath directory.path (directory.file (.walSegment first))
      cache.directory cache.active cache.pending staged = calls.fsync keeperHandle staged)
    (markerRoute : calls.syncPath directory.path (directory.file .stagedWalBoundary)
      cache.directory cache.active cache.pending (reachedState (calls.fsync keeperHandle staged)) =
        calls.fsync markerHandle consumed)
    (grouped : calls.group directory.path cache.directory cache.active cache.pending
      #[directory.file (.walSegment first), directory.file .stagedWalBoundary] staged = .ok () reached)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ heap, RunDirectoryInodeView directory (inodes heap) (runs heap))
    (keeperEffect : ∀ after, calls.FileReturnEffect view inodes observe (directory.file (.walSegment first))
      keeperHandle staged after)
    (markerEffect : calls.FileReturnEffect view inodes observe (directory.file .stagedWalBoundary)
      markerHandle consumed reached)
    (consumeKeeps : let inode := (view.descriptors staged).inode (view.handle staged keeperHandle).2.1.description
      let before := reachedState (calls.fsync keeperHandle staged)
      (observe consumed).visible (directory.file (.walSegment first)) =
        (observe before).visible (directory.file (.walSegment first)) ∧
      (inodes consumed).visible inode = (inodes before).visible inode) :
    let inode := (view.descriptors staged).inode (view.handle staged keeperHandle).2.1.description
    (observe reached).visible (directory.file (.walSegment first)) = some inode ∧
    (inodes reached).visible inode = (inodes staged).visible inode := by
  intro inode
  obtain ⟨keeperReturned, markerReturned⟩ := calls.groupedFileReturns cache keeperRoute markerRoute grouped
  obtain ⟨keeperNamed, keeperSynced, keeperNames, _⟩ := keeperEffect _ keeperReturned
  obtain ⟨_, markerSynced, markerNames, _⟩ := markerEffect markerReturned
  have keeperVisible := congrArg (fun image => image.visible inode) keeperSynced
  have markerVisible := congrArg (fun image => image.visible inode) markerSynced
  exact ⟨(congrFun markerNames _).trans (consumeKeeps.1.trans ((congrFun keeperNames _).trans keeperNamed)),
    markerVisible.trans (consumeKeeps.2.trans keeperVisible)⟩

/-- Use the actual cached routes after append and stage. The keeper
payload is carried from the append return. The staged marker's payload
passes through the first fsync and the reached pending-cell removal. -/
theorem RawSyncCalls.groupedStorageFromStaging {heap image : Type} (calls : RawSyncCalls heap)
    {directory : DiskDirectory} {files : DiskTable.OpenSyncFiles}
    (cache : OpenSyncCacheRefs files directory.path) (view : OpenCloseHeapView heap image) {first count : Nat}
    {appended staged consumed reached : heap} {keeperHandle markerHandle : IO.FS.Handle}
    (activeKeeper : view.active appended cache.active = some (directory.file (.walSegment first), keeperHandle))
    (keeperMiss : (view.pending appended cache.pending).find?
      (fun entry => entry.1 == directory.file (.walSegment first)) = none)
    (remembered : view.literalCacheAt staged cache.directory cache.active cache.pending =
      (view.literalCacheAt appended cache.directory cache.active cache.pending).remember
        (directory.file .stagedWalBoundary) markerHandle)
    (loadedKeeper : calls.readPending cache.pending staged = .ok (view.pending staged cache.pending) staged)
    (loadedActive : calls.readActive cache.active staged = .ok (view.active staged cache.active) staged)
    (loadedMarker : let atKeeper := reachedState (calls.fsync keeperHandle staged)
      calls.readPending cache.pending atKeeper = .ok (view.pending staged cache.pending) atKeeper)
    (removed : calls.setPending cache.pending
      ((view.pending staged cache.pending).filter (fun entry => entry.1 != directory.file .stagedWalBoundary))
      (reachedState (calls.fsync keeperHandle staged)) = .ok () consumed)
    (grouped : calls.group directory.path cache.directory cache.active cache.pending
      #[directory.file (.walSegment first), directory.file .stagedWalBoundary] staged = .ok () reached)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ heap, RunDirectoryInodeView directory (inodes heap) (runs heap))
    (keeperTarget : RawFsyncTarget view appended staged keeperHandle)
    (markerTarget : RawFsyncTarget view staged consumed markerHandle)
    {keeperInode markerInode : Nat} {priorBytes bytes : ByteArray}
    (keeperSelected : (view.handle appended keeperHandle).1.inode
      (view.handle appended keeperHandle).2.1.description = keeperInode)
    (markerSelected : (view.handle staged markerHandle).1.inode
      (view.handle staged markerHandle).2.1.description = markerInode)
    (appendBytes : (inodes appended).visible keeperInode = priorBytes ++ bytes)
    (keptByStage : (inodes staged).visible keeperInode = (inodes appended).visible keeperInode)
    (stagedBytes : ∃ inode, (observe staged).visible (directory.file .stagedWalBoundary) = some inode ∧
      (inodes staged).visible inode = WAL.Boundary.encode count.toUInt64)
    (keptByConsume : let afterKeeper := reachedState (calls.fsync keeperHandle staged)
      (observe consumed).visible (directory.file .stagedWalBoundary) =
        (observe afterKeeper).visible (directory.file .stagedWalBoundary) ∧
      (inodes consumed).visible markerInode = (inodes afterKeeper).visible markerInode)
    (keeperEffect : ∀ after, calls.FileReturnEffect view inodes observe (directory.file (.walSegment first))
      keeperHandle staged after)
    (markerEffect : calls.FileReturnEffect view inodes observe (directory.file .stagedWalBoundary)
      markerHandle consumed reached)
    (distinct : keeperInode ≠ markerInode) {footprint : FilePath → Prop}
    (consumeFrame : (observe (reachedState (calls.fsync keeperHandle staged))).storageObservation.Frames
      (fun path => path = directory.file (.walSegment first) ∨ footprint path) (observe consumed).storageObservation)
    (unrelated : ∀ path, footprint path → ∀ inode, (observe staged).storageObservation.files.names path = some inode →
      inode ≠ keeperInode ∧ inode ≠ markerInode) :
    (observe reached).storageObservation.files.Stored (directory.file (.walSegment first)) (priorBytes ++ bytes) ∧
    (observe reached).storageObservation.files.Stored (directory.file .stagedWalBoundary)
      (WAL.Boundary.encode count.toUInt64) ∧
    (observe staged).storageObservation.Frames footprint (observe reached).storageObservation := by
  obtain ⟨keeperRoute, markerRoute, _⟩ :=
    calls.groupedFromStaging cache view activeKeeper keeperMiss remembered loadedKeeper loadedActive loadedMarker removed
  obtain ⟨keeperReturned, markerReturned⟩ := calls.groupedFileReturns cache keeperRoute markerRoute grouped
  obtain ⟨_, syncedKeeper, keptNames, _⟩ := keeperEffect _ keeperReturned
  have markerAtIssue := (markerEffect markerReturned).1
  rw [markerTarget.inode, markerSelected] at markerAtIssue
  obtain ⟨stagedInode, namedStage, payload⟩ := stagedBytes
  have same := Option.some.inj (markerAtIssue.symm.trans
    (keptByConsume.1.trans ((congrFun keptNames _).trans namedStage)))
  subst stagedInode
  have sameBytes := congrArg (fun image => image.visible markerInode) syncedKeeper
  exact calls.groupedReturnedStorage cache view keeperRoute markerRoute grouped inodes runs observe keeperTarget markerTarget
    keeperSelected markerSelected (keptByStage.trans appendBytes) (keptByConsume.2.trans (sameBytes.trans payload))
    keeperEffect markerEffect distinct consumeFrame unrelated

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

/-- Carry the live keeper through the publication tail and the actual
ready phase store. These local frames concern the named inode's visible
bytes, in addition to the separate durable publication guarantees. -/
theorem RawSyncCalls.publishedKeeperVisible {heap : Type} (calls : RawSyncCalls heap)
    {directory : DiskDirectory} {files : DiskTable.OpenSyncFiles}
    (cache : OpenSyncCacheRefs files directory.path) {first inode : Nat} {payload : ByteArray}
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit)
    (names : heap → FilePath → Option Nat) (visible : heap → Nat → ByteArray)
    {phase : IO.Ref (Phase Installed)} {next : Installed} {grouped renamed issued synced ready : heap}
    {root : IO.FS.Handle}
    (bound : names grouped (directory.file (.walSegment first)) = some inode)
    (bytes : visible grouped inode = payload)
    (moved : rename (directory.file .stagedWalBoundary) (directory.file .walBoundary) grouped = .ok () renamed)
    (loaded : calls.readDirectory cache.directory renamed = .ok (some root) issued)
    (returned : calls.fsync root issued = .ok () synced)
    (installed : set phase (.ready next) synced = .ok () ready)
    (renameKeeps : rename (directory.file .stagedWalBoundary) (directory.file .walBoundary) grouped = .ok () renamed →
      names renamed (directory.file (.walSegment first)) = names grouped (directory.file (.walSegment first)) ∧
      visible renamed inode = visible grouped inode)
    (loadKeeps : calls.readDirectory cache.directory renamed = .ok (some root) issued →
      names issued (directory.file (.walSegment first)) = names renamed (directory.file (.walSegment first)) ∧
      visible issued inode = visible renamed inode)
    (syncKeeps : calls.fsync root issued = .ok () synced →
      names synced (directory.file (.walSegment first)) = names issued (directory.file (.walSegment first)) ∧
      visible synced inode = visible issued inode)
    (installKeeps : set phase (.ready next) synced = .ok () ready →
      names ready (directory.file (.walSegment first)) = names synced (directory.file (.walSegment first)) ∧
      visible ready inode = visible synced inode) :
    names ready (directory.file (.walSegment first)) = some inode ∧ visible ready inode = payload := by
  obtain ⟨renameName, renameBytes⟩ := renameKeeps moved
  obtain ⟨loadName, loadBytes⟩ := loadKeeps loaded
  obtain ⟨syncName, syncBytes⟩ := syncKeeps returned
  obtain ⟨installName, installBytes⟩ := installKeeps installed
  exact ⟨installName.trans (syncName.trans (loadName.trans (renameName.trans bound))),
    installBytes.trans (syncBytes.trans (loadBytes.trans (renameBytes.trans bytes)))⟩

end Alvoki.Storage.DiskSession
