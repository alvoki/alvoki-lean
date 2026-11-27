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
visible bytes and crash names. Consuming the pending cell needs its own
local frame for the keeper path. -/
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
      (observe before).storageObservation.Frames (· = directory.file (.walSegment first))
        (observe consumed).storageObservation ∧
      (inodes consumed).visible inode = (inodes before).visible inode) :
    let inode := (view.descriptors staged).inode (view.handle staged keeperHandle).2.1.description
    (observe reached).visible (directory.file (.walSegment first)) = some inode ∧
    (inodes reached).visible inode = (inodes staged).visible inode ∧
    ∀ names ∈ (observe reached).crashBindings, ∃ prior ∈ (observe staged).crashBindings,
      names (directory.file (.walSegment first)) = prior (directory.file (.walSegment first)) := by
  intro inode
  obtain ⟨keeperReturned, markerReturned⟩ := calls.groupedFileReturns cache keeperRoute markerRoute grouped
  obtain ⟨keeperNamed, keeperSynced, keeperNames, keeperCrash⟩ := keeperEffect _ keeperReturned
  obtain ⟨_, markerSynced, markerNames, markerCrash⟩ := markerEffect markerReturned
  have keeperVisible := congrArg (fun image => image.visible inode) keeperSynced
  have markerVisible := congrArg (fun image => image.visible inode) markerSynced
  have sameName := (consumeKeeps.1.visible _ rfl).1
  refine ⟨(congrFun markerNames _).trans (sameName.trans ((congrFun keeperNames _).trans keeperNamed)),
    markerVisible.trans (consumeKeeps.2.trans keeperVisible), ?_⟩
  intro names survives
  have atConsumption : names ∈ (observe consumed).crashBindings := markerCrash ▸ survives
  obtain ⟨prior, possible, same⟩ := consumeKeeps.1.survivors names atConsumption
  change prior ∈ (observe (reachedState (calls.fsync keeperHandle staged))).crashBindings at possible
  exact ⟨prior, keeperCrash ▸ possible, same _ rfl⟩

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

/-- Local effects of the callbacks issued by the keeper append. A hit
must already be clean. The open, write, flush and active-reference store
are separate from either of the later file barriers. -/
structure RawWalAppendCalls.KeeperEffects {heap image : Type} (calls : RawWalAppendCalls heap)
    (view : OpenCloseHeapView heap image) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (path : FilePath) (bytes : ByteArray) (entry reached : heap)
    (names : heap → FilePath → Option Nat) (visible : heap → Nat → ByteArray)
    (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray) (keeper : Nat) : Prop where
  loaded : calls.getActive active entry = .ok (view.active entry active) entry
  cleanCached : ∀ handle, view.active entry active = some (path, handle) →
    inode handle = keeper ∧ buffered entry handle = ByteArray.empty
  openedExisting : ∀ {handle opened}, calls.openAppend path entry = .ok handle opened →
    inode handle = keeper ∧ names opened path = some keeper ∧ visible opened keeper = visible entry keeper ∧
    buffered opened handle = ByteArray.empty
  write : ∀ {handle before after}, calls.write handle bytes before = .ok () after →
    names after path = names before path ∧
    visible after (inode handle) ++ buffered after handle =
      (visible before (inode handle) ++ buffered before handle) ++ bytes
  flush : ∀ {handle before after}, calls.flush handle before = .ok () after →
    names after path = names before path ∧ visible after (inode handle) = visible before (inode handle) ++ buffered before handle ∧
    buffered after handle = ByteArray.empty
  store : ∀ {handle before}, calls.setActive active (some (path, handle)) before = .ok () reached →
    view.active reached active = some (path, handle) ∧ names reached path = names before path ∧
    visible reached (inode handle) = visible before (inode handle) ∧ buffered reached handle = buffered before handle

/-- The marker's exclusive create starts empty. The cache and the
keeper's live bytes are framed along the separate staging callbacks. -/
structure RawWalStageCalls.MarkerEffects {heap image : Type} (calls : RawWalStageCalls heap)
    {directory : DiskDirectory} {files : DiskTable.OpenSyncFiles} (cache : OpenSyncCacheRefs files directory.path)
    (view : OpenCloseHeapView heap image) (bytes : ByteArray) (entry reached : heap)
    (names : heap → FilePath → Option Nat) (visible : heap → Nat → ByteArray)
    (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray) (keeper : Nat) : Prop where
  first : ∀ {file opened}, calls.tryCreate (directory.file .stagedWalBoundary) entry = .ok (.ok file) opened →
    names opened (directory.file .stagedWalBoundary) = some (inode file) ∧
    visible opened (inode file) = ByteArray.empty ∧ buffered opened file = ByteArray.empty
  retry : ∀ {file before opened}, calls.create (directory.file .stagedWalBoundary) before = .ok file opened →
    names opened (directory.file .stagedWalBoundary) = some (inode file) ∧
    visible opened (inode file) = ByteArray.empty ∧ buffered opened file = ByteArray.empty
  acquired : ∀ {file opened}, calls.acquire (directory.file .stagedWalBoundary) entry = .ok file opened →
    view.literalCacheAt opened cache.directory cache.active cache.pending =
      view.literalCacheAt entry cache.directory cache.active cache.pending ∧ visible opened keeper = visible entry keeper
  write : ∀ {file before after}, calls.write file bytes before = .ok () after →
    view.literalCacheAt after cache.directory cache.active cache.pending =
      view.literalCacheAt before cache.directory cache.active cache.pending ∧ visible after keeper = visible before keeper ∧
    names after (directory.file .stagedWalBoundary) = names before (directory.file .stagedWalBoundary) ∧
    visible after (inode file) ++ buffered after file = (visible before (inode file) ++ buffered before file) ++ bytes
  flush : ∀ {file before after}, calls.flush file before = .ok () after →
    view.literalCacheAt after cache.directory cache.active cache.pending =
      view.literalCacheAt before cache.directory cache.active cache.pending ∧ visible after keeper = visible before keeper ∧
    names after (directory.file .stagedWalBoundary) = names before (directory.file .stagedWalBoundary) ∧
    visible after (inode file) = visible before (inode file) ++ buffered before file
  store : ∀ {file before}, calls.remember cache.pending (pushPending (directory.file .stagedWalBoundary) file) before =
      .ok () reached →
    view.literalCacheAt reached cache.directory cache.active cache.pending =
      (view.literalCacheAt before cache.directory cache.active cache.pending).remember
        (directory.file .stagedWalBoundary) file ∧ visible reached keeper = visible before keeper ∧
    names reached (directory.file .stagedWalBoundary) = names before (directory.file .stagedWalBoundary) ∧
    visible reached (inode file) = visible before (inode file)

/-- Literal cache reads and pending consumption that route the two file
syncs, in their issued order, on both success and failure. -/
structure RawSyncCalls.GroupedFileRoute {heap image : Type} (calls : RawSyncCalls heap)
    {directory : DiskDirectory} {files : DiskTable.OpenSyncFiles} (cache : OpenSyncCacheRefs files directory.path)
    (view : OpenCloseHeapView heap image) (first : Nat) (appended staged consumed : heap)
    (keeperHandle markerHandle : IO.FS.Handle) (keeper marker : Nat) : Prop where
  keeperMiss : (view.pending appended cache.pending).find? (fun entry => entry.1 == directory.file (.walSegment first)) = none
  loadedKeeper : calls.readPending cache.pending staged = .ok (view.pending staged cache.pending) staged
  loadedActive : calls.readActive cache.active staged = .ok (view.active staged cache.active) staged
  loadedMarker : let afterKeeper := reachedState (calls.fsync keeperHandle staged)
    calls.readPending cache.pending afterKeeper = .ok (view.pending staged cache.pending) afterKeeper
  removed : calls.setPending cache.pending
    ((view.pending staged cache.pending).filter (fun entry => entry.1 != directory.file .stagedWalBoundary))
    (reachedState (calls.fsync keeperHandle staged)) = .ok () consumed
  keeperTarget : RawFsyncTarget view appended staged keeperHandle
  markerTarget : RawFsyncTarget view staged consumed markerHandle
  keeperSelected : (view.handle appended keeperHandle).1.inode (view.handle appended keeperHandle).2.1.description = keeper
  markerSelected : (view.handle staged markerHandle).1.inode (view.handle staged markerHandle).2.1.description = marker
  distinct : keeper ≠ marker

/-- Primitive observations at the literal handles chosen by the two
file barriers. Consuming the pending reference has a separate frame
because releasing entries can change the reached heap. -/
structure RawSyncCalls.GroupedFileEffects {heap image : Type} (calls : RawSyncCalls heap)
    {directory : DiskDirectory} {files : DiskTable.OpenSyncFiles} (cache : OpenSyncCacheRefs files directory.path)
    (view : OpenCloseHeapView heap image) (inodes : heap → WalInodeImage) {runs : heap → RunUnlinkImage}
    (observe : ∀ heap, RunDirectoryInodeView directory (inodes heap) (runs heap)) (first : Nat)
    (appended staged consumed reached : heap) (keeperHandle markerHandle : IO.FS.Handle)
    (keeper marker : Nat)
    extends calls.GroupedFileRoute cache view first appended staged consumed keeperHandle markerHandle keeper marker where
  keeperEffect : ∀ after, calls.FileReturnEffect view inodes observe (directory.file (.walSegment first)) keeperHandle staged after
  markerEffect : calls.FileReturnEffect view inodes observe (directory.file .stagedWalBoundary) markerHandle consumed reached
  consumeKeeper : let afterKeeper := reachedState (calls.fsync keeperHandle staged)
    (observe afterKeeper).storageObservation.Frames (· = directory.file (.walSegment first)) (observe consumed).storageObservation ∧
      (inodes consumed).visible keeper = (inodes afterKeeper).visible keeper
  consumeMarker : let afterKeeper := reachedState (calls.fsync keeperHandle staged)
    (observe consumed).visible (directory.file .stagedWalBoundary) = (observe afterKeeper).visible (directory.file .stagedWalBoundary) ∧
      (inodes consumed).visible marker = (inodes afterKeeper).visible marker

private theorem stagedPublicationTargets {heap image : Type}
    {directory : DiskDirectory} {files : DiskTable.OpenSyncFiles}
    (cache : OpenSyncCacheRefs files directory.path) (view : OpenCloseHeapView heap image)
    (appender : RawWalAppendCalls heap) (stager : RawWalStageCalls heap)
    (inodes : heap → WalInodeImage) {runs : heap → RunUnlinkImage}
    (observe : ∀ heap, RunDirectoryInodeView directory (inodes heap) (runs heap))
    (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray)
    {first count keeper : Nat} {entry appended staged : heap} {priorBytes bytes : ByteArray}
    (priorBinding : (observe entry).visible (directory.file (.walSegment first)) = some keeper)
    (priorVisible : (inodes entry).visible keeper = priorBytes)
    (wrote : appender.run cache.active (directory.file (.walSegment first)) bytes entry = .ok () appended)
    (stagedMarker : stager.run cache.pending (directory.file .stagedWalBoundary)
      (WAL.Boundary.encode count.toUInt64) appended = .ok () staged)
    (appendEffects : appender.KeeperEffects view cache.active (directory.file (.walSegment first)) bytes entry appended
      (fun heap => (observe heap).visible) (fun heap => (inodes heap).visible) inode buffered keeper)
    (stageEffects : (observe appended).visible (directory.file (.walSegment first)) = some keeper →
      stager.MarkerEffects cache view (WAL.Boundary.encode count.toUInt64) appended staged
        (fun heap => (observe heap).visible) (fun heap => (inodes heap).visible) inode buffered keeper) :
    ∃ keeperHandle markerHandle,
      (observe appended).visible (directory.file (.walSegment first)) = some keeper ∧
      inode keeperHandle = keeper ∧
      view.active appended cache.active = some (directory.file (.walSegment first), keeperHandle) ∧
      view.literalCacheAt staged cache.directory cache.active cache.pending =
        (view.literalCacheAt appended cache.directory cache.active cache.pending).remember
          (directory.file .stagedWalBoundary) markerHandle ∧
      (inodes appended).visible keeper = priorBytes ++ bytes ∧
      (inodes staged).visible keeper = (inodes appended).visible keeper ∧
      ∃ ino, (observe staged).visible (directory.file .stagedWalBoundary) = some ino ∧
        (inodes staged).visible ino = WAL.Boundary.encode count.toUInt64 := by
  let names := fun heap => (observe heap).visible
  let visible := fun heap => (inodes heap).visible
  obtain ⟨keeperHandle, active, keeperIdentity, keeperNamed, appendBytes, _⟩ := appender.appendsVisible view names inode visible buffered
    priorBinding appendEffects.loaded wrote appendEffects.cleanCached appendEffects.openedExisting
    appendEffects.write appendEffects.flush appendEffects.store
  change (inodes appended).visible keeper = (inodes entry).visible keeper ++ bytes at appendBytes
  rw [priorVisible] at appendBytes
  have stageEffects := stageEffects keeperNamed
  obtain ⟨markerHandle, remembered, keptByStage, _⟩ := stager.retainsStaged view
    (fun heap => visible heap keeper) names inode stagedMarker
    (fun opened => ⟨(stageEffects.acquired opened).1, (stageEffects.acquired opened).2,
      stager.acquireBinds _ names inode opened (fun created => (stageEffects.first created).1)
        (fun created => (stageEffects.retry created).1)⟩)
    (fun wrote => ⟨(stageEffects.write wrote).1, (stageEffects.write wrote).2.1, (stageEffects.write wrote).2.2.1⟩)
    (fun flushed => ⟨(stageEffects.flush flushed).1, (stageEffects.flush flushed).2.1, (stageEffects.flush flushed).2.2.1⟩)
    (fun saved => ⟨(stageEffects.store saved).1, (stageEffects.store saved).2.1, (stageEffects.store saved).2.2.1⟩)
  have stagedBytes := stager.stagesVisible names inode visible buffered stagedMarker stageEffects.first stageEffects.retry
    (fun wrote => (stageEffects.write wrote).2.2) (fun flushed => (stageEffects.flush flushed).2.2)
    (fun saved => (stageEffects.store saved).2.2)
  exact ⟨keeperHandle, markerHandle, keeperNamed, keeperIdentity, active, remembered, appendBytes, keptByStage, stagedBytes⟩

/-- Derive the durable payloads from the actual append, staging and
grouped file-sync returns. The live keeper at the group return uses
its own byte frame and remains available for the next append. -/
theorem RawSyncCalls.groupedStorageFromPublication {heap image : Type} (calls : RawSyncCalls heap)
    {directory : DiskDirectory} {files : DiskTable.OpenSyncFiles}
    (cache : OpenSyncCacheRefs files directory.path) (view : OpenCloseHeapView heap image)
    (appender : RawWalAppendCalls heap) (stager : RawWalStageCalls heap)
    (inodes : heap → WalInodeImage) {runs : heap → RunUnlinkImage}
    (observe : ∀ heap, RunDirectoryInodeView directory (inodes heap) (runs heap))
    (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray)
    {first count keeper : Nat} {entry appended staged reached : heap} {priorBytes bytes : ByteArray}
    (priorBinding : (observe entry).visible (directory.file (.walSegment first)) = some keeper)
    (priorVisible : (inodes entry).visible keeper = priorBytes)
    (wrote : appender.run cache.active (directory.file (.walSegment first)) bytes entry = .ok () appended)
    (stagedMarker : stager.run cache.pending (directory.file .stagedWalBoundary)
      (WAL.Boundary.encode count.toUInt64) appended = .ok () staged)
    (grouped : calls.group directory.path cache.directory cache.active cache.pending
      #[directory.file (.walSegment first), directory.file .stagedWalBoundary] staged = .ok () reached)
    (appendEffects : appender.KeeperEffects view cache.active (directory.file (.walSegment first)) bytes entry appended
      (fun heap => (observe heap).visible) (fun heap => (inodes heap).visible) inode buffered keeper)
    (stageEffects : (observe appended).visible (directory.file (.walSegment first)) = some keeper →
      stager.MarkerEffects cache view (WAL.Boundary.encode count.toUInt64) appended staged
        (fun heap => (observe heap).visible) (fun heap => (inodes heap).visible) inode buffered keeper)
    (barrierEffects : ∀ {keeperHandle markerHandle},
      (observe appended).visible (directory.file (.walSegment first)) = some keeper →
      inode keeperHandle = keeper →
      view.active appended cache.active = some (directory.file (.walSegment first), keeperHandle) →
      view.literalCacheAt staged cache.directory cache.active cache.pending =
        (view.literalCacheAt appended cache.directory cache.active cache.pending).remember
          (directory.file .stagedWalBoundary) markerHandle →
      ∃ consumed, calls.GroupedFileEffects cache view inodes observe first appended staged consumed reached
        keeperHandle markerHandle keeper (inode markerHandle)) :
    (observe reached).storageObservation.files.Stored (directory.file (.walSegment first)) (priorBytes ++ bytes) ∧
    (observe reached).storageObservation.files.Stored (directory.file .stagedWalBoundary)
      (WAL.Boundary.encode count.toUInt64) ∧
    (observe reached).visible (directory.file (.walSegment first)) = some keeper ∧
    (inodes reached).visible keeper = priorBytes ++ bytes ∧
    (∀ inode, (observe reached).visible (directory.file .stagedWalBoundary) = some inode →
      (inodes reached).visible inode = WAL.Boundary.encode count.toUInt64) ∧
    ∀ names ∈ (observe reached).crashBindings, ∃ prior ∈ (observe staged).crashBindings,
      names (directory.file (.walSegment first)) = prior (directory.file (.walSegment first)) := by
  obtain ⟨_, markerHandle, keeperNamed, keeperIdentity, active, remembered, appendBytes, keptByStage, stagedBytes⟩ :=
    stagedPublicationTargets cache view appender stager inodes observe inode buffered priorBinding priorVisible
      wrote stagedMarker appendEffects stageEffects
  obtain ⟨consumed, effects⟩ := barrierEffects keeperNamed keeperIdentity active remembered
  obtain ⟨keeperStored, markerStored, _⟩ := calls.groupedStorageFromStaging cache view active effects.keeperMiss remembered
    effects.loadedKeeper effects.loadedActive effects.loadedMarker effects.removed grouped inodes runs observe
    effects.keeperTarget effects.markerTarget effects.keeperSelected effects.markerSelected appendBytes keptByStage stagedBytes
    effects.consumeMarker effects.keeperEffect effects.markerEffect effects.distinct (footprint := fun _ => False)
    (effects.consumeKeeper.1.weaken fun _ selected => selected.elim id False.elim)
    (fun _ impossible => False.elim impossible)
  obtain ⟨keeperRoute, markerRoute, _⟩ := calls.groupedFromStaging cache view active effects.keeperMiss remembered
    effects.loadedKeeper effects.loadedActive effects.loadedMarker effects.removed
  have keeperInode := effects.keeperTarget.inode.trans effects.keeperSelected
  have consumedKeeps := effects.consumeKeeper.2
  rw [← keeperInode] at consumedKeeps
  obtain ⟨named, liveBytes, survivors⟩ := calls.groupedKeeperVisible cache view keeperRoute markerRoute grouped inodes runs observe
    effects.keeperEffect effects.markerEffect ⟨effects.consumeKeeper.1, consumedKeeps⟩
  rw [keeperInode] at named liveBytes
  obtain ⟨_, markerReturned⟩ := calls.groupedFileReturns cache keeperRoute markerRoute grouped
  obtain ⟨markerNamed, markerSynced, namesAtSync, _⟩ := effects.markerEffect markerReturned
  let markerInode := (view.descriptors consumed).inode (view.handle consumed markerHandle).2.1.description
  have markerAtGroup : (observe reached).visible (directory.file .stagedWalBoundary) = some markerInode :=
    (congrFun namesAtSync _).trans markerNamed
  have syncedMarker :
      (inodes reached).crashBytes markerInode = [(inodes reached).visible markerInode] := by
    rw [markerSynced]
    simp [markerInode, WalInodeImage.completeFileSync, WalInodeImage.reportFileSync]
  have liveMarker (inode) (bound : (observe reached).visible (directory.file .stagedWalBoundary) = some inode) :
      (inodes reached).visible inode = WAL.Boundary.encode count.toUInt64 := by
    obtain ⟨recorded, reachedName, certified⟩ := markerStored
    have same := Option.some.inj (reachedName.symm.trans bound)
    have sampled := Option.some.inj (bound.symm.trans markerAtGroup)
    subst recorded
    subst inode
    exact (List.cons.inj (syncedMarker.symm.trans certified)).1
  exact ⟨keeperStored, markerStored, named, liveBytes.trans (keptByStage.trans appendBytes), liveMarker, survivors⟩

/-- Local effects of one reached file fsync, including a reported
failure. The actual return selects the heap. A successful call settles
the live payload, while an error can leave other reported byte choices. -/
structure RawSyncCalls.FileReachedEffect {heap image : Type} (calls : RawSyncCalls heap)
    (view : OpenCloseHeapView heap image) (inodes : heap → WalInodeImage)
    {directory : DiskDirectory} {runs : heap → RunUnlinkImage}
    (observe : ∀ heap, RunDirectoryInodeView directory (inodes heap) (runs heap))
    (path : FilePath) (handle : IO.FS.Handle) (issued : heap) (choices : List ByteArray) : Prop where
  named : (observe issued).visible path =
    some ((view.descriptors issued).inode (view.handle issued handle).2.1.description)
  written : inodes (reachedState (calls.fsync handle issued)) =
    (inodes issued).reportFileSync ((view.descriptors issued).inode (view.handle issued handle).2.1.description) choices
  names : (observe (reachedState (calls.fsync handle issued))).visible = (observe issued).visible
  crashNames : (observe (reachedState (calls.fsync handle issued))).crashBindings = (observe issued).crashBindings
  completed : ∀ after, calls.fsync handle issued = .ok () after →
    choices = [(inodes issued).visible ((view.descriptors issued).inode (view.handle issued handle).2.1.description)]

/-- Under the exact cached dispatch, the grouped error's reached heap is
always the reached heap of the second file fsync. The diagnostic may
come from the first fsync even when the second reports its own error. -/
private theorem groupedFailureReached {heap : Type} (calls : RawSyncCalls heap)
    {directory : DiskDirectory} {files : DiskTable.OpenSyncFiles}
    (cache : OpenSyncCacheRefs files directory.path) {first : Nat}
    {staged consumed reached : heap} {keeperHandle markerHandle : IO.FS.Handle} {cause : IO.Error}
    (keeper : calls.syncPath directory.path (directory.file (.walSegment first))
      cache.directory cache.active cache.pending staged = calls.fsync keeperHandle staged)
    (marker : calls.syncPath directory.path (directory.file .stagedWalBoundary)
      cache.directory cache.active cache.pending (reachedState (calls.fsync keeperHandle staged)) =
        calls.fsync markerHandle consumed)
    (failed : calls.group directory.path cache.directory cache.active cache.pending
      #[directory.file (.walSegment first), directory.file .stagedWalBoundary] staged = .error cause reached) :
    reachedState (calls.fsync markerHandle consumed) = reached := by
  rcases calls.groupedFileError cache keeper marker failed with ⟨_, _, _, reached, _⟩ | ⟨_, _, _, failed, _⟩
  · exact reached
  · rw [failed, reachedState]

/-- The two issued fsync effects and the intervening pending store on
the selected literal handles. On a keeper error the local filesystem
law retains the committed prefix in every reported byte choice. -/
def RawSyncCalls.GroupedFailureFileEffects {heap image : Type} (calls : RawSyncCalls heap)
    {directory : DiskDirectory} {files : DiskTable.OpenSyncFiles}
    (cache : OpenSyncCacheRefs files directory.path) (view : OpenCloseHeapView heap image)
    (inodes : heap → WalInodeImage) {runs : heap → RunUnlinkImage}
    (observe : ∀ heap, RunDirectoryInodeView directory (inodes heap) (runs heap))
    (first : Nat) (appended staged : heap) (keeperHandle markerHandle : IO.FS.Handle)
    (keeper scratch oldMarker : Nat) (priorBytes : ByteArray) : Prop :=
  ∃ consumed keeperChoices markerChoices,
    calls.GroupedFileRoute cache view first appended staged consumed keeperHandle markerHandle keeper scratch ∧
    calls.FileReachedEffect view inodes observe (directory.file (.walSegment first)) keeperHandle staged keeperChoices ∧
    calls.FileReachedEffect view inodes observe (directory.file .stagedWalBoundary) markerHandle consumed markerChoices ∧
    (∀ {err after}, calls.fsync keeperHandle staged = .error err after →
      keeperChoices ≠ [] ∧ ∀ payload ∈ keeperChoices, ∃ tail, payload = priorBytes ++ tail) ∧
    oldMarker ≠ keeper ∧ oldMarker ≠ scratch ∧
    let afterKeeper := reachedState (calls.fsync keeperHandle staged)
    (observe afterKeeper).storageObservation.Frames
      (fun path => path = directory.file (.walSegment first) ∨ path = directory.file .walBoundary)
      (observe consumed).storageObservation ∧
    (inodes consumed).visible keeper = (inodes afterKeeper).visible keeper ∧
    (inodes consumed).visible oldMarker = (inodes afterKeeper).visible oldMarker

/-- A failed grouped barrier skips publication. Both file fsyncs still
affect their issued inodes, and the marker's pending entry is consumed
at the heap reached by the first fsync. The surviving keeper contents
retain the old committed prefix, even if an error partially persisted
the append, and the canonical marker still selects the old prefix. -/
theorem RawSyncCalls.groupedFailurePreservesSelection {heap image : Type} (calls : RawSyncCalls heap)
    {directory : DiskDirectory} {files : DiskTable.OpenSyncFiles}
    (cache : OpenSyncCacheRefs files directory.path) (view : OpenCloseHeapView heap image)
    (appender : RawWalAppendCalls heap) (stager : RawWalStageCalls heap)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (inodes : heap → WalInodeImage) {runs : heap → RunUnlinkImage}
    (observe : ∀ heap, RunDirectoryInodeView directory (inodes heap) (runs heap))
    (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray)
    {first count keeper oldMarker : Nat} {entry appended staged reached : heap} {cause : IO.Error}
    {priorBytes bytes oldMarkerBytes : ByteArray}
    (priorBinding : (observe entry).visible (directory.file (.walSegment first)) = some keeper)
    (priorVisible : (inodes entry).visible keeper = priorBytes)
    (markerBinding : (observe entry).visible (directory.file .walBoundary) = some oldMarker)
    (markerDurable : (inodes entry).crashBytes oldMarker = [oldMarkerBytes])
    (markerLive : (inodes entry).visible oldMarker = oldMarkerBytes)
    (settledMarker : ∀ names ∈ (observe entry).crashBindings, names (directory.file .walBoundary) = some oldMarker)
    (settledKeeper : ∀ names ∈ (observe staged).crashBindings, names (directory.file (.walSegment first)) = some keeper)
    (prefixMarker : (observe entry).storageObservation.Frames (· = directory.file .walBoundary)
      (observe staged).storageObservation)
    (prefixKeepsMarker : (inodes staged).visible oldMarker = (inodes entry).visible oldMarker)
    (wrote : appender.run cache.active (directory.file (.walSegment first)) bytes entry = .ok () appended)
    (stagedMarker : stager.run cache.pending (directory.file .stagedWalBoundary)
      (WAL.Boundary.encode count.toUInt64) appended = .ok () staged)
    (grouped : calls.group directory.path cache.directory cache.active cache.pending
      #[directory.file (.walSegment first), directory.file .stagedWalBoundary] staged = .error cause reached)
    (appendEffects : appender.KeeperEffects view cache.active (directory.file (.walSegment first)) bytes entry appended
      (fun heap => (observe heap).visible) (fun heap => (inodes heap).visible) inode buffered keeper)
    (stageEffects : (observe appended).visible (directory.file (.walSegment first)) = some keeper →
      stager.MarkerEffects cache view (WAL.Boundary.encode count.toUInt64) appended staged
        (fun heap => (observe heap).visible) (fun heap => (inodes heap).visible) inode buffered keeper)
    (barrierEffects : ∀ {keeperHandle markerHandle},
      (observe appended).visible (directory.file (.walSegment first)) = some keeper →
      inode keeperHandle = keeper →
      view.active appended cache.active = some (directory.file (.walSegment first), keeperHandle) →
      view.literalCacheAt staged cache.directory cache.active cache.pending =
        (view.literalCacheAt appended cache.directory cache.active cache.pending).remember
          (directory.file .stagedWalBoundary) markerHandle →
      calls.GroupedFailureFileEffects cache view inodes observe first appended staged keeperHandle markerHandle
        keeper (inode markerHandle) oldMarker priorBytes) :
    WalSegmentCommit.commitBytesAt directory first bytes count (appender.run cache.active) (stager.run cache.pending)
      (calls.group directory.path cache.directory cache.active cache.pending) rename entry = .error cause reached ∧
    (observe reached).visible (directory.file .walBoundary) = some oldMarker ∧
    (inodes reached).crashBytes oldMarker = [oldMarkerBytes] ∧
    (inodes reached).visible oldMarker = oldMarkerBytes ∧
    (observe reached).visible (directory.file (.walSegment first)) = some keeper ∧
    (inodes reached).visible keeper = priorBytes ++ bytes ∧
    (inodes reached).crashBytes keeper ≠ [] ∧
    (∀ payload ∈ (inodes reached).crashBytes keeper, ∃ tail, payload = priorBytes ++ tail) ∧
    ∀ names ∈ (observe reached).crashBindings,
      names (directory.file .walBoundary) = some oldMarker ∧ names (directory.file (.walSegment first)) = some keeper := by
  have returned := calls.commitAfterStaging cache appender stager rename wrote stagedMarker
  dsimp only at returned
  rw [grouped] at returned
  obtain ⟨keeperHandle, markerHandle, keeperNamed, keeperIdentity, active, remembered, appendBytes, keptByStage, _⟩ :=
    stagedPublicationTargets cache view appender stager inodes observe inode buffered priorBinding priorVisible
      wrote stagedMarker appendEffects stageEffects
  obtain ⟨consumed, keeperChoices, markerChoices, route, keeperEffect, markerEffect, failedKeeper,
    markerApartKeeper, markerApartScratch, consumeFrame, consumeKeeper, consumeMarker⟩ :=
    barrierEffects keeperNamed keeperIdentity active remembered
  obtain ⟨keeperRoute, markerRoute, _⟩ := calls.groupedFromStaging cache view active route.keeperMiss remembered
    route.loadedKeeper route.loadedActive route.loadedMarker route.removed
  have reachedAt := groupedFailureReached calls cache keeperRoute markerRoute grouped
  let afterKeeper := reachedState (calls.fsync keeperHandle staged)
  have keeperTarget := route.keeperTarget.inode.trans route.keeperSelected
  have markerTarget := route.markerTarget.inode.trans route.markerSelected
  have keeperUpdate : inodes afterKeeper = (inodes staged).reportFileSync keeper keeperChoices := by
    simpa only [keeperTarget] using keeperEffect.written
  have markerUpdate : inodes reached = (inodes consumed).reportFileSync (inode markerHandle) markerChoices := by
    simpa only [reachedAt, markerTarget] using markerEffect.written
  have keeperBytes : (inodes staged).visible keeper = priorBytes ++ bytes := keptByStage.trans appendBytes
  have retained : keeperChoices ≠ [] ∧ ∀ payload ∈ keeperChoices, ∃ tail, payload = priorBytes ++ tail := by
    cases firstCall : calls.fsync keeperHandle staged with
    | error err after => exact failedKeeper firstCall
    | ok value after =>
      cases value
      have completed := keeperEffect.completed after firstCall
      rw [keeperTarget, keeperBytes] at completed
      rw [completed]
      exact ⟨by simp, fun payload member => ⟨bytes, List.mem_singleton.mp member⟩⟩
  let keeperPath := directory.file (.walSegment first)
  let markerPath := directory.file .walBoundary
  have keeperStaged : (observe staged).visible keeperPath = some keeper := by
    simpa only [keeperTarget] using keeperEffect.named
  have oldAtStage : (observe staged).visible markerPath = some oldMarker :=
    (prefixMarker.visible markerPath rfl).1.trans markerBinding
  have durableAtStage : (inodes staged).crashBytes oldMarker = [oldMarkerBytes] :=
    ((prefixMarker.visible markerPath rfl).2 _ markerBinding).trans markerDurable
  have keeperAtFirst : (observe afterKeeper).visible keeperPath = some keeper :=
    (congrFun keeperEffect.names keeperPath).trans keeperStaged
  have oldAtFirst : (observe afterKeeper).visible markerPath = some oldMarker :=
    (congrFun keeperEffect.names markerPath).trans oldAtStage
  have keeperAtConsume : (observe consumed).visible keeperPath = some keeper :=
    (consumeFrame.visible keeperPath (.inl rfl)).1.trans keeperAtFirst
  have oldAtConsume : (observe consumed).visible markerPath = some oldMarker :=
    (consumeFrame.visible markerPath (.inr rfl)).1.trans oldAtFirst
  have reachedNames : (observe reached).visible = (observe consumed).visible := by
    rw [← reachedAt]
    exact markerEffect.names
  have keeperDurableAtConsume : (inodes consumed).crashBytes keeper = keeperChoices := by
    refine ((consumeFrame.visible keeperPath (.inl rfl)).2 _ keeperAtFirst).trans ?_
    change (inodes afterKeeper).crashBytes keeper = keeperChoices
    simp [keeperUpdate, WalInodeImage.reportFileSync]
  have oldDurableAtConsume : (inodes consumed).crashBytes oldMarker = [oldMarkerBytes] := by
    refine ((consumeFrame.visible markerPath (.inr rfl)).2 _ oldAtFirst).trans ?_
    change (inodes afterKeeper).crashBytes oldMarker = [oldMarkerBytes]
    simp [keeperUpdate, WalInodeImage.reportFileSync, markerApartKeeper, durableAtStage]
  have oldDurable : (inodes reached).crashBytes oldMarker = [oldMarkerBytes] := by
    simp [markerUpdate, WalInodeImage.reportFileSync, markerApartScratch, oldDurableAtConsume]
  have keeperDurable : (inodes reached).crashBytes keeper = keeperChoices := by
    simp [markerUpdate, WalInodeImage.reportFileSync, route.distinct, keeperDurableAtConsume]
  have oldAtFirstBytes : (inodes afterKeeper).visible oldMarker = oldMarkerBytes := by
    rw [keeperUpdate]
    exact prefixKeepsMarker.trans markerLive
  have keeperAtFirstBytes : (inodes afterKeeper).visible keeper = priorBytes ++ bytes := by
    rw [keeperUpdate]
    exact keeperBytes
  have oldVisible : (inodes reached).visible oldMarker = oldMarkerBytes := by
    rw [markerUpdate]
    exact consumeMarker.trans oldAtFirstBytes
  have keeperVisible : (inodes reached).visible keeper = priorBytes ++ bytes := by
    rw [markerUpdate]
    exact consumeKeeper.trans keeperAtFirstBytes
  refine ⟨returned, (congrFun reachedNames markerPath).trans oldAtConsume, oldDurable, oldVisible,
    (congrFun reachedNames keeperPath).trans keeperAtConsume, keeperVisible, ?_, ?_, ?_⟩
  · rw [keeperDurable]
    exact retained.1
  · rw [keeperDurable]
    exact retained.2
  · intro names member
    have finalMaps : (observe reached).crashBindings = (observe consumed).crashBindings := by
      rw [← reachedAt]
      exact markerEffect.crashNames
    rw [finalMaps] at member
    obtain ⟨prior, atFirst, same⟩ := consumeFrame.survivors names member
    change prior ∈ (observe afterKeeper).crashBindings at atFirst
    have atStage : prior ∈ (observe staged).crashBindings := keeperEffect.crashNames ▸ atFirst
    obtain ⟨initial, atEntry, sameMarker⟩ := prefixMarker.survivors prior atStage
    exact ⟨(same markerPath (.inr rfl)).trans ((sameMarker markerPath rfl).trans (settledMarker initial atEntry)),
      (same keeperPath (.inl rfl)).trans (settledKeeper prior atStage)⟩

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

/-- Carry a named live inode through the publication tail and the
actual ready phase store. A rename can move the inode to its final name. -/
theorem RawSyncCalls.publishedFileVisible {heap : Type} (calls : RawSyncCalls heap)
    {directory : DiskDirectory} {files : DiskTable.OpenSyncFiles}
    (cache : OpenSyncCacheRefs files directory.path) {inode : Nat} {payload : ByteArray}
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit)
    (fromPath toPath : FilePath)
    (names : heap → FilePath → Option Nat) (visible : heap → Nat → ByteArray)
    {phase : IO.Ref (Phase Installed)} {next : Installed} {grouped renamed issued synced ready : heap}
    {root : IO.FS.Handle}
    (bound : names grouped fromPath = some inode)
    (bytes : visible grouped inode = payload)
    (moved : rename (directory.file .stagedWalBoundary) (directory.file .walBoundary) grouped = .ok () renamed)
    (loaded : calls.readDirectory cache.directory renamed = .ok (some root) issued)
    (returned : calls.fsync root issued = .ok () synced)
    (installed : set phase (.ready next) synced = .ok () ready)
    (renameKeeps : rename (directory.file .stagedWalBoundary) (directory.file .walBoundary) grouped = .ok () renamed →
      names renamed toPath = names grouped fromPath ∧
      visible renamed inode = visible grouped inode)
    (loadKeeps : calls.readDirectory cache.directory renamed = .ok (some root) issued →
      names issued toPath = names renamed toPath ∧
      visible issued inode = visible renamed inode)
    (syncKeeps : calls.fsync root issued = .ok () synced →
      names synced toPath = names issued toPath ∧
      visible synced inode = visible issued inode)
    (installKeeps : set phase (.ready next) synced = .ok () ready →
      names ready toPath = names synced toPath ∧
      visible ready inode = visible synced inode) :
    names ready toPath = some inode ∧ visible ready inode = payload := by
  obtain ⟨renameName, renameBytes⟩ := renameKeeps moved
  obtain ⟨loadName, loadBytes⟩ := loadKeeps loaded
  obtain ⟨syncName, syncBytes⟩ := syncKeeps returned
  obtain ⟨installName, installBytes⟩ := installKeeps installed
  exact ⟨installName.trans (syncName.trans (loadName.trans (renameName.trans bound))),
    installBytes.trans (syncBytes.trans (loadBytes.trans (renameBytes.trans bytes)))⟩

end Alvoki.Storage.DiskSession
