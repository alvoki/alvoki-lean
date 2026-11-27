import Alvoki.Storage.Disk.NativeLongKeeperSettlementHeap
import Alvoki.Storage.Disk.NativeLongKeeperPending
import Alvoki.Storage.Disk.NativeOpenReadyStorage
import Alvoki.Storage.Disk.NativeWalPublicationTail
import Alvoki.Storage.Disk.NativeRetainedOpenStorage

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair CheckpointPublication
open WAL.Boundary (WalInodeImage)

section Replacement

variable {heap : Type}

/-- An already synced staging inode becomes the keeper at the successful
rename. Loading the cached root carries the selected paths and scratch
name to the actual directory issue heap. That barrier settles the
children; the root's own name stays settled in its parent separately. -/
theorem NativeReadyStorage.afterKeeperReplacement
    (state : NativeReadyState)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    {stageIssued stageSynced renamed rootIssued reached : heap} {old replacement : Nat}
    (stageBinding : (observe stageIssued).files.names (state.session.directory.file .stagedWal) = some replacement)
    (stagedPrefix : visible stageIssued replacement = state.writer.wal.active.bytes)
    (fileSync : RegularFileSyncEffect replacement [visible stageIssued replacement]
      (observe stageIssued) (observe stageSynced))
    (fileSyncVisible : visible stageSynced replacement = visible stageIssued replacement)
    (oldBinding : (observe stageSynced).files.names
      (state.session.directory.file (.walSegment state.writer.wal.active.first)) = some old)
    (distinct : replacement ≠ old)
    (moved : (observe renamed).files.names (state.session.directory.file (.walSegment state.writer.wal.active.first)) =
      (observe stageSynced).files.names (state.session.directory.file .stagedWal))
    (detached : (observe renamed).files.names (state.session.directory.file .stagedWal) = none)
    (renameBytes : (observe renamed).files.bytes replacement = (observe stageSynced).files.bytes replacement)
    (renameVisible : visible renamed replacement = visible stageSynced replacement)
    (protectedFiles : NativeReadyProtectedStorage state (observe renamed).files)
    (marker : (observe renamed).files.Stored (state.session.directory.file .walBoundary)
      (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64))
    (rootSettled : ∀ names ∈ (observe renamed).crashNames,
      names state.session.directory.path = (observe renamed).files.names state.session.directory.path)
    (load : (observe renamed).Frames (fun path => state.crashPath path ∨ path = state.session.directory.file .stagedWal)
      (observe rootIssued))
    (loadVisible : visible rootIssued replacement = visible renamed replacement)
    (children : WalRootSyncEffect state.session.directory true (observe rootIssued) (observe reached))
    (parent : (observe rootIssued).Frames (· = state.session.directory.path) (observe reached))
    (directoryVisible : visible reached replacement = visible rootIssued replacement) :
    let directory := state.session.directory
    let keeper := directory.file (.walSegment state.writer.wal.active.first)
    let scratch := directory.file .stagedWal
    NativeReadyStorage state (observe reached) ∧
      (observe reached).files.names keeper = some replacement ∧
      (observe reached).files.names keeper ≠ (observe stageSynced).files.names keeper ∧
      (observe reached).files.names scratch = none ∧
      (∀ names ∈ (observe reached).crashNames, names keeper = some replacement ∧ names scratch = none) ∧
      ∀ inode, (observe reached).files.names keeper = some inode → visible reached inode = state.writer.wal.active.bytes := by
  intro directory keeper scratch
  have rootScope : state.crashPath directory.path := .inl rfl
  have markerScope : state.crashPath (directory.file .walBoundary) :=
    NativeReadyState.crashPath_iff_write.mpr (.inl rfl)
  have keeperScope : state.crashPath keeper := NativeReadyState.crashPath_iff_write.mpr (.inr (.inl rfl))
  have rootAtIssue := (load.weaken (scope := (· = directory.path)) (fun path equal => .inl (equal.symm ▸ rootScope))).settledFrom
    (fun names member path equal => equal.symm ▸ rootSettled names member)
  have childFiles : (observe rootIssued).files.Frames
      (fun path => ∃ file, path = directory.file file) (observe reached).files := by
    rintro _ ⟨file, rfl⟩
    exact ⟨children.visible file, fun inode named =>
      children.bytes _ (.inl rfl) file inode ((children.visible file).trans named)⟩
  obtain ⟨directoryFrame, settled⟩ := NativeReadyState.framesByDirectory rfl parent childFiles
    (fun names member => rootAtIssue names member _ rfl) (children.settled rfl)
  have selected := (load.weaken (fun _ kept => Or.inl kept)).visible.trans directoryFrame
  have syncedBinding : (observe stageSynced).files.names scratch = some replacement :=
    (congrFun fileSync.names scratch).trans stageBinding
  have renamedBinding : (observe renamed).files.names keeper = some replacement := moved.trans syncedBinding
  have persisted : (observe stageSynced).files.bytes replacement = [state.writer.wal.active.bytes] := by
    simpa [stagedPrefix] using fileSync.bytes replacement
  have keeperAtRename : (observe renamed).files.Stored keeper state.writer.wal.active.bytes :=
    ⟨replacement, renamedBinding, renameBytes.trans persisted⟩
  have named : (observe reached).files.names keeper = some replacement :=
    (selected keeper keeperScope).1.trans renamedBinding
  have gone : (observe reached).files.names scratch = none :=
    (children.visible .stagedWal).trans ((load.visible scratch (.inr rfl)).1.trans detached)
  refine ⟨⟨protectedFiles.frame (fun path kept => selected path
    (NativeReadyState.crashPath_iff_write.mpr (.inr (.inr kept)))), selected.stored markerScope marker,
    selected.stored keeperScope keeperAtRename, settled⟩, named, ?_, gone, ?_, ?_⟩
  · intro unchanged
    exact distinct (Option.some.inj (named.symm.trans (unchanged.trans oldBinding)))
  · intro names member
    exact ⟨(children.settled rfl names member (.walSegment state.writer.wal.active.first)).trans named,
      (children.settled rfl names member .stagedWal).trans gone⟩
  · intro inode held
    obtain rfl := Option.some.inj (held.symm.trans named)
    exact directoryVisible.trans (loadVisible.trans (renameVisible.trans (fileSyncVisible.trans stagedPrefix)))

end Replacement

section LiteralReplacement

variable {heap image : Type}

/-- The held root is the description still referenced by the original
cache cell. Another live handle for the same inode is insufficient. -/
def CachedKeeperReplacementRoot (state : NativeReadyState) (view : OpenCloseHeapView heap image)
    (cached : IO.Ref (Option IO.FS.Handle)) (root : IO.FS.Handle) (atHeap : heap) : Prop :=
  view.directory atHeap cached = some root ∧
    attachedReadSlot view root state.directorySlot (state.census.inode state.directorySlot.description) atHeap

private def keeperStageAt (state : NativeReadyState) (view : OpenCloseHeapView heap image)
    (observe : heap → CheckpointStorageObservation) (file : IO.FS.Handle) (slot : DescriptorSlot) (inode : Nat)
    (atHeap : heap) : Prop :=
  attachedReadSlot view file slot inode atHeap ∧
    (observe atHeap).files.names (state.session.directory.file .stagedWal) = some inode ∧
    ∀ path, state.crashPath path → (observe atHeap).files.names path ≠ some inode

private def freshKeeperStage (state : NativeReadyState) (view : OpenCloseHeapView heap image)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (buffered : heap → IO.FS.Handle → ByteArray) (file : IO.FS.Handle) (atHeap : heap) : Prop :=
  ∃ (slot : DescriptorSlot) (inode : Nat), keeperStageAt state view observe file slot inode atHeap ∧
    visible atHeap inode = .empty ∧ buffered atHeap file = .empty

private def SameLiveWalNames (directory : DiskDirectory) (before after : CheckpointStorageObservation) : Prop :=
  ∀ start, after.files.names (directory.file (.walSegment start)) = before.files.names (directory.file (.walSegment start))

private theorem SameLiveWalNames.trans {directory : DiskDirectory} {first middle last : CheckpointStorageObservation}
    (earlier : SameLiveWalNames directory first middle) (later : SameLiveWalNames directory middle last) :
    SameLiveWalNames directory first last :=
  fun start => (later start).trans (earlier start)

private structure keepsKeeperStage (state : NativeReadyState) (view : OpenCloseHeapView heap image)
    (observe : heap → CheckpointStorageObservation) (file : IO.FS.Handle) (slot : DescriptorSlot) (inode : Nat)
    (cached : IO.Ref (Option IO.FS.Handle)) (root : IO.FS.Handle) (before after : heap) : Prop where
  storage : (observe before).Frames state.crashPath (observe after)
  attached : attachedReadSlot view file slot inode after
  scratch : (observe after).files.names (state.session.directory.file .stagedWal) =
    (observe before).files.names (state.session.directory.file .stagedWal)
  root : CachedKeeperReplacementRoot state view cached root before → CachedKeeperReplacementRoot state view cached root after
  walNames : SameLiveWalNames state.session.directory (observe before) (observe after)

private theorem keepsKeeperStage.carries {state : NativeReadyState} {view : OpenCloseHeapView heap image}
    {observe : heap → CheckpointStorageObservation} {file : IO.FS.Handle} {slot : DescriptorSlot} {inode : Nat}
    {cached : IO.Ref (Option IO.FS.Handle)} {root : IO.FS.Handle} {before after : heap}
    (frame : keepsKeeperStage state view observe file slot inode cached root before after)
    (stage : keeperStageAt state view observe file slot inode before) :
    keeperStageAt state view observe file slot inode after :=
  ⟨frame.attached, frame.scratch.trans stage.2.1, fun path selected present =>
    stage.2.2 path selected ((frame.storage.visible path selected).1.symm.trans present)⟩

/-- A cached directory sync can settle child names only while its
handle is still attached to the inode named by the database root. -/
structure AlignedKeeperCacheCallbacks.CachedRootEffects
    (calls : AlignedKeeperCacheCallbacks heap) (state : NativeReadyState)
    (view : OpenCloseHeapView heap image) (observe : heap → CheckpointStorageObservation)
    (visible : heap → Nat → ByteArray) (cached : IO.Ref (Option IO.FS.Handle)) (root : IO.FS.Handle) where
  loadRoot : ∀ {before issued}, calls.getDirectory cached before = .ok (some root) issued →
    CachedKeeperReplacementRoot state view cached root before →
    CachedKeeperReplacementRoot state view cached root issued ∧
    (observe before).Frames (fun path => state.crashPath path ∨ path = state.session.directory.file .stagedWal)
      (observe issued) ∧
    SameLiveWalNames state.session.directory (observe before) (observe issued) ∧
    ∀ inode, (observe before).files.names (state.session.directory.file (.walSegment state.writer.wal.active.first)) =
      some inode → visible issued inode = visible before inode
  rootSync : ∀ {issued after}, calls.sync root issued = .ok () after →
    CachedKeeperReplacementRoot state view cached root issued →
    (observe issued).files.names state.session.directory.path = some (state.census.inode state.directorySlot.description) →
    WalRootSyncEffect state.session.directory true (observe issued) (observe after) ∧
      (observe issued).Frames (· = state.session.directory.path) (observe after) ∧
      CachedKeeperReplacementRoot state view cached root after ∧
      ∀ inode, (observe issued).files.names (state.session.directory.file (.walSegment state.writer.wal.active.first)) =
        some inode → visible after inode = visible issued inode

/-- Local namespace, descriptor and byte laws through the synced
replacement stage. Each premise is keyed to its own raw callback. -/
structure LongKeeperStageCallbacks.ReplacementPrefixStorageEffects
    (stage : LongKeeperStageCallbacks heap) (calls : AlignedKeeperCacheCallbacks heap)
    (state : NativeReadyState) (view : OpenCloseHeapView heap image)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (buffered : heap → IO.FS.Handle → ByteArray)
    (cached : IO.Ref (Option IO.FS.Handle)) (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
    (root : IO.FS.Handle)
    extends calls.CachedRootEffects state view observe visible cached root where
  acquire : ∀ before, stage.AcquisitionFrames (state.session.directory.file .stagedWal) before
    (fun first last => (observe first).Frames state.crashPath (observe last) ∧
      (CachedKeeperReplacementRoot state view cached root first → CachedKeeperReplacementRoot state view cached root last) ∧
      SameLiveWalNames state.session.directory (observe first) (observe last))
  tryCreate : ∀ {before after file}, stage.tryCreate (state.session.directory.file .stagedWal) before = .ok (.ok file) after →
    freshKeeperStage state view observe visible buffered file after
  create : ∀ {before after file}, stage.create (state.session.directory.file .stagedWal) before = .ok file after →
    freshKeeperStage state view observe visible buffered file after
  write : ∀ {before after file slot inode bytes}, stage.write file bytes before = .ok () after →
    keeperStageAt state view observe file slot inode before →
    keepsKeeperStage state view observe file slot inode cached root before after ∧
    visible after inode ++ buffered after file = (visible before inode ++ buffered before file) ++ bytes
  flush : ∀ {before after file slot inode}, stage.flush file before = .ok () after →
    keeperStageAt state view observe file slot inode before →
    keepsKeeperStage state view observe file slot inode cached root before after ∧
    visible after inode = visible before inode ++ buffered before file
  record : ∀ {before after file slot inode},
    calls.modifyPending pending (pushPending (state.session.directory.file .stagedWal) file) before = .ok () after →
    keeperStageAt state view observe file slot inode before →
    keepsKeeperStage state view observe file slot inode cached root before after ∧ visible after inode = visible before inode
  loadPending : ∀ {before after entries file slot inode}, calls.getPending pending before = .ok entries after →
    entries.find? (fun entry => entry.1 == state.session.directory.file .stagedWal) =
      some (state.session.directory.file .stagedWal, file) →
    keeperStageAt state view observe file slot inode before →
    keepsKeeperStage state view observe file slot inode cached root before after ∧ visible after inode = visible before inode
  clearPending : ∀ {before loaded after entries file slot inode}, calls.getPending pending before = .ok entries loaded →
    entries.find? (fun entry => entry.1 == state.session.directory.file .stagedWal) =
      some (state.session.directory.file .stagedWal, file) →
    calls.setPending pending (entries.filter (fun entry => entry.1 != state.session.directory.file .stagedWal)) loaded =
      .ok () after →
    keeperStageAt state view observe file slot inode loaded →
    keepsKeeperStage state view observe file slot inode cached root loaded after ∧ visible after inode = visible loaded inode
  fileSync : ∀ {before after file slot inode}, calls.sync file before = .ok () after →
    attachedReadSlot view file slot inode before →
    (observe before).files.names (state.session.directory.file .stagedWal) = some inode →
    RegularFileSyncEffect inode [visible before inode] (observe before) (observe after) ∧
      visible after inode = visible before inode ∧
      (CachedKeeperReplacementRoot state view cached root before → CachedKeeperReplacementRoot state view cached root after)

private abbrev replacementLiveFiles {heap : Type} (observe : heap → CheckpointStorageObservation)
    (visible : heap → Nat → ByteArray) (atHeap : heap) : CheckpointSurvivingFiles :=
  ⟨(observe atHeap).files.names, fun inode => [visible atHeap inode]⟩

section LivePrefix

variable {stage : LongKeeperStageCallbacks heap} {calls : AlignedKeeperCacheCallbacks heap}
  {state : NativeReadyState} {view : OpenCloseHeapView heap image}
  {observe : heap → CheckpointStorageObservation} {visible : heap → Nat → ByteArray}
  {cached : IO.Ref (Option IO.FS.Handle)} {pending : IO.Ref (List (FilePath × IO.FS.Handle))}
  {root : IO.FS.Handle}

private abbrev replacementLiveFrame (state : NativeReadyState) (observe : heap → CheckpointStorageObservation)
    (visible : heap → Nat → ByteArray) (before after : heap) : Prop :=
  (replacementLiveFiles observe visible before).Frames state.crashPath (replacementLiveFiles observe visible after)

private abbrev replacementPendingFrame (view : OpenCloseHeapView heap image)
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (before after : heap) : Prop :=
  view.pending after pending = view.pending before pending

private def ignoresReplacementStage (state : NativeReadyState) (observe : heap → CheckpointStorageObservation)
    (visible : heap → Nat → ByteArray) (staged : Nat) (before after : heap) : Prop :=
  ∀ path, state.crashPath path → ∀ inode, (observe before).files.names path = some inode →
    inode ≠ staged → visible after inode = visible before inode

/-- Each reached primitive supplies a live-byte law on protected names.
The pending setter applies only to the actual singleton. -/
structure LongKeeperStageCallbacks.ReplacementPrefixLiveEffects
    (stage : LongKeeperStageCallbacks heap) (calls : AlignedKeeperCacheCallbacks heap)
    (state : NativeReadyState) (view : OpenCloseHeapView heap image)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (cached : IO.Ref (Option IO.FS.Handle)) (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
    (root : IO.FS.Handle) (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)) where
  loadRoot : ∀ {before after}, calls.getDirectory cached before = .ok (some root) after →
    replacementLiveFrame state observe visible before after ∧ replacementPendingFrame view pending before after
  syncRoot : ∀ {before after}, calls.sync root before = .ok () after →
    replacementLiveFrame state observe visible before after ∧ replacementPendingFrame view pending before after
  unlink : ∀ {ordinal before after result}, ¬ state.crashPath (state.session.directory.file (.walSegment ordinal)) →
    remove (state.session.directory.file (.walSegment ordinal)) before = .ok result after →
    RunCollection.ownedUnlinkResult result = .ok () → replacementLiveFrame state observe visible before after ∧ replacementPendingFrame view pending before after
  acquire : ∀ before, stage.AcquisitionFrames (state.session.directory.file .stagedWal) before
    (fun first last => replacementLiveFrame state observe visible first last ∧ replacementPendingFrame view pending first last)
  write : ∀ {before after file slot inode bytes}, stage.write file bytes before = .ok () after →
    attachedReadSlot view file slot inode before →
    ignoresReplacementStage state observe visible inode before after ∧ replacementPendingFrame view pending before after
  flush : ∀ {before after file slot inode}, stage.flush file before = .ok () after →
    attachedReadSlot view file slot inode before →
    ignoresReplacementStage state observe visible inode before after ∧ replacementPendingFrame view pending before after
  record : ∀ {before after file},
    calls.modifyPending pending (pushPending (state.session.directory.file .stagedWal) file) before = .ok () after →
    view.pending before pending = [] → replacementLiveFrame state observe visible before after
  loadPending : ∀ {before after entries}, calls.getPending pending before = .ok entries after →
    replacementLiveFrame state observe visible before after ∧ replacementPendingFrame view pending before after
  clearPending : ∀ {before after file slot inode},
    view.pending before pending = [(state.session.directory.file .stagedWal, file)] →
    attachedReadSlot view file slot inode before → calls.setPending pending [] before = .ok () after →
    ignoresReplacementStage state observe visible inode before after
  syncFile : ∀ {before after file slot inode}, calls.sync file before = .ok () after →
    attachedReadSlot view file slot inode before → ignoresReplacementStage state observe visible inode before after

private theorem replacementLive_offStage {before after : heap} {staged : Nat}
    (frames : (observe before).files.Frames state.crashPath (observe after).files)
    (bytes : ignoresReplacementStage state observe visible staged before after)
    (privateStage : ∀ path, state.crashPath path → (observe before).files.names path ≠ some staged) :
    replacementLiveFrame state observe visible before after := by
  intro path selected
  refine ⟨(frames path selected).1, fun inode bound => ?_⟩
  have apart : inode ≠ staged := fun same => privateStage path selected (same ▸ bound)
  exact congrArg (fun bytes => [bytes]) (bytes path selected inode bound apart)

end LivePrefix

/-- A successful replacement also supplies the effect of moving the
synced inode. The same cached-root law applies to its final barrier. -/
structure LongKeeperStageCallbacks.ReplacementStorageEffects
    (stage : LongKeeperStageCallbacks heap) (calls : AlignedKeeperCacheCallbacks heap)
    (state : NativeReadyState) (view : OpenCloseHeapView heap image)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (buffered : heap → IO.FS.Handle → ByteArray)
    (cached : IO.Ref (Option IO.FS.Handle)) (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
    (root : IO.FS.Handle) (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    extends stage.ReplacementPrefixStorageEffects calls state view observe visible buffered cached pending root where
  move : ∀ {before after replacement old},
    let dir := state.session.directory
    let keeper := dir.file (.walSegment state.writer.wal.active.first)
    let scratch := dir.file .stagedWal
    rename scratch keeper before = .ok () after → (observe before).files.names scratch = some replacement →
    (observe before).files.names keeper = some old → replacement ≠ old →
    (observe before).Frames state.selectedRetryPath (observe after) ∧
      (observe after).files.names keeper = (observe before).files.names scratch ∧
      (observe after).files.names scratch = none ∧
      (observe after).files.bytes replacement = (observe before).files.bytes replacement ∧
      visible after replacement = visible before replacement ∧
      (CachedKeeperReplacementRoot state view cached root before → CachedKeeperReplacementRoot state view cached root after) ∧
      ∀ start, start ≠ state.writer.wal.active.first →
        (observe after).files.names (dir.file (.walSegment start)) =
        (observe before).files.names (dir.file (.walSegment start))

/-- A successful cached-root barrier frames the existing file bytes and
names. Children may acquire new crash choices, so only the root's own
parent binding uses a joint before-to-after crash frame. -/
theorem AlignedKeeperCacheCallbacks.CachedRootEffects.framesRootSync
    {calls : AlignedKeeperCacheCallbacks heap}
    {state : NativeReadyState} {view : OpenCloseHeapView heap image}
    {observe : heap → CheckpointStorageObservation} {visible : heap → Nat → ByteArray}
    {cached : IO.Ref (Option IO.FS.Handle)}
    {pending : IO.Ref (List (FilePath × IO.FS.Handle))}
    {root : IO.FS.Handle}
    (effects : calls.CachedRootEffects state view observe visible cached root)
    {active : IO.Ref (Option (FilePath × IO.FS.Handle))} {before after : heap}
    (rootNamed : (observe before).files.names state.session.directory.path =
      some (state.census.inode state.directorySlot.description))
    (held : CachedKeeperReplacementRoot state view cached root before)
    (readsDirectory : ∀ {before result issued}, calls.getDirectory cached before = .ok result issued →
      result = view.directory before cached)
    (returned : calls.syncPaths state.session.directory.path cached active pending #[state.session.directory.path]
      before = .ok () after) :
    (observe before).files.Frames state.crashPath (observe after).files ∧
      (observe before).Frames (· = state.session.directory.path) (observe after) ∧
      CachedKeeperReplacementRoot state view cached root after ∧
      SameLiveWalNames state.session.directory (observe before) (observe after) ∧
    (∀ names ∈ (observe after).crashNames, ∀ file,
      names (state.session.directory.file file) = (observe after).files.names (state.session.directory.file file)) ∧
    ∃ issued, calls.getDirectory cached before = .ok (some root) issued ∧ calls.sync root issued = .ok () after := by
  let dir := state.session.directory
  let syncer : RawSyncCalls heap := ⟨⟨calls.getDirectory, calls.getPending, calls.setPending, calls.getActive, calls.openRead⟩, calls.sync⟩
  change syncer.group dir.path cached active pending #[dir.path] before = .ok () after at returned
  obtain ⟨chosen, _, loaded, synced⟩ := syncer.rootGroupReturned returned
  have same : chosen = root := Option.some.inj ((readsDirectory loaded).trans held.1)
  subst chosen
  obtain ⟨attached, loadFrame, loadNames, _⟩ := effects.loadRoot loaded held
  have rootScope : state.crashPath dir.path := .inl rfl
  obtain ⟨children, parent, reachedRoot, _⟩ := effects.rootSync synced attached
    (((loadFrame.visible _ (.inl rootScope)).1).trans rootNamed)
  have rootLoad := loadFrame.weaken (scope := (· = dir.path)) (fun path same => .inl (same.symm ▸ rootScope))
  refine ⟨?_, rootLoad.trans parent, reachedRoot, fun start =>
    (children.visible (.walSegment start)).trans (loadNames start), children.settled rfl, _, loaded, synced⟩
  intro path tracked
  rcases NativeReadyState.crashPath_rootOrChild tracked with atRoot | ⟨file, rfl⟩
  · exact (rootLoad.trans parent).visible path atRoot
  · obtain ⟨named, content⟩ := loadFrame.visible _ (.inl tracked)
    exact ⟨(children.visible file).trans named, fun inode bound =>
      (children.bytes _ (.inl rfl) file inode ((children.visible file).trans (named.trans bound))).trans (content inode bound)⟩

/-- The common successful prefix ends at the literal fsync of the
fresh staging descriptor. The prune barrier settles the protected
child names, including the old keeper. Creation, writing, the selected
pending entry and regular-file fsync carry them to the rename issue. -/
theorem LongKeeperStageCallbacks.prunedAndSyncedReplacement
    (stage : LongKeeperStageCallbacks heap) (calls : AlignedKeeperCacheCallbacks heap)
    (state : NativeReadyState) (view : OpenCloseHeapView heap image)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (buffered : heap → IO.FS.Handle → ByteArray)
    (cached : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (root : IO.FS.Handle)
    (effects : stage.ReplacementPrefixStorageEffects calls state view observe visible buffered cached pending root)
    (plan : Plan) (keeper : plan.keeper = state.writer.wal.active.first)
    {entry authorized unlinked pruned staged synced : heap}
    (heldRoot : CachedKeeperReplacementRoot state view cached root entry)
    (rootNamed : (observe entry).files.names state.session.directory.path =
      some (state.census.inode state.directorySlot.description))
    (laterOutside : ∀ ordinal ∈ plan.newer,
      ¬ state.crashPath (state.session.directory.file (.walSegment ordinal)))
    (unlink : ∀ {ordinal before after result}, ¬ state.crashPath (state.session.directory.file (.walSegment ordinal)) →
      remove (state.session.directory.file (.walSegment ordinal)) before = .ok result after →
      RunCollection.ownedUnlinkResult result = .ok () → (observe before).Frames state.crashPath (observe after) ∧
      (CachedKeeperReplacementRoot state view cached root before → CachedKeeperReplacementRoot state view cached root after))
    (records : ∀ {file before after},
      calls.modifyPending pending (pushPending (state.session.directory.file .stagedWal) file) before = .ok () after →
      view.pending after pending = pushPending (state.session.directory.file .stagedWal) file (view.pending before pending))
    (readsPending : ∀ {before entries loaded}, calls.getPending pending before = .ok entries loaded →
      entries = view.pending before pending)
    (readsDirectory : ∀ {before result issued}, calls.getDirectory cached before = .ok result issued →
      result = view.directory before cached)
    (firstRoot : calls.syncPaths state.session.directory.path cached active pending
      #[state.session.directory.path] entry = .ok () authorized)
    (unlinks : ((plan.newer.map Step.unlink).forM (performPaths state.session.directory plan remove throw
      (stage.stage pending calls.modifyPending) (calls.syncPaths state.session.directory.path cached active pending) rename))
      authorized = .ok () unlinked)
    (pruneRoot : calls.syncPaths state.session.directory.path cached active pending
      #[state.session.directory.path] unlinked = .ok () pruned)
    (wroteStage : stage.stage pending calls.modifyPending (state.session.directory.file .stagedWal)
      (plan.keeperBytes.extract 0 plan.keeperSize) pruned = .ok () staged)
    (syncedStage : calls.syncPaths state.session.directory.path cached active pending
      #[state.session.directory.file .stagedWal] staged = .ok () synced) :
    (observe entry).files.Frames state.crashPath (observe synced).files ∧
    (observe entry).Frames (· = state.session.directory.path) (observe synced) ∧
    CachedKeeperReplacementRoot state view cached root synced ∧
    SameLiveWalNames state.session.directory (observe entry) (observe authorized) ∧
    SameLiveWalNames state.session.directory (observe unlinked) (observe synced) ∧
    (observe synced).files.names (state.session.directory.file (.walSegment plan.keeper)) =
      (observe entry).files.names (state.session.directory.file (.walSegment plan.keeper)) ∧
    (∀ names ∈ (observe synced).crashNames, ∀ file, state.crashPath (state.session.directory.file file) →
      names (state.session.directory.file file) = (observe synced).files.names (state.session.directory.file file)) ∧
    (SameLiveWalNames state.session.directory (observe unlinked) (observe pruned) ∧
      ∀ names ∈ (observe pruned).crashNames, ∀ file,
        names (state.session.directory.file file) = (observe pruned).files.names (state.session.directory.file file)) ∧
    ∃ (issued : heap) (file : IO.FS.Handle) (slot : DescriptorSlot) (replacement : Nat),
      calls.sync file issued = .ok () synced ∧
      attachedReadSlot view file slot replacement issued ∧
      (observe synced).files.names (state.session.directory.file (.walSegment plan.keeper)) ≠ some replacement ∧
      (observe issued).files.names (state.session.directory.file .stagedWal) = some replacement ∧
      visible issued replacement = plan.keeperBytes.extract 0 plan.keeperSize ∧
      RegularFileSyncEffect replacement [visible issued replacement] (observe issued) (observe synced) ∧
      visible synced replacement = visible issued replacement ∧
      (stage.ReplacementPrefixLiveEffects calls state view observe visible cached pending root remove →
        view.pending entry pending = [] →
        (replacementLiveFiles observe visible entry).Frames state.crashPath (replacementLiveFiles observe visible synced)) := by
  let dir := state.session.directory
  let path := dir.file .stagedWal
  let keeperPath := dir.file (.walSegment plan.keeper)
  let write := stage.stage pending calls.modifyPending
  let group := calls.syncPaths dir.path cached active pending
  obtain ⟨file, opened, written, flushed, acquired, wrote, didFlush, recorded⟩ := stage.reachedStage wroteStage
  obtain ⟨entries, loaded, consumed, got, chosenStage, cleared, stageSync⟩ :=
    calls.rememberedPendingReturned view (file_ne_directory dir .stagedWal)
      (records recorded) readsPending syncedStage
  have rootScope : state.crashPath dir.path := .inl rfl
  have keepScope : state.crashPath keeperPath := by
    change state.crashPath (dir.file (.walSegment plan.keeper))
    rw [keeper]
    exact NativeReadyState.crashPath_iff_write.mpr (.inr (.inl rfl))
  obtain ⟨authFiles, authParent, authRoot, authNames, _, _, authLoaded, authSynced⟩ :=
    effects.toCachedRootEffects.framesRootSync rootNamed heldRoot readsDirectory firstRoot
  let frames (_ : Unit) (atHeap : heap) := (observe authorized).Frames state.crashPath (observe atHeap) ∧
    CachedKeeperReplacementRoot state view cached root atHeap
  have ⟨removes, unlinkedRoot⟩ : frames () unlinked := foldReturnedWalUnlinks dir plan remove write group rename frames
    (fun _ _ => ()) (initial := ()) ⟨.refl _ _, authRoot⟩ (fun member called accepted before => by
      obtain ⟨unchanged, retained⟩ := unlink (laterOutside _ member) called accepted
      exact ⟨before.1.trans unchanged, retained before.2⟩) unlinks
  have prunedRootName := (removes.visible _ rootScope).1.trans ((authFiles _ rootScope).1.trans rootNamed)
  obtain ⟨prunedFiles, prunedParent, prunedRoot, prunedNames, settled, _, pruneLoaded, pruneSynced⟩ :=
    effects.toCachedRootEffects.framesRootSync prunedRootName unlinkedRoot readsDirectory pruneRoot
  have prunedFootprint := authFiles.trans (removes.visible.trans prunedFiles)
  have prunedParentFrame := authParent.trans
    ((removes.weaken (scope := (· = dir.path)) (fun _ same => same.symm ▸ rootScope)).trans prunedParent)
  have acquiredFrame := (effects.acquire pruned).keeps (fun _ => ⟨.refl _ _, id, fun _ => rfl⟩)
    (fun first second => ⟨first.1.trans second.1, second.2.1 ∘ first.2.1, first.2.2.trans second.2.2⟩)
  change stage.acquire path pruned = .ok file opened at acquired
  rw [show stage.acquire (dir.file .stagedWal) pruned = .ok file opened from acquired,
    NativeFileEffectProjection.reached] at acquiredFrame
  obtain ⟨acquireFrame, acquiredRoot, acquiredNames⟩ := acquiredFrame
  obtain ⟨slot, replacement, openedStage, empty, unbuffered⟩ :=
    withFreshStaging_acquireProvides stage.tryCreate stage.detachStale stage.create path
      (freshKeeperStage state view observe visible buffered) acquired effects.tryCreate effects.create
  obtain ⟨writeFrame, payloadWrite⟩ := effects.write wrote openedStage
  have writtenStage := writeFrame.carries openedStage
  obtain ⟨flushFrame, payloadFlush⟩ := effects.flush didFlush writtenStage
  have flushedStage := flushFrame.carries writtenStage
  obtain ⟨recordFrame, payloadRecord⟩ := effects.record recorded flushedStage
  have recordedStage := recordFrame.carries flushedStage
  obtain ⟨loadFrame, payloadLoad⟩ := effects.loadPending got chosenStage recordedStage
  have loadedStage := loadFrame.carries recordedStage
  obtain ⟨clearFrame, payloadClear⟩ := effects.clearPending got chosenStage cleared loadedStage
  have syncedStage := clearFrame.carries loadedStage
  have stagedBinding := syncedStage.2.1
  have stageBytes := payloadClear.trans (payloadLoad.trans (payloadRecord.trans (payloadFlush.trans payloadWrite)))
  rw [empty, unbuffered, ByteArray.empty_append, ByteArray.empty_append] at stageBytes
  have atSyncRoot := clearFrame.root (loadFrame.root (recordFrame.root
    (flushFrame.root (writeFrame.root (acquiredRoot prunedRoot)))))
  have pendingFrames := writeFrame.storage.trans
    (flushFrame.storage.trans (recordFrame.storage.trans (loadFrame.storage.trans clearFrame.storage)))
  have noAlias (name : FilePath) (selected : state.crashPath name) (inode : Nat)
      (binding : (observe consumed).files.names name = some inode) : inode ≠ replacement := by
    intro equal
    exact syncedStage.2.2 name selected (equal ▸ binding)
  obtain ⟨fileSync, syncedVisible, keepSyncRoot⟩ := effects.fileSync stageSync syncedStage.1 stagedBinding
  have toSynced := acquireFrame.trans (pendingFrames.trans (fileSync.frames noAlias))
  have keeperAtRename := (toSynced.visible keeperPath keepScope).1.trans (prunedFootprint keeperPath keepScope).1
  have separate : (observe synced).files.names keeperPath ≠ some replacement := by
    rw [fileSync.names]
    exact syncedStage.2.2 _ keepScope
  have parentFrame := prunedParentFrame.trans
    (toSynced.weaken (scope := (· = dir.path)) (fun _ same => same.symm ▸ rootScope))
  have childrenSettled := (toSynced.weaken
    (scope := fun name => state.crashPath name ∧ ∃ file, name = dir.file file)
    (fun _ child => child.1)).settledFrom (by
      intro names possible name child
      obtain ⟨file, rfl⟩ := child.2
      exact settled names possible file)
  have stageNames : SameLiveWalNames dir (observe unlinked) (observe synced) := prunedNames.trans (acquiredNames.trans
    (writeFrame.walNames.trans (flushFrame.walNames.trans (recordFrame.walNames.trans
      (loadFrame.walNames.trans (clearFrame.walNames.trans (fun start =>
        congrFun fileSync.names (dir.file (.walSegment start)))))))))
  refine ⟨prunedFootprint.trans toSynced.visible, parentFrame, keepSyncRoot atSyncRoot, authNames, stageNames,
    keeperAtRename, fun names possible file selected => childrenSettled names possible _ ⟨selected, file, rfl⟩,
    ⟨prunedNames, settled⟩, consumed, file, slot, replacement, stageSync, syncedStage.1, separate, stagedBinding, stageBytes, fileSync,
    syncedVisible, ?_⟩
  intro liveEffects pendingAtEntry
  obtain ⟨authReadLive, authReadPending⟩ := liveEffects.loadRoot authLoaded
  obtain ⟨authSyncLive, authSyncPending⟩ := liveEffects.syncRoot authSynced
  let liveThroughPrune (_ : Unit) (atHeap : heap) :=
    (replacementLiveFiles observe visible entry).Frames state.crashPath (replacementLiveFiles observe visible atHeap) ∧
    view.pending atHeap pending = []
  have atAuthorization : liveThroughPrune () authorized :=
    ⟨authReadLive.trans authSyncLive, authSyncPending.trans (authReadPending.trans pendingAtEntry)⟩
  have unlinkedLive : liveThroughPrune () unlinked := by
    refine foldReturnedWalUnlinks dir plan remove write group rename liveThroughPrune (fun _ _ => ()) (initial := ()) atAuthorization
      ?_ unlinks
    intro ordinal before after result _ member called accepted previous
    obtain ⟨keepsLive, keepsPending⟩ := liveEffects.unlink (laterOutside ordinal member) called accepted
    exact ⟨previous.1.trans keepsLive, keepsPending.trans previous.2⟩
  obtain ⟨pruneReadLive, pruneReadPending⟩ := liveEffects.loadRoot pruneLoaded
  obtain ⟨pruneSyncLive, pruneSyncPending⟩ := liveEffects.syncRoot pruneSynced
  have prunedLive := unlinkedLive.1.trans (pruneReadLive.trans pruneSyncLive)
  have prunedPending := pruneSyncPending.trans (pruneReadPending.trans unlinkedLive.2)
  have openedFrame := (liveEffects.acquire pruned).keeps
    (fun _ => ⟨fun _ _ => ⟨rfl, fun _ _ => rfl⟩, rfl⟩)
    (fun first second => ⟨first.1.trans second.1, second.2.trans first.2⟩)
  rw [show stage.acquire (dir.file .stagedWal) pruned = .ok file opened from acquired,
    NativeFileEffectProjection.reached] at openedFrame
  obtain ⟨openedLive, openedPending⟩ := openedFrame
  obtain ⟨writeLive, writePending⟩ := liveEffects.write wrote openedStage.1
  obtain ⟨flushLive, flushPending⟩ := liveEffects.flush didFlush writtenStage.1
  have emptyAtFlush := flushPending.trans (writePending.trans (openedPending.trans prunedPending))
  have onlyFresh : view.pending staged pending = [(path, file)] := by
    simpa only [emptyAtFlush, pushPending, List.filter_nil] using records recorded
  have recordedLive := liveEffects.record recorded emptyAtFlush
  obtain ⟨loadLive, loadPending⟩ := liveEffects.loadPending got
  have clearLive := calls.clearsOnlyStagedKeeper view pending
    (fun atHeap => (observe atHeap).files.names) visible onlyFresh got (fun read => ⟨readsPending read, loadPending⟩)
    cleared loadedStage.1 liveEffects.clearPending
    (fun path selected => (clearFrame.storage.visible path selected).1) loadedStage.2.2
  have fileLive := replacementLive_offStage (fileSync.frames noAlias).visible
    (liveEffects.syncFile stageSync syncedStage.1) syncedStage.2.2
  exact prunedLive.trans (openedLive.trans
    ((replacementLive_offStage writeFrame.storage.visible writeLive openedStage.2.2).trans
      ((replacementLive_offStage flushFrame.storage.visible flushLive writtenStage.2.2).trans
        (recordedLive.trans (loadLive.trans (clearLive.trans fileLive))))))

/-- The actual successful long repair builds physical readiness. Its
accepted unlink pass is framed locally; a fresh stage descriptor supplies
its own bytes at the pending fsync and is the inode moved into the keeper.
If the selected scan identifies all later starts, the same execution
also settles the WAL catalog through any prospective marker. -/
theorem LongKeeperStageCallbacks.readyStorageOfFinishedReplacement
    (stage : LongKeeperStageCallbacks heap) (calls : AlignedKeeperCacheCallbacks heap)
    (state : NativeReadyState) (view : OpenCloseHeapView heap image)
    (observe : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (buffered : heap → IO.FS.Handle → ByteArray)
    (cached : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (root : IO.FS.Handle)
    (effects : stage.ReplacementStorageEffects calls state view observe visible buffered cached pending root rename)
    (plan : Plan) (physicalSize : Nat) (longer : plan.keeperSize < physicalSize)
    (keeper : plan.keeper = state.writer.wal.active.first)
    (prefixBytes : plan.keeperBytes.extract 0 plan.keeperSize = state.writer.wal.active.bytes)
    {entry reached : heap} {old : Nat}
    (heldRoot : CachedKeeperReplacementRoot state view cached root entry)
    (protectedFiles : NativeReadyProtectedStorage state (observe entry).files)
    (oldNamed : (observe entry).files.names (state.session.directory.file (.walSegment plan.keeper)) = some old)
    (marker : (observe entry).files.Stored (state.session.directory.file .walBoundary)
      (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64))
    (rootSettled : ∀ names ∈ (observe entry).crashNames,
      names state.session.directory.path = (observe entry).files.names state.session.directory.path)
    (laterOutside : ∀ ordinal ∈ plan.newer,
      ¬ state.crashPath (state.session.directory.file (.walSegment ordinal)))
    (unlink : ∀ {ordinal before after result}, ¬ state.crashPath (state.session.directory.file (.walSegment ordinal)) →
      remove (state.session.directory.file (.walSegment ordinal)) before = .ok result after →
      RunCollection.ownedUnlinkResult result = .ok () → (observe before).Frames state.crashPath (observe after) ∧
      (CachedKeeperReplacementRoot state view cached root before → CachedKeeperReplacementRoot state view cached root after))
    (records : ∀ {file before after},
      calls.modifyPending pending (pushPending (state.session.directory.file .stagedWal) file) before = .ok () after →
      view.pending after pending = pushPending (state.session.directory.file .stagedWal) file (view.pending before pending))
    (readsPending : ∀ {before entries loaded}, calls.getPending pending before = .ok entries loaded →
      entries = view.pending before pending)
    (readsDirectory : ∀ {before result issued}, calls.getDirectory cached before = .ok result issued →
      result = view.directory before cached)
    (returned : finishBoundedMarkedOpen state.session.directory plan physicalSize remove
      (stage.stage pending calls.modifyPending) (calls.syncPaths state.session.directory.path cached active pending)
      rename entry = .ok () reached) :
    ∃ replacement, replacement ≠ old ∧
      NativeReadyStorage state (observe reached) ∧
      (observe reached).files.names (state.session.directory.file (.walSegment plan.keeper)) = some replacement ∧
      (observe reached).files.names (state.session.directory.file .stagedWal) = none ∧
      (∀ names ∈ (observe reached).crashNames,
        names (state.session.directory.file (.walSegment plan.keeper)) = some replacement ∧
        names (state.session.directory.file .stagedWal) = none) ∧
      visible reached replacement = state.writer.wal.active.bytes ∧
      ∀ {firstOffset : Nat},
        state.writer.wal.NamespaceWindow state.session.directory firstOffset plan.through (observe entry).files.names →
        (∀ start ∈ state.writer.wal.segments.map WalSegment.first, start ≤ plan.through) →
        (∀ ordinal ∈ plan.newer, plan.through < ordinal) →
        (∀ start, plan.through < start →
          (((observe entry).files.names (state.session.directory.file (.walSegment start))).isSome = true ↔
            start ∈ plan.newer)) →
        (∀ {ordinal before after result}, plan.through < ordinal →
          remove (state.session.directory.file (.walSegment ordinal)) before = .ok result after →
          RunCollection.ownedUnlinkResult result = .ok () →
          (observe after).files.names (state.session.directory.file (.walSegment ordinal)) = none ∧
          ∀ start, start ≠ ordinal → (observe after).files.names (state.session.directory.file (.walSegment start)) =
            (observe before).files.names (state.session.directory.file (.walSegment start))) →
        ∀ through, state.writer.wal.SettledNamespaceWindow state.session.directory firstOffset through (observe reached) := by
  let dir := state.session.directory
  let path := dir.file .stagedWal
  let keeperPath := dir.file (.walSegment plan.keeper)
  let write := stage.stage pending calls.modifyPending
  let group := calls.syncPaths dir.path cached active pending
  obtain ⟨authorized, unlinked, pruned, staged, synced, renamed, firstRoot, unlinks, pruneRoot,
    wroteStage, syncedStage, moved, finalGroup⟩ :=
    finishBoundedMarkedOpen_replacementReached dir plan physicalSize remove write group rename longer returned
  obtain ⟨atSync, parentAtSync, heldAtSync, authNames, stageNames, oldAtRename, _, _,
    issued, _, _, replacement, _, _, separate, stagedBinding, stagedBytes, fileSync, syncedVisible, _⟩ :=
    stage.prunedAndSyncedReplacement calls state view observe visible buffered cached active pending remove rename
      root effects.toReplacementPrefixStorageEffects plan keeper heldRoot protectedFiles.directoryBound laterOutside unlink records readsPending
      readsDirectory firstRoot unlinks pruneRoot wroteStage syncedStage
  have distinct : replacement ≠ old := fun same => separate (same.symm ▸ oldAtRename.trans oldNamed)
  have stageBytes : visible issued replacement = state.writer.wal.active.bytes := stagedBytes.trans prefixBytes
  have stageAtRename := (congrFun fileSync.names path).trans stagedBinding
  have rootScope : state.crashPath dir.path := .inl rfl
  have keepScope : state.crashPath keeperPath := by
    change state.crashPath (dir.file (.walSegment plan.keeper))
    rw [keeper]
    exact NativeReadyState.crashPath_iff_write.mpr (.inr (.inl rfl))
  rw [keeper] at moved
  have oldKeeper : (observe synced).files.names (dir.file (.walSegment state.writer.wal.active.first)) = some old := by
    simpa only [keeperPath, keeper] using oldAtRename.trans oldNamed
  obtain ⟨moveFrame, movedName, detached, movedBytes, movedVisible, keepMoveRoot, movedOtherWalNames⟩ :=
    effects.move moved stageAtRename oldKeeper distinct
  have included (name : FilePath) (selected : state.selectedRetryPath name) : state.crashPath name :=
    NativeReadyState.crashPath_iff_write.mpr (selected.imp id Or.inr)
  have toRename : (observe entry).files.Frames state.selectedRetryPath (observe renamed).files :=
    CheckpointSurvivingFiles.Frames.trans (fun name selected => atSync name (included name selected)) moveFrame.visible
  have protectedAtRename := protectedFiles.frame (fun name inside => toRename name (.inr inside))
  have markerAtRename := toRename.stored (.inl rfl) marker
  have rootAtRename := (toRename _ (.inr (.inl rfl))).1.trans protectedFiles.directoryBound
  have rootFrame := parentAtSync.trans (moveFrame.weaken (fun _ eq => .inr (.inl eq)))
  have parentSettled := rootFrame.settledFrom (fun map allowed name eq => eq.symm ▸ rootSettled map allowed)
  have heldAtRename := keepMoveRoot heldAtSync
  let syncer : RawSyncCalls heap := ⟨⟨calls.getDirectory, calls.getPending, calls.setPending,
    calls.getActive, calls.openRead⟩, calls.sync⟩
  change syncer.group dir.path cached active pending #[dir.path] renamed = .ok () reached at finalGroup
  obtain ⟨chosenRoot, _, readRoot, finalRoot⟩ := syncer.rootGroupReturned finalGroup
  have sameRoot : chosenRoot = root := Option.some.inj ((readsDirectory readRoot).trans heldAtRename.1)
  subst chosenRoot
  obtain ⟨rootAttached, loadedRootFrame, rootLoadNames, rootLoadVisible⟩ := effects.loadRoot readRoot heldAtRename
  obtain ⟨children, parent, _, rootSyncVisible⟩ := effects.rootSync finalRoot rootAttached
    (((loadedRootFrame.visible _ (.inl rootScope)).1).trans rootAtRename)
  have finalKeeperName := movedName.trans stageAtRename
  have atRootIssue := (loadedRootFrame.visible _ (.inl (keeper ▸ keepScope))).1.trans finalKeeperName
  obtain ⟨ready, bound, _, gone, chosen, live⟩ := NativeReadyStorage.afterKeeperReplacement state observe visible
    stagedBinding stageBytes fileSync syncedVisible oldKeeper distinct movedName detached movedBytes movedVisible
    protectedAtRename markerAtRename (fun map allowed => parentSettled map allowed _ rfl)
    loadedRootFrame (rootLoadVisible _ finalKeeperName) children parent (rootSyncVisible _ atRootIssue)
  refine ⟨replacement, distinct, ready, keeper.symm ▸ bound, gone,
    fun map allowed => keeper.symm ▸ chosen map allowed, live replacement bound, ?_⟩
  intro firstOffset selected bounded later listed unlinkNames through
  have fromAuth := selected.frame (fun start _ _ => congrArg Option.isSome (authNames start))
  have fromPrune := fromAuth.afterAcceptedUnlinks (plan := plan) (names := fun atHeap => (observe atHeap).files.names)
    bounded later (fun start beyond => by rw [authNames start]; exact (listed start beyond).mp) remove write group rename
    (fun member called accepted => unlinkNames (later _ member) called accepted) unlinks through
  have beforeRoot := (fromPrune.frame fun start _ _ => congrArg Option.isSome (stageNames start)).frame
    (fun start _ _ => by
      have same : ((observe renamed).files.names (dir.file (.walSegment start))).isSome =
          ((observe synced).files.names (dir.file (.walSegment start))).isSome := by
        by_cases isKeeper : start = state.writer.wal.active.first
        · rw [isKeeper, finalKeeperName, oldKeeper]
          rfl
        · rw [movedOtherWalNames start isKeeper]
      exact (congrArg Option.isSome (rootLoadNames start)).trans same)
  exact beforeRoot.afterDirectorySync children.visible (children.settled rfl)

end LiteralReplacement

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout retry.image history} {published : CheckpointPublication.Image}
  {admission : CensusOpenAdmissionReports input directory inventory retry}
  {vacant : TryLockObserves retry.owners directory (.ok true)} {checkpoint : Option (PackedTable × UInt64)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}
  {calls : CapturedAlignedCallbacks admission} {reads : CapturedMarkedReadReports admission layout published}
  {heap : Type} {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap} {entry : heap}
  {finish : CapturedLongKeeperFinish calls reads vacant selected}
  {seed : OpenSyncCacheAllocations admission.opened view init entry}
  {reader : MarkedTemporaryReadCalls heap} {before : heap}
  {read : NativeLongKeeperReadHeap finish seed reader before} {sync : AlignedKeeperCacheCallbacks heap}
  {authorization : NativeLongKeeperAuthorizationHeap read sync}
  {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)}
  {suffix : NativeLongKeeperSuffixHeap authorization remove} {stage : LongKeeperStageCallbacks heap}

variable {staged : NativeLongKeeperFreshStageHeap suffix stage}
  {observe : heap → CheckpointStorageObservation} {visible : heap → Nat → ByteArray}
  {synced : NativeLongKeeperStagedSyncHeap staged (fun heap => (observe heap).files.names)}
  {rename : FilePath → FilePath → EStateM IO.Error heap Unit}
  {renamed : NativeLongKeeperRenameHeap synced rename}

local notation "replacement" => finish.stage.inventory.inode finish.stage.slot.description

theorem NativeReadyState.stagedWalOutsideRetryFootprint (state : NativeReadyState) :
    ∀ path, state.selectedRetryPath path → path ≠ state.session.directory.file .stagedWal := by
  let directory := state.session.directory
  have basename {left right : DiskFile} (same : directory.file left = directory.file right) :=
    (String.append_right_inj (directory.path.toString ++ "/")).mp (congrArg FilePath.toString same)
  intro path retained same
  rcases retained with marker | held
  · have equal := basename (marker.symm.trans same)
    change "WAL.commit" = "WAL.next" at equal
    exact (by decide : "WAL.commit" ≠ "WAL.next") equal
  rcases held with root | lock | manifest | sealedPath | runPath
  · exact file_ne_directory directory .stagedWal (root.symm.trans same).symm
  · have equal := basename (lock.symm.trans same)
    change "LOCK" = "WAL.next" at equal
    exact (by decide : "LOCK" ≠ "WAL.next") equal
  · have equal := basename (manifest.symm.trans same)
    change "MANIFEST" = "WAL.next" at equal
    exact (by decide : "MANIFEST" ≠ "WAL.next") equal
  · obtain ⟨segment, _, equal⟩ := sealedPath
    obtain ⟨_, impossible⟩ := DiskDirectory.walSegment_exclusive (equal.symm.trans same).symm
    cases impossible
  · obtain ⟨_, metadata, index, _, _, _, equal⟩ := runPath
    have samePrefix := congrArg (fun name : String => name.toList.take 4) (basename (equal.symm.trans same))
    change ("run-" ++ metadata.header.generation.toNat.repr ++ "-" ++ index.repr ++ ".v3").toList.take 4 =
      "WAL.next".toList.take 4 at samePrefix
    simp [String.toList_append] at samePrefix


/-- A captured staging write can change its own inode, while its name
and every protected binding are disjoint. Project those local effects
to the selected retry footprint. -/
private theorem RunWriteInodeFrame.framesSelectedStage
    {state : NativeReadyState} {dir : DiskDirectory} {before after : WalInodeImage}
    {oldRuns newRuns : RunUnlinkImage} {inode : Nat}
    {entry : RunDirectoryInodeView dir before oldRuns} {reached : RunDirectoryInodeView dir after newRuns}
    (effect : RunWriteInodeFrame (dir.file .stagedWal) inode after entry reached)
    (sameDirectory : state.session.directory = dir)
    (apart : ∀ path, state.selectedRetryPath path → entry.visible path ≠ some inode) :
    state.SelectedRetryFrame entry.storageObservation reached.storageObservation before.visible after.visible := by
  have separate (path : FilePath) (held : state.selectedRetryPath path) : path ≠ dir.file .stagedWal := by
    rw [← sameDirectory]
    exact state.stagedWalOutsideRetryFootprint path held
  have distinct (path : FilePath) (held : state.selectedRetryPath path)
      (object : Nat) (bound : entry.visible path = some object) : object ≠ inode := by
    intro same
    exact apart path held (same ▸ bound)
  refine ⟨?_, ?_, ?_⟩
  · intro path held
    exact ⟨effect.visibleNames path (separate path held),
      fun object bound => congrArg (fun bytes => [bytes]) (effect.visibleBytes object (distinct path held object bound))⟩
  · intro path held
    exact ⟨effect.visibleNames path (separate path held), fun object bound => effect.crashBytes object (distinct path held object bound)⟩
  · have root : state.selectedRetryPath state.session.directory.path := .inr (.inl rfl)
    refine ⟨?_, ?_⟩
    · intro path same
      subst path
      exact ⟨effect.visibleNames _ (separate _ root),
        fun object bound => effect.crashBytes object (distinct _ root object bound)⟩
    · intro names chosen
      obtain ⟨prior, available, keeps⟩ := effect.crashNames names chosen
      exact ⟨prior, available, fun path same => keeps path (same.symm ▸ separate _ root)⟩

/-- On the actual staging path the winning exclusive create supplies the
new, disjoint inode. Its write and flush preserve the selected files.
The real fsync uses that same descriptor and makes its payload durable. -/
theorem NativeLongKeeperStagedSyncHeap.preservesSelectedStage
    (state : NativeReadyState) (sameDirectory : state.session.directory = directory)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (buffered : heap → IO.FS.Handle → ByteArray)
    (observation : ∀ atHeap, RunDirectoryInodeView directory (inodes atHeap) (runs atHeap))
    (seen : NativeLongKeeperStagedSyncHeap staged (fun atHeap => (observation atHeap).visible))
    (acquisition : stage.AcquisitionFrames (directory.file .stagedWal) suffix.reached
      (fun before after => state.SelectedRetryFrame (observation before).storageObservation
        (observation after).storageObservation (inodes before).visible (inodes after).visible))
    (freshFirst : ∀ {file opened}, stage.tryCreate (directory.file .stagedWal) suffix.reached = .ok (.ok file) opened →
      let inode := (view.descriptors opened).inode (view.handle opened file).2.1.description
      (∀ path, state.selectedRetryPath path → (observation opened).visible path ≠ some inode) ∧
      (inodes opened).visible inode = ByteArray.empty ∧ buffered opened file = ByteArray.empty)
    (freshRetry : ∀ {file before opened}, stage.create (directory.file .stagedWal) before = .ok file opened →
      let inode := (view.descriptors opened).inode (view.handle opened file).2.1.description
      (∀ path, state.selectedRetryPath path → (observation opened).visible path ≠ some inode) ∧
      (inodes opened).visible inode = ByteArray.empty ∧ buffered opened file = ByteArray.empty)
    (wrote : stage.write staged.descriptor layout.keeper.bytes staged.created = .ok () staged.written →
      stage.flush staged.descriptor staged.written = .ok () staged.flushed →
      RunWriteInodeFrame (directory.file .stagedWal) replacement (inodes staged.flushed)
        (observation staged.created) (observation staged.flushed))
    (writePayload : stage.write staged.descriptor layout.keeper.bytes staged.created = .ok () staged.written →
      (inodes staged.written).visible replacement ++ buffered staged.written staged.descriptor =
        ((inodes staged.created).visible replacement ++ buffered staged.created staged.descriptor) ++ layout.keeper.bytes)
    (flushPayload : stage.flush staged.descriptor staged.written = .ok () staged.flushed →
      (inodes staged.flushed).visible replacement =
        (inodes staged.written).visible replacement ++ buffered staged.written staged.descriptor)
    (stored : sync.modifyPending seed.pendingRef (pushPending (directory.file .stagedWal) staged.descriptor) staged.flushed =
      .ok () staged.recorded →
      state.SelectedRetryFrame (observation staged.flushed).storageObservation (observation staged.recorded).storageObservation
        (inodes staged.flushed).visible (inodes staged.recorded).visible ∧
      (inodes staged.recorded).visible replacement = (inodes staged.flushed).visible replacement)
    (consumed : sync.setPending seed.pendingRef [] staged.recorded = .ok () seen.consumed →
      state.SelectedRetryFrame (observation staged.recorded).storageObservation (observation seen.consumed).storageObservation
        (inodes staged.recorded).visible (inodes seen.consumed).visible ∧
      (inodes seen.consumed).visible replacement = (inodes staged.recorded).visible replacement)
    (fsync : sync.sync staged.descriptor seen.consumed = .ok () seen.reached →
      (view.handle seen.consumed staged.descriptor).2.1 ∈ (view.descriptors seen.consumed).slots →
      RegularFileSyncEffect ((view.handle seen.consumed staged.descriptor).1.inode
        (view.handle seen.consumed staged.descriptor).2.1.description) [(inodes seen.consumed).visible replacement]
        (observation seen.consumed).storageObservation (observation seen.reached).storageObservation ∧
      (inodes seen.reached).visible = (inodes seen.consumed).visible) :
    state.SelectedRetryFrame (observation suffix.reached).storageObservation (observation seen.reached).storageObservation
        (inodes suffix.reached).visible (inodes seen.reached).visible ∧
      (observation seen.reached).visible (directory.file .stagedWal) = some replacement ∧
      (inodes seen.reached).crashBytes replacement = [layout.keeper.bytes] ∧
      (inodes seen.reached).visible replacement = layout.keeper.bytes := by
  have opened := acquisition.keeps (fun atHeap => .refl _ _ _) NativeReadyState.SelectedRetryFrame.trans
  rw [staged.acquired] at opened
  have fresh := withFreshStaging_acquireProvides stage.tryCreate stage.detachStale stage.create
    (directory.file .stagedWal) (fun file atHeap =>
      let inode := (view.descriptors atHeap).inode (view.handle atHeap file).2.1.description
      (∀ path, state.selectedRetryPath path → (observation atHeap).visible path ≠ some inode) ∧
      (inodes atHeap).visible inode = ByteArray.empty ∧ buffered atHeap file = ByteArray.empty)
    staged.acquired freshFirst freshRetry
  obtain ⟨distinct, empty, noBuffered⟩ := fresh
  rw [staged.openedCensus, staged.openedSlot] at distinct empty
  have stageWritten := RunWriteInodeFrame.framesSelectedStage (wrote staged.wrote staged.flush) sameDirectory distinct
  obtain ⟨remembered, stagedVisible⟩ := stored staged.record
  obtain ⟨cleared, consumedVisible⟩ := consumed seen.cleared
  have inPending := stageWritten.trans (remembered.trans cleared)
  have bytes := consumedVisible.trans (stagedVisible.trans ((flushPayload staged.flush).trans (writePayload staged.wrote)))
  rw [empty, noBuffered, ByteArray.append_empty, ByteArray.empty_append] at bytes
  have apart (path : FilePath) (held : state.selectedRetryPath path)
      (object : Nat) (bound : (observation seen.consumed).visible path = some object) : object ≠ replacement := by
    intro same
    have preserved := (inPending.live path held).1
    exact distinct path held (preserved.symm.trans (same ▸ bound))
  obtain ⟨_, handleAtSync, live, named, _⟩ := seen.syncs
  obtain ⟨effect, sameContents⟩ := fsync seen.synced (by rw [handleAtSync]; exact live)
  rw [handleAtSync, bytes] at effect
  rw [seen.consumeCensus, staged.atSync] at named
  have durable := effect.frames (footprint := state.selectedRetryPath) apart
  have parent := durable.weaken (fun path equal => .inr (.inl equal))
  have kept : state.SelectedRetryFrame (observation seen.consumed).storageObservation
      (observation seen.reached).storageObservation (inodes seen.consumed).visible (inodes seen.reached).visible :=
    ⟨fun path held => ⟨(durable.visible path held).1, by rw [sameContents]; intros; rfl⟩, durable.visible, parent⟩
  exact ⟨opened.trans (inPending.trans kept), (congrFun effect.names _).trans named,
    by simpa [RunDirectoryInodeView.storageObservation] using effect.bytes replacement,
    sameContents ▸ bytes⟩

/-- The actual rename transfers the synced staging inode to the keeper
name. The old keeper and scratch names are outside the immutable paths. -/
theorem NativeLongKeeperRenameHeap.preservesSelectedReplacement
    (state : NativeReadyState) (valid : state.Valid) (sameDirectory : state.session.directory = directory)
    (keeperStart : state.writer.wal.active.first ≤ layout.keeper.first)
    (seen : NativeLongKeeperRenameHeap synced rename)
    (stagedBytes : (observe synced.reached).files.bytes replacement = [layout.keeper.bytes])
    (stagedVisible : visible synced.reached replacement = layout.keeper.bytes)
    (frame : rename (directory.file .stagedWal) (directory.file (.walSegment layout.keeper.first)) synced.reached =
      .ok () seen.reached →
      (∀ path, path ≠ directory.file .stagedWal → path ≠ directory.file (.walSegment layout.keeper.first) →
        (observe seen.reached).files.names path = (observe synced.reached).files.names path) ∧
      (∀ names ∈ (observe seen.reached).crashNames, ∃ prior ∈ (observe synced.reached).crashNames,
        ∀ path, path ≠ directory.file .stagedWal → path ≠ directory.file (.walSegment layout.keeper.first) →
          names path = prior path) ∧
      (∀ path, state.selectedRetryPath path ∨ path = directory.file .stagedWal →
        ∀ inode, (observe synced.reached).files.names path = some inode →
          (observe seen.reached).files.bytes inode = (observe synced.reached).files.bytes inode ∧
          visible seen.reached inode = visible synced.reached inode)) :
    state.SelectedRetryFrame (observe synced.reached) (observe seen.reached) (visible synced.reached) (visible seen.reached) ∧
      (observe seen.reached).files.names (directory.file (.walSegment layout.keeper.first)) = some replacement ∧
      (observe seen.reached).files.bytes replacement = [layout.keeper.bytes] ∧
      visible seen.reached replacement = layout.keeper.bytes := by
  obtain ⟨unchanged, survivors, payload⟩ := frame seen.renamed
  have offStage {path} (kept : state.selectedRetryPath path) : path ≠ directory.file .stagedWal := by
    rw [← sameDirectory]
    exact state.stagedWalOutsideRetryFootprint path kept
  have offKeeper {path} (kept : state.selectedRetryPath path) : path ≠ directory.file (.walSegment layout.keeper.first) := by
    rw [← sameDirectory]
    exact NativeReadyState.protectedPathNeWalFromActive valid kept keeperStart
  have durable : (observe synced.reached).Frames state.selectedRetryPath (observe seen.reached) := by
    refine ⟨?_, ?_⟩
    · intro path kept
      exact ⟨unchanged path (offStage kept) (offKeeper kept), fun inode named => (payload path (.inl kept) inode named).1⟩
    · intro names allowed
      obtain ⟨prior, admitted, stays⟩ := survivors names allowed
      exact ⟨prior, admitted, fun path kept => stays path (offStage kept) (offKeeper kept)⟩
  have live : (⟨(observe synced.reached).files.names, fun inode => [visible synced.reached inode]⟩ :
      CheckpointSurvivingFiles).Frames state.selectedRetryPath
      ⟨(observe seen.reached).files.names, fun inode => [visible seen.reached inode]⟩ :=
    fun path kept => ⟨(durable.visible path kept).1, fun inode named =>
      congrArg (fun bytes => [bytes]) (payload path (.inl kept) inode named).2⟩
  obtain ⟨source, _, _, _, moved, _⟩ := seen.movesStagedInode
  obtain ⟨durableStage, liveStage⟩ := payload (directory.file .stagedWal) (.inr rfl) replacement source
  exact ⟨⟨live, durable.visible, durable.weaken (fun _ root => .inr (.inl root))⟩,
    moved, durableStage.trans stagedBytes, liveStage.trans stagedVisible⟩

/-- The literal staged-file fsync stores the selected prefix. The
rename moves the same inode, and the final directory fsync settles
its keeper binding together with the other selected children. -/
theorem NativeLongKeeperSettlementHeap.readyStorage
    (seen : NativeLongKeeperSettlementHeap renamed)
    {state : NativeReadyState}
    (sameDirectory : state.session.directory = directory) (sameCensus : state.census = finish.census)
    (sameSlot : state.directorySlot = admission.cached) (sameFirst : state.writer.wal.active.first = layout.keeper.first)
    (sameBytes : state.writer.wal.active.bytes = layout.keeper.bytes)
    (protectedFiles : NativeReadyProtectedStorage state (observe renamed.reached).files)
    (marker : (observe renamed.reached).files.Stored (state.session.directory.file .walBoundary)
      (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64))
    (rootSettled : ∀ names ∈ (observe renamed.reached).crashNames,
      names state.session.directory.path = (observe renamed.reached).files.names state.session.directory.path)
    (stageLive : visible synced.consumed replacement = layout.keeper.bytes)
    (stageEffect : sync.sync staged.descriptor synced.consumed = .ok () synced.reached →
      (view.handle synced.consumed staged.descriptor).2.1 ∈ (view.descriptors synced.consumed).slots →
      RegularFileSyncEffect ((view.handle synced.consumed staged.descriptor).1.inode
        (view.handle synced.consumed staged.descriptor).2.1.description)
        [visible synced.consumed replacement] (observe synced.consumed) (observe synced.reached) ∧
      visible synced.reached replacement = visible synced.consumed replacement)
    (renameEffect : rename (directory.file .stagedWal) (directory.file (.walSegment layout.keeper.first))
      synced.reached = .ok () renamed.reached →
      (observe synced.reached).files.names (directory.file .stagedWal) = some replacement →
      (observe renamed.reached).files.bytes replacement = (observe synced.reached).files.bytes replacement ∧
      visible renamed.reached replacement = visible synced.reached replacement)
    (directoryEffect : sync.sync seed.handle renamed.reached = .ok () seen.reached →
      (view.handle renamed.reached seed.handle).2.1 ∈ (view.descriptors renamed.reached).slots →
      (observe renamed.reached).files.names directory.path = some
        ((view.handle renamed.reached seed.handle).1.inode (view.handle renamed.reached seed.handle).2.1.description) →
      WalRootSyncEffect directory true (observe renamed.reached) (observe seen.reached) ∧
      (observe renamed.reached).Frames (· = state.session.directory.path) (observe seen.reached) ∧
      visible seen.reached replacement = visible renamed.reached replacement) :
    view.descriptors seen.reached = state.census ∧ NativeReadyStorage state (observe seen.reached) ∧
    ∀ inode, (observe seen.reached).files.names (state.session.directory.file (.walSegment state.writer.wal.active.first)) =
      some inode → visible seen.reached inode = state.writer.wal.active.bytes := by
  have ran := seen.returns
  obtain ⟨_, stagedHandle, stagedLive, _, _⟩ := synced.syncs
  obtain ⟨persisted, stagedContents⟩ := stageEffect synced.synced (by rw [stagedHandle]; exact stagedLive)
  rw [stagedHandle] at persisted
  change RegularFileSyncEffect replacement [visible synced.consumed replacement]
    (observe synced.consumed) (observe synced.reached) at persisted
  obtain ⟨staging, oldBinding, differentBindings, detached, keeper, _⟩ := renamed.movesStagedInode
  obtain ⟨movedBytes, movedContents⟩ := renameEffect renamed.renamed staging
  have root := protectedFiles.directoryBound
  rw [sameDirectory, sameCensus, sameSlot, finish.sameCensusObjects] at root
  obtain ⟨children, parent, keptContents⟩ := directoryEffect seen.synced
    (by rw [ran.directoryAtIssue]; exact ran.directoryLive)
    (by rw [ran.directoryAtIssue]; exact root)
  have sourceAtIssue := (congrFun persisted.names (directory.file .stagedWal)).symm.trans staging
  have distinct : replacement ≠ finish.rename.original.active := by
    intro same
    exact differentBindings (staging.trans ((congrArg some same).trans oldBinding.symm))
  have ⟨ready, _, _, _, _, live⟩ := NativeReadyStorage.afterKeeperReplacement state observe visible
    (by simpa only [sameDirectory] using sourceAtIssue) (stageLive.trans sameBytes.symm)
    persisted stagedContents
    (by rw [sameDirectory, sameFirst]; exact oldBinding) distinct
    (by rw [sameDirectory, sameFirst]; exact keeper.trans staging.symm)
    (by rw [sameDirectory]; exact detached) movedBytes movedContents protectedFiles marker rootSettled
    (.refl _ _) rfl (sameDirectory.symm ▸ children) parent keptContents
  exact ⟨(congrArg (fun observed => observed.2.1) ran.final).trans sameCensus.symm, ready, live⟩

end Alvoki.Storage.DiskSession
