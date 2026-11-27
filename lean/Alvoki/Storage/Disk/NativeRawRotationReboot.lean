import Alvoki.Storage.Disk.NativeRawRotationDirectoryError
import Alvoki.Storage.Disk.NativeRotationReadyStorage
import Alvoki.Storage.Disk.NativeRotationWalWindow
import Alvoki.Storage.Disk.NativeAlignedWriteRecovery

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentRepair

/-- At the issued directory barrier, the synced empty successor has a
live name. An earlier namespace can still omit that inode. -/
structure RotationSuccessorAtSync (directory : DiskDirectory) (start inode : Nat)
    (storage : CheckpointStorageObservation) : Prop where
  named : storage.files.names (directory.file (.walSegment start)) = some inode
  possible : ∀ names ∈ storage.crashNames,
    names (directory.file (.walSegment start)) = none ∨ names (directory.file (.walSegment start)) = some inode
  durable : storage.files.bytes inode = [ByteArray.empty]

/-- For a nonempty rotation, the successor offset is later than every
start in the retained WAL. -/
theorem SegmentedWriterState.RetainedReady.successorOutsideWal {directory : DiskDirectory}
    {descriptor : Nat} {writer : SegmentedWriterState}
    (ready : writer.RetainedReady directory descriptor)
    (nonempty : writer.installed.activeFirst < writer.installed.walBytes / WAL.frameSize) :
    writer.rotationInstalled.activeFirst ∉ writer.wal.segments.map WalSegment.first := by
  have sameEnd : writer.wal.active.last = writer.rotationInstalled.activeFirst :=
    ready.layout.activeEnd.trans ready.rotationAtEnd.symm
  intro present
  obtain ⟨segment, member, atEnd⟩ := List.mem_map.mp present
  have rotates := ready.rotationInput nonempty
  rcases List.mem_append.mp member with earlier | active
  · exact Nat.ne_of_lt (Nat.lt_trans (rotates.sealedBefore segment earlier) rotates.nonempty) (atEnd.trans sameEnd.symm)
  · obtain rfl := List.mem_singleton.mp active
    exact Nat.ne_of_lt rotates.nonempty (atEnd.trans sameEnd.symm)

/-- The old recovery files and bounded WAL names that the exclusive
successor cannot replace. Absent offsets belong to the same footprint. -/
def NativeReadyState.rotationProtectedScope (state : NativeReadyState) (first through : Nat) (path : FilePath) : Prop :=
  state.crashPath path ∨ ∃ start, first ≤ start ∧ start ≤ through ∧
    start ≠ state.writer.rotationInstalled.activeFirst ∧ path = state.session.directory.file (.walSegment start)

section ExclusiveSuccessor

variable {heap image : Type} {directory : DiskDirectory} {writer : SegmentedWriterState}
  {calls : OpenRotationCallbacks heap}
  {stager : RawWalStageCalls heap} {raw : RawSyncCalls heap} {files : DiskTable.OpenSyncFiles}
  {cache : OpenSyncCacheRefs files directory.path} {entry synced : heap}
  {filePrefix : calls.SuccessorFilePrefix directory writer.rotationInstalled.activeFirst entry synced}

variable (receipt : filePrefix.ExclusiveSync stager raw cache) (view : OpenCloseHeapView heap image)

local notation "createdInode" => OpenCloseHeapView.capturedInode view receipt.opened receipt.handle
local notation "start" => writer.rotationInstalled.activeFirst
local notation "successorPath" => directory.file (DiskFile.walSegment start)

/-- Scoped effects at the exact callbacks that create and sync the
successor. The later cached directory read keeps these file facts. -/
structure OpenRotationCallbacks.SuccessorFilePrefix.ExclusiveSync.SuccessorEffects
    (storage : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (beforePoison rootIssued : heap) : Prop where
  poison : WalNamePresenceFrame directory start start (storage beforePoison) (storage entry)
  probe : WalNamePresenceFrame directory start start (storage entry) (storage filePrefix.afterRead)
  create : ExclusiveCreateNameEffect successorPath createdInode (storage filePrefix.afterRead) (storage receipt.opened)
  empty : visible receipt.opened createdInode = ByteArray.empty
  target : RawFsyncTarget view receipt.opened receipt.issued receipt.handle
  beforeFileSync :
    let frame before after := (storage before).Frames (· = successorPath) (storage after) ∧
      visible after createdInode = visible before createdInode
    frame receipt.opened filePrefix.beforeSync ∧ frame filePrefix.beforeSync receipt.loaded ∧
      frame receipt.loaded receipt.issued
  sync : (view.handle receipt.issued receipt.handle).2.1 ∈ (view.descriptors receipt.issued).slots →
    let inode := (view.descriptors receipt.issued).inode (view.handle receipt.issued receipt.handle).2.1.description
    (storage receipt.issued).files.names successorPath = some inode →
    RegularFileSyncEffect inode [visible receipt.issued inode] (storage receipt.issued) (storage synced)
  rootLoad : ∀ {rootHandle}, raw.readDirectory cache.directory synced = .ok (some rootHandle) rootIssued →
    (storage synced).Frames (· = successorPath) (storage rootIssued)

/-- Each reached callback preserves the old files and names in scope.
The newly created inode is distinct from any inode already named there. -/
structure OpenRotationCallbacks.SuccessorFilePrefix.ExclusiveSync.PreservesFiles
    (storage : heap → CheckpointStorageObservation) (scope : FilePath → Prop)
    (beforePoison rootIssued : heap) : Prop where
  poison : (storage beforePoison).Frames scope (storage entry)
  probe : (storage entry).Frames scope (storage filePrefix.afterRead)
  create : (storage filePrefix.afterRead).Frames scope (storage receipt.opened)
  fresh : ∀ path, scope path → (storage filePrefix.afterRead).files.names path ≠ some createdInode
  remember : (storage receipt.opened).Frames scope (storage filePrefix.beforeSync)
  load : (storage filePrefix.beforeSync).Frames scope (storage receipt.loaded)
  consume : (storage receipt.loaded).Frames scope (storage receipt.issued)
  rootLoad : ∀ {handle}, raw.readDirectory cache.directory synced = .ok (some handle) rootIssued →
    (storage synced).Frames scope (storage rootIssued)

private theorem exclusiveFileSyncEffect
    {storage : heap → CheckpointStorageObservation} {visible : heap → Nat → ByteArray}
    {beforePoison rootIssued : heap} (effects : receipt.SuccessorEffects view storage visible beforePoison rootIssued) :
    (storage receipt.issued).files.names successorPath = some createdInode ∧
    RegularFileSyncEffect createdInode [ByteArray.empty] (storage receipt.issued) (storage synced) := by
  obtain ⟨remember, load, consume⟩ := effects.beforeFileSync
  have retained := remember.1.trans (load.1.trans consume.1)
  have nameAtSync := (retained.visible successorPath rfl).1.trans effects.create.named
  have emptyAtSync : visible receipt.issued createdInode = ByteArray.empty :=
    consume.2.trans (load.2.trans (remember.2.trans effects.empty))
  have sameInode := effects.target.inode
  have observed := effects.sync effects.target.live (sameInode.symm ▸ nameAtSync)
  rw [sameInode, emptyAtSync] at observed
  exact ⟨nameAtSync, observed⟩

/-- Reuse the effect on the actual successor descriptor to frame every
old inode and name through the file sync and the reached root load. -/
theorem OpenRotationCallbacks.SuccessorFilePrefix.ExclusiveSync.preservesFilesAtRootIssue
    {storage : heap → CheckpointStorageObservation} {visible : heap → Nat → ByteArray}
    {scope : FilePath → Prop} {beforePoison rootIssued : heap} {rootHandle : IO.FS.Handle}
    (loadedRoot : raw.readDirectory cache.directory synced = .ok (some rootHandle) rootIssued)
    (effects : receipt.SuccessorEffects view storage visible beforePoison rootIssued)
    (frames : receipt.PreservesFiles view storage scope beforePoison rootIssued) :
    (storage beforePoison).Frames scope (storage rootIssued) := by
  have fromCreate := frames.create.trans (frames.remember.trans (frames.load.trans frames.consume))
  have synced := (exclusiveFileSyncEffect receipt view effects).2.frames (footprint := scope) (by
    intro path inside inode named same
    exact frames.fresh path inside ((fromCreate.visible path inside).1.symm.trans (same ▸ named)))
  exact frames.poison.trans (frames.probe.trans (fromCreate.trans (synced.trans (frames.rootLoad loadedRoot))))

/-- The settled WAL catalog excludes the successor through the probe.
Follow the inode created at that name through file fsync to the issued
root barrier. -/
theorem OpenRotationCallbacks.SuccessorFilePrefix.ExclusiveSync.observesSuccessorAtRootIssue
    (storage : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    {beforePoison : heap} {descriptor : Nat}
    (ready : writer.RetainedReady directory descriptor)
    (nonempty : writer.installed.activeFirst < writer.installed.walBytes / WAL.frameSize)
    (window : writer.wal.SettledNamespaceWindow directory start start (storage beforePoison))
    {rootHandle : IO.FS.Handle} {issued : heap}
    (loadedRoot : raw.readDirectory cache.directory synced = .ok (some rootHandle) issued)
    (effects : receipt.SuccessorEffects view storage visible beforePoison issued) :
    RotationSuccessorAtSync directory start createdInode
      (storage issued) := by
  let inode := createdInode
  obtain ⟨remember, load, consume⟩ := effects.beforeFileSync
  have beforeCreate := (effects.poison.trans effects.probe).preservesNamespaceWindow window
  have missing (names : FilePath → Option Nat) (catalog : writer.wal.NamespaceWindow directory start start names) :
      names successorPath = none := by
    cases bound : names successorPath with
    | none => rfl
    | some found =>
      exact False.elim (ready.successorOutsideWal nonempty
        ((catalog start (Nat.le_refl _) (Nat.le_refl _)).1 (by simp only [bound, Option.isSome_some])))
  have created := effects.create
  have openedChoices (names : FilePath → Option Nat) (chosen : names ∈ (storage receipt.opened).crashNames) :
      names successorPath = none ∨ names successorPath = some inode := by
    rcases created.survivors names chosen with installed | ⟨prior, fromLive | fromCrash, same⟩
    · exact .inr installed
    · exact .inl (same.trans (fromLive ▸ missing _ beforeCreate.1))
    · exact .inl (same.trans (missing _ (beforeCreate.2 prior fromCrash)))
  have retained := remember.1.trans (load.1.trans consume.1)
  obtain ⟨nameAtSync, observed⟩ := exclusiveFileSyncEffect receipt view effects
  have fileSynced : (storage synced).files.names successorPath = some inode :=
    (congrFun observed.names _).trans nameAtSync
  have bytesSynced : (storage synced).files.bytes inode = [ByteArray.empty] := by
    simpa [inode] using observed.bytes inode
  have rootKeeps := effects.rootLoad loadedRoot
  refine ⟨(rootKeeps.visible successorPath rfl).1.trans fileSynced, ?_,
    ((rootKeeps.visible successorPath rfl).2 inode fileSynced).trans bytesSynced⟩
  intro names chosen
  obtain ⟨fsynced, beforeRoot, sameRoot⟩ := rootKeeps.survivors names chosen
  have atFile : fsynced ∈ (storage receipt.issued).crashNames := observed.crashNames ▸ beforeRoot
  obtain ⟨prior, atBirth, sameFile⟩ := retained.survivors fsynced atFile
  have sameName := (sameRoot successorPath rfl).trans (sameFile successorPath rfl)
  exact sameName.symm ▸ openedChoices prior atBirth

end ExclusiveSuccessor

/-- Project the successor from the same surviving directory map as the
rest of the rotation. An effective barrier forces the live binding. -/
theorem WalRootSyncEffect.selectsRotationSuccessor {directory : DiskDirectory} {start inode : Nat}
    {effective : Bool} {issued failed : CheckpointStorageObservation}
    (effect : WalRootSyncEffect directory effective issued failed)
    (successor : RotationSuccessorAtSync directory start inode issued)
    {names : FilePath → Option Nat} (chosen : names ∈ failed.crashNames) :
    let path := directory.file (.walSegment start)
    (names path = none ∨ names path = some inode ∧ failed.files.bytes inode = [ByteArray.empty]) ∧
    (effective = true → names path = some inode) := by
  intro path
  have settled (applied : effective = true) : names path = some inode :=
    (effect.settled applied names chosen (.walSegment start)).trans
      ((effect.visible (.walSegment start)).trans successor.named)
  have bytes (sampled : names path = some inode) : failed.files.bytes inode = [ByteArray.empty] :=
    (effect.bytes names (.inr chosen) (.walSegment start) inode sampled).trans successor.durable
  refine ⟨?_, settled⟩
  cases applied : effective with
  | true => exact .inr ⟨settled applied, bytes (settled applied)⟩
  | false =>
    obtain ⟨prior, possible, keep⟩ := effect.unchanged applied names chosen
    rcases successor.possible prior possible with missing | present
    · exact .inl ((keep (.walSegment start)).trans missing)
    · have survived := (keep (.walSegment start)).trans present
      exact .inr ⟨survived, bytes survived⟩

/-- Choose the retained WAL writer from the sampled successor name.
This determines the recovery layout without changing the failed handle's phase. -/
def NativeReadyState.rotationWriterAtSample (state : NativeReadyState) (valid : state.Valid)
    (names : FilePath → Option Nat) : SegmentedWriterState :=
  if (names (state.session.directory.file (.walSegment state.writer.rotationInstalled.activeFirst))).isSome then
    state.writer.rotated valid.retained.rotationTarget
  else state.writer

theorem NativeReadyState.rotationWriterAtSample_retained {state : NativeReadyState} (valid : state.Valid)
    (nonempty : state.writer.installed.activeFirst < state.writer.installed.walBytes / WAL.frameSize)
    (names : FilePath → Option Nat) : (state.rotationWriterAtSample valid names).RetainedReady
      state.session.directory state.session.descriptor := by
  unfold NativeReadyState.rotationWriterAtSample
  split
  · exact valid.retained.rotates nonempty ⟨rfl, rfl, rfl⟩
  · exact valid.retained

theorem NativeReadyState.rotationWriterAtSample_history {state : NativeReadyState} (valid : state.Valid)
    (names : FilePath → Option Nat) : (state.rotationWriterAtSample valid names).history = state.writer.history := by
  unfold NativeReadyState.rotationWriterAtSample
  split <;> rfl

theorem NativeReadyState.rotationWriterAtSample_pair {state : NativeReadyState} (valid : state.Valid)
    (names : FilePath → Option Nat) : (state.rotationWriterAtSample valid names).target.pair = state.writer.target.pair := by
  unfold NativeReadyState.rotationWriterAtSample
  split <;> rfl

/-- The chosen map determines which layout survives. Other offsets are
transported by the existing rotation name frame, including absent names. -/
theorem NativeReadyState.rotationWriterAtSample_namespace {state : NativeReadyState} (valid : state.Valid)
    (nonempty : state.writer.installed.activeFirst < state.writer.installed.walBytes / WAL.frameSize)
    {first through : Nat} {entry failed : CheckpointStorageObservation}
    (initial : ∀ start, first ≤ start → start ≤ through → start ≠ state.writer.rotationInstalled.activeFirst →
      state.writer.wal.SettledNamespaceWindow state.session.directory start start entry)
    (framed : RotationWalNameFrame state.session.directory first through state.writer.rotationInstalled.activeFirst entry failed)
    {names : FilePath → Option Nat} (chosen : names ∈ failed.crashNames) :
    (state.rotationWriterAtSample valid names).wal.NamespaceWindow state.session.directory first through names := by
  let wal := state.writer.wal
  let successor := state.writer.rotationInstalled.activeFirst
  have sameEnd : wal.active.last = successor := valid.retained.layout.activeEnd.trans valid.retained.rotationAtEnd.symm
  have newStarts : wal.rotated.segments.map WalSegment.first = wal.segments.map WalSegment.first ++ [successor] := by
    change (wal.segments ++ [(⟨wal.active.last, wal.active.last, ByteArray.empty⟩ : WalSegment)]).map WalSegment.first = _
    rw [List.map_append, List.map_cons, List.map_nil, sameEnd]
  have fresh := valid.retained.successorOutsideWal nonempty
  have other start (lower : first ≤ start) (upper : start ≤ through) (apart : start ≠ successor) :
      (names (state.session.directory.file (.walSegment start))).isSome = true ↔ start ∈ wal.segments.map WalSegment.first :=
    ((framed start lower upper apart).preservesNamespaceWindow (initial start lower upper apart)).2
      names chosen start (Nat.le_refl _) (Nat.le_refl _)
  unfold NativeReadyState.rotationWriterAtSample
  cases present : (names (state.session.directory.file (.walSegment successor))).isSome with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    intro start lower upper
    by_cases same : start = successor
    · subst start
      simp only [present, Bool.false_eq_true, false_iff]
      exact fresh
    · exact other start lower upper same
  | true =>
    simp only [↓reduceIte]
    exact WalSegmentImage.namespaceWindowAfterRotation newStarts present other

/-- The successor file work frames the root name and the inode recorded
by the directory cache. The active and pending cells may change. -/
abbrev RotationRootFrame {heap image : Type} (view : OpenCloseHeapView heap image)
    (directory : IO.Ref (Option IO.FS.Handle)) (storage : heap → CheckpointStorageObservation)
    (root : FilePath) (before after : heap) : Prop :=
  let cached atHeap := (view.directory atHeap directory).map (view.capturedInode atHeap)
  (storage after).files.names root = (storage before).files.names root ∧ cached after = cached before

/-- The final rotation barrier invokes fsync on the handle loaded from
the original directory cache. -/
structure OpenRotationCallbacks.FailedRootBarrier {heap : Type} (calls : OpenRotationCallbacks heap)
    (raw : RawSyncCalls heap) {files : DiskTable.OpenSyncFiles} {root : FilePath}
    (cache : OpenSyncCacheRefs files root) (synced : heap) where
  handle : IO.FS.Handle
  issued : heap
  failed : heap
  cause : IO.Error
  route : calls.sync root synced = raw.group root cache.directory cache.active cache.pending #[root] synced
  loaded : raw.readDirectory cache.directory synced = .ok (some handle) issued
  returned : raw.fsync handle issued = .error cause failed

/-- The reached prefix and cached read preserve the parent binding and
the issued fsync acts on its actual live descriptor. -/
structure OpenRotationCallbacks.SuccessorFilePrefix.RootErrorEffects {heap image : Type}
    {calls : OpenRotationCallbacks heap} {directory : DiskDirectory} {start : Nat} {entry synced : heap}
    (filePrefix : calls.SuccessorFilePrefix directory start entry synced)
    {raw : RawSyncCalls heap} {files : DiskTable.OpenSyncFiles} {cache : OpenSyncCacheRefs files directory.path}
    (barrier : calls.FailedRootBarrier raw cache synced) (view : OpenCloseHeapView heap image)
    (storage : heap → CheckpointStorageObservation) (effective : Bool) (beforePoison : heap) : Prop where
  target : RawFsyncTarget view synced barrier.issued barrier.handle
  prefixFrames :
    let frame := RotationRootFrame view cache.directory storage directory.path
    frame beforePoison entry ∧ frame entry filePrefix.afterRead ∧
    (filePrefix.observed = none → frame filePrefix.afterRead filePrefix.beforeSync) ∧
    frame filePrefix.beforeSync synced
  cached : view.directory synced cache.directory = some barrier.handle
  named : (storage barrier.issued).files.names directory.path = (storage synced).files.names directory.path
  rootLive : (storage barrier.failed).files.names directory.path = (storage barrier.issued).files.names directory.path
  rootSurvivors : ∀ names ∈ (storage barrier.failed).crashNames, ∃ prior,
    (prior = (storage barrier.issued).files.names ∨ prior ∈ (storage barrier.issued).crashNames) ∧
    names directory.path = prior directory.path
  sync : (view.handle barrier.issued barrier.handle).2.1 ∈ (view.descriptors barrier.issued).slots →
    (storage barrier.issued).files.names directory.path =
      some ((view.descriptors barrier.issued).inode (view.handle barrier.issued barrier.handle).2.1.description) →
    WalRootSyncEffect directory effective (storage barrier.issued) (storage barrier.failed)

/-- Adapt the sampled writer to the shared reboot observation. The
session and descriptors still come from the original ready position. -/
abbrev NativeReadyState.withRotationSample (state : NativeReadyState) (valid : state.Valid)
    (names : FilePath → Option Nat) : NativeReadyState :=
  {state with writer := state.rotationWriterAtSample valid names}

section SampledReader

variable {heap stream : Type} {state : NativeReadyState} {view : OpenCloseHeapView heap FileImage}
  {storage : heap → CheckpointStorageObservation} {visible : heap → Nat → ByteArray}
  {failed rebooted : heap} {source : RawMarkedOpenInterpreter heap stream}
  {namespaceView : DirectoryReadNamespace} {root : DeviceInode}
  (valid : state.Valid)

local notation "directory" => state.session.directory
local notation "names" => fun h => CheckpointSurvivingFiles.names (CheckpointStorageObservation.files (storage h))
local notation "successor" => state.writer.rotationInstalled.activeFirst
local notation "picked" => state.withRotationSample valid (names rebooted)

/-- The directory sample chooses the new keeper before opening. The
literal reopening shares the ordinary WAL reader and retains the earlier
history whether the sampled namespace lost or kept the empty successor. -/
theorem NativeReadyState.visibleWalAtRotationSample
    (chosen : names rebooted ∈ (storage failed).crashNames)
    (sampled : ∀ path, checkpointSurvivorPath directory (picked).writer (picked).writer.target.pair.manifest path →
      ∀ inode, names rebooted path = some inode → visible rebooted inode ∈ (storage failed).files.bytes inode)
    (old : NativeReadyStorage state (storage failed))
    (ready : (picked).writer.RetainedReady directory state.session.descriptor)
    {inode : Nat}
    (choice : names rebooted ((directory).file (.walSegment successor)) = none ∨
      names rebooted ((directory).file (.walSegment successor)) = some inode ∧ (storage failed).files.bytes inode = [ByteArray.empty])
    (window : (picked).writer.wal.NamespaceWindow directory 0 (picked).writer.target.range.through (names rebooted))
    (noManifest : state.writer.target.pair.manifest = none) :
    (picked).writer.VisibleWalFiles directory (names rebooted) (visible rebooted) := by
  have pairEq := state.rotationWriterAtSample_pair valid (names rebooted)
  have oldName (path : FilePath) (inside : state.crashPath path) :
      names rebooted path = (storage failed).files.names path :=
    old.settled _ chosen path inside
  have frame : NativeReadyProtectedStorage picked (storage failed).files ∧
      (∀ path, (picked).writeFramePath path → state.crashPath path) := by
    cases found : names rebooted ((directory).file (.walSegment successor)) with
    | none =>
      have unrotated : picked = state := by
        simp only [NativeReadyState.withRotationSample, NativeReadyState.rotationWriterAtSample, found,
          Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      rw [unrotated]
      exact ⟨old.toNativeReadyProtectedStorage, fun _ keep => NativeReadyState.crashPath_iff_write.mpr (.inr (.inr keep))⟩
    | some child =>
      have rotated : (picked).writer = state.writer.rotated valid.retained.rotationTarget := by
        simp only [NativeReadyState.rotationWriterAtSample, found, Option.isSome_some, ↓reduceIte]
      exact ⟨old.protectedAfterRotation valid rotated rfl rfl rfl,
        fun _ keep => NativeReadyState.rotationProtectedPaths valid rotated rfl keep⟩
  obtain ⟨protectedFiles, _⟩ := frame.1.samplesRebootFiles (names rebooted) (visible rebooted)
    (fun path inside => oldName path (frame.2 path inside)) sampled
  let markerPath := (directory).file .walBoundary
  have marker : state.writer.target.pair.walBoundary = some (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64) :=
    (congrArg DirectoryPublication.Bindings.walBoundary valid.retained.resumed.ready.selected).symm.trans
      (congrArg Publication.Image.active valid.retained.resumed.markerImage)
  obtain ⟨markerInode, markerNamed, markerBytes⟩ :=
    old.marker.samplesAtBinding (names rebooted) (visible rebooted)
      (oldName markerPath (NativeReadyState.crashPath_iff_write.mpr (.inl rfl)))
      (sampled markerPath (.inr (.inl (.inl rfl))))
  have marked : (names rebooted markerPath).map (visible rebooted) = (picked).writer.target.pair.walBoundary := by
    rw [markerNamed, Option.map_some, markerBytes, pairEq, marker]
  have trimmed : (picked).writer.target.trimmed = (picked).writer.wal.active.bytes := by
    rw [ready.resumed.contents, ready.active, ready.layout.activeBytes]
  let keeperPath := (directory).file (.walSegment (picked).writer.wal.active.first)
  have payload : (names rebooted keeperPath).map (visible rebooted) = some (picked).writer.target.trimmed := by
    rw [trimmed]
    rcases choice with missing | ⟨present, durable⟩
    · have unrotated : (picked).writer = state.writer := by
        simp only [NativeReadyState.rotationWriterAtSample, missing,
          Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      let oldKeeper := (directory).file (.walSegment state.writer.wal.active.first)
      have path : keeperPath = oldKeeper :=
        congrArg (fun writer : SegmentedWriterState => (directory).file (.walSegment writer.wal.active.first)) unrotated
      obtain ⟨oldInode, named, bytes⟩ := old.keeper.samplesAtBinding (names rebooted) (visible rebooted)
        (oldName oldKeeper (NativeReadyState.crashPath_iff_write.mpr (.inr (.inl rfl))))
        (fun inode bound => sampled keeperPath (.inr (.inl (.inr (.inl rfl)))) inode (path.symm ▸ bound))
      rw [path, named, Option.map_some, bytes, unrotated]
    · have rotated : (picked).writer = state.writer.rotated valid.retained.rotationTarget := by
        simp only [NativeReadyState.rotationWriterAtSample, present, Option.isSome_some, ↓reduceIte]
      have start : (picked).writer.wal.active.first = successor := by
        rw [rotated]
        exact valid.retained.layout.activeEnd.trans valid.retained.rotationAtEnd.symm
      have atKeeper : names rebooted keeperPath = some inode := by
        change names rebooted ((directory).file (.walSegment (picked).writer.wal.active.first)) = some inode
        rw [start]
        exact present
      have bytes := sampled keeperPath (.inr (.inl (.inr (.inl rfl)))) inode atKeeper
      rw [durable] at bytes
      rw [atKeeper, Option.map_some, List.mem_singleton.mp bytes, rotated]
      rfl
  have absent : (picked).writer.target.pair.manifest = none :=
    (congrArg DirectoryPublication.Bindings.manifest pairEq).trans noManifest
  have lock := protectedFiles.lockBound
  have manifestAbsent := protectedFiles.manifest
  rw [absent] at manifestAbsent
  have seals (segment : WalSegment) (member : segment ∈ (picked).writer.wal.sealed) :
      (names rebooted ((directory).file (.walSegment segment.first))).map (visible rebooted) = some segment.bytes := by
    obtain ⟨inode, bound, bytes⟩ := protectedFiles.sealedFiles segment member
    exact Option.map_eq_some_iff.mpr ⟨inode, bound, List.singleton_inj.mp bytes⟩
  exact ⟨⟨_, lock⟩, manifestAbsent, marked, ready.resumed.through ▸ window, seals, trimmed ▸ payload⟩

end SampledReader

/-- The filesystem effects through a failed root barrier select the keeper
and retained WAL files in one joint reboot sample. -/
theorem NativeOpenedPosition.samplesFailedRotationDirectory {heap : Type}
    {opened : NativeOpenedHandle heap} (current : NativeOpenedPosition opened)
    (calls : OpenRotationCallbacks heap) (raw : RawSyncCalls heap) (view : OpenCloseHeapView heap FileImage)
    (cache : OpenSyncCacheRefs opened.files opened.directory.path)
    (storage : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    {stager : RawWalStageCalls heap} {poisoned afterFileSync rebooted : heap} {effective : Bool}
    (filePrefix : calls.SuccessorFilePrefix opened.directory
      current.current.ready.state.writer.rotationInstalled.activeFirst poisoned afterFileSync)
    (file : filePrefix.ExclusiveSync stager raw cache)
    (barrier : calls.FailedRootBarrier raw cache afterFileSync)
    (fileEffects : file.SuccessorEffects view storage visible current.reached barrier.issued)
    (rootEffects : filePrefix.RootErrorEffects barrier view storage effective current.reached)
    (nonempty : current.current.ready.state.writer.installed.activeFirst <
      current.current.ready.state.writer.installed.walBytes / WAL.frameSize)
    (initial : current.WriteStorageEntry view
      ⟨cache.directory, cache.active, cache.pending, cache.references,
        (congrArg DiskDirectory.path current.directory).symm ▸ cache.atRoot⟩ (storage current.reached)
      (visible current.reached))
    (fileFrames : file.PreservesFiles view storage
      (current.current.ready.state.rotationProtectedScope 0 current.current.ready.state.writer.target.range.through)
      current.reached barrier.issued)
    (window : current.current.ready.state.writer.wal.SettledNamespaceWindow
      current.current.ready.state.session.directory 0 current.current.ready.state.writer.target.range.through
      (storage current.reached))
    (chosen : (storage rebooted).files.names ∈ (storage barrier.failed).crashNames) :
    let state := current.current.ready.state
    let directory := state.session.directory
    let names := (storage rebooted).files.names
    let path := directory.file (.walSegment state.writer.rotationInstalled.activeFirst)
    let selected := state.rotationWriterAtSample current.current.ready.readPrefix.refines.1 names
    let inode := view.capturedInode file.opened file.handle
    NativeReadyStorage state (storage barrier.failed) ∧ selected.RetainedReady directory state.session.descriptor ∧
    selected.history = state.writer.history ∧ selected.target.pair = state.writer.target.pair ∧
    selected.wal.NamespaceWindow directory 0 selected.target.range.through names ∧
    (names path = none ∨ names path = some inode ∧ (storage barrier.failed).files.bytes inode = [ByteArray.empty]) ∧
    (effective = true → names path = some inode) ∧
    ((∀ selectedPath, checkpointSurvivorPath directory selected selected.target.pair.manifest selectedPath →
        ∀ object, names selectedPath = some object → visible rebooted object ∈ (storage barrier.failed).files.bytes object) →
      state.writer.target.pair.manifest = none →
      selected.VisibleWalFiles directory names (visible rebooted)) := by
  intro state directory names path selected inode
  let valid := current.current.ready.readPrefix.refines.1
  let frame := RotationRootFrame view cache.directory storage opened.directory.path
  have trans {before middle after : heap} (early : frame before middle) (late : frame middle after) :
      frame before after := ⟨late.1.trans early.1, late.2.trans early.2⟩
  obtain ⟨poison, read, created, fileSync⟩ := rootEffects.prefixFrames
  have kept := trans poison (filePrefix.frames (frame := frame) trans read created fileSync)
  have selectedInode := kept.2.symm
  simp only [rootEffects.cached, Option.map_some] at selectedInode
  obtain ⟨original, bound, sameInode⟩ := Option.map_eq_some_iff.mp selectedInode
  have initialRoot := initial.root original bound
  rw [current.directory] at initialRoot
  have root := rootEffects.named.trans (kept.1.trans
    (initialRoot.trans (congrArg some (sameInode.trans rootEffects.target.inode.symm))))
  have effect := rootEffects.sync rootEffects.target.live root
  have ready : selected.RetainedReady directory state.session.descriptor :=
    state.rotationWriterAtSample_retained valid nonempty names
  have history : selected.history = state.writer.history := state.rotationWriterAtSample_history valid names
  have cutoff : selected.target.range.through = state.writer.target.range.through :=
    ready.resumed.through.trans ((congrArg List.length history).trans valid.retained.resumed.through.symm)
  have slice start (lower : 0 ≤ start) (upper : start ≤ state.writer.target.range.through) :
      state.writer.wal.SettledNamespaceWindow directory start start (storage current.reached) :=
    ⟨window.1.restrict lower upper, fun candidate allowed => (window.2 candidate allowed).restrict lower upper⟩
  have beforeRotation : state.writer.RetainedReady opened.directory state.session.descriptor :=
    current.directory ▸ valid.retained
  have successorBound : state.writer.rotationInstalled.activeFirst ≤ state.writer.target.range.through :=
    Nat.le_of_eq (valid.retained.rotationAtEnd.trans valid.retained.resumed.through.symm)
  have successorWindow : state.writer.wal.SettledNamespaceWindow opened.directory
      state.writer.rotationInstalled.activeFirst state.writer.rotationInstalled.activeFirst (storage current.reached) :=
    current.directory ▸ slice _ (Nat.zero_le _) successorBound
  have successor := file.observesSuccessorAtRootIssue view storage visible beforeRotation nonempty
    successorWindow barrier.loaded fileEffects
  have atIssue := file.preservesFilesAtRootIssue view barrier.loaded fileEffects fileFrames
  have effectAtDirectory : WalRootSyncEffect directory effective (storage barrier.issued) (storage barrier.failed) :=
    Eq.mpr (congrArg (fun dir => WalRootSyncEffect dir effective (storage barrier.issued) (storage barrier.failed))
      current.directory) effect
  have successorAtDirectory : RotationSuccessorAtSync directory state.writer.rotationInstalled.activeFirst inode
      (storage barrier.issued) :=
    Eq.mpr (congrArg (fun dir => RotationSuccessorAtSync dir state.writer.rotationInstalled.activeFirst inode
      (storage barrier.issued)) current.directory) successor
  obtain ⟨survives, settled⟩ := effectAtDirectory.selectsRotationSuccessor successorAtDirectory chosen
  have oldAtIssue := initial.physical.frame (atIssue.weaken fun _ held => Or.inl held)
  have sameDirectory : directory = opened.directory := current.directory
  have rootLive : (storage barrier.failed).files.names directory.path = (storage barrier.issued).files.names directory.path := by
    rw [sameDirectory]
    exact rootEffects.rootLive
  have rootSurvives (sample : FilePath → Option Nat) (chosen : sample ∈ (storage barrier.failed).crashNames) :
      sample directory.path = (storage barrier.failed).files.names directory.path := by
    obtain ⟨earlier, possible, sameName⟩ := rootEffects.rootSurvivors sample chosen
    have fromEarlier : sample directory.path = earlier directory.path := by
      rw [sameDirectory]
      exact sameName
    have fromReady : earlier directory.path = (storage barrier.issued).files.names directory.path := by
      rcases possible with live | predicted
      · rw [live]
      · exact oldAtIssue.settled earlier predicted directory.path
          (NativeReadyState.crashPath_iff_write.mpr (.inr (.inr (.inl rfl))))
    exact fromEarlier.trans (fromReady.trans rootLive.symm)
  have old := effectAtDirectory.preservesReadyStorage oldAtIssue rootLive rootSurvives
  have namesFrame : RotationWalNameFrame directory 0 state.writer.target.range.through
      state.writer.rotationInstalled.activeFirst (storage current.reached) (storage barrier.failed) := by
    intro start lower upper other
    have carried : WalNamePresenceFrame directory start start (storage current.reached) (storage barrier.issued) :=
      WalNamePresenceFrame.ofStorageFrame atIssue fun observed fromStart toStart => by
        have same : observed = start := Nat.le_antisymm toStart fromStart
        subst observed
        exact .inr ⟨start, lower, upper, other, rfl⟩
    exact carried.trans (WalNamePresenceFrame.ofRootSync effectAtDirectory)
  have catalog : selected.wal.NamespaceWindow directory 0 selected.target.range.through names := by
    rw [cutoff]
    exact state.rotationWriterAtSample_namespace valid nonempty (fun start low high _ => slice start low high)
      namesFrame chosen
  refine ⟨old, ready, history, state.rotationWriterAtSample_pair valid names,
    catalog, survives, settled, ?_⟩
  intro sampled noManifest
  exact @NativeReadyState.visibleWalAtRotationSample
    (storage := storage) («visible» := visible) (failed := barrier.failed) (rebooted := rebooted)
    (valid := valid) (chosen := chosen) (sampled := sampled)
    (old := old) (ready := ready) (choice := survives) (window := catalog) (noManifest := noManifest)

end Alvoki.Storage.DiskSession
