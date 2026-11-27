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

private theorem RotationRawSuccessor.observesSuccessorBinding {directory : DiskDirectory} {writer : SegmentedWriterState}
    {lookup : FilePath → Except IO.Error IO.FS.Metadata} {inventory : DescriptorInventory}
    {parent : RotationCreateParent directory writer lookup inventory} (created : RotationRawSuccessor parent)
    {storage : CheckpointStorageObservation} {visible : Nat → ByteArray}
    (observed : created.files.ObservesWalChild parent.root directory
      writer.rotationInstalled.activeFirst storage visible) :
    let path := directory.file (.walSegment writer.rotationInstalled.activeFirst)
    let inode := inventory.inode created.raw.description
    storage.files.names path = some inode ∧
    (∀ names ∈ storage.crashNames, names path = none ∨ names path = some inode) := by
  intro path inode
  let name := renderWalSegmentName writer.rotationInstalled.activeFirst
  have named : created.files.view.child parent.root name = some created.child.child := by
    have bound := created.child.binds
    rw [created.child.atRoot, created.child.atName] at bound
    exact bound
  have bound : storage.files.names (directory.file (.walSegment writer.rotationInstalled.activeFirst)) =
      some (inventory.inode created.raw.description) := by
    have exactChild := observed.live.trans (congrArg (Option.map created.files.view.modelObject) named)
    simpa only [Option.map_some, created.inode] using exactChild
  refine ⟨bound, ?_⟩
  intro names chosen
  obtain ⟨option, allowed, exactChild⟩ := List.mem_map.mp (observed.survivors names chosen)
  rcases created.successorSurvivors option allowed with rfl | rfl
  · exact .inl exactChild.symm
  · change some (created.files.view.modelObject created.child.child) = _ at exactChild
    rw [created.inode] at exactChild
    exact .inr exactChild.symm

/-- The successful file sync of the exclusive-created inode supplies the
empty bytes and possible names observed at the issued root barrier. -/
theorem RotationRawSuccessor.observesSyncedSuccessor {directory : DiskDirectory} {writer : SegmentedWriterState}
    {lookup : FilePath → Except IO.Error IO.FS.Metadata} {inventory : DescriptorInventory}
    {parent : RotationCreateParent directory writer lookup inventory} (created : RotationRawSuccessor parent)
    {storage : CheckpointStorageObservation} {visible : Nat → ByteArray}
    (observed : (created.afterSync true).files.ObservesWalChild parent.root directory
      writer.rotationInstalled.activeFirst storage visible) :
    RotationSuccessorAtSync directory writer.rotationInstalled.activeFirst (inventory.inode created.raw.description)
      storage := by
  obtain ⟨bound, possible⟩ := (created.afterSync true).observesSuccessorBinding observed
  exact ⟨bound, possible, (observed.bytes _ bound).1.trans created.syncedBytes⟩

section ExclusiveSuccessor

variable {heap image : Type} {directory : DiskDirectory} {writer : SegmentedWriterState}
  {lookup : FilePath → Except IO.Error IO.FS.Metadata} {inventory : DescriptorInventory}
  {parent : RotationCreateParent directory writer lookup inventory} {calls : OpenRotationCallbacks heap}
  {stager : RawWalStageCalls heap} {raw : RawSyncCalls heap} {files : DiskTable.OpenSyncFiles}
  {cache : OpenSyncCacheRefs files directory.path} {entry synced : heap}
  {filePrefix : calls.SuccessorFilePrefix directory writer.rotationInstalled.activeFirst entry synced}

local notation "successorPath" => directory.file (DiskFile.walSegment writer.rotationInstalled.activeFirst)

/-- Start from the physical projection only at exclusive open, and
follow the actual remembered descriptor through the successful file
fsync to the issued root. Only the file fsync establishes durability. -/
theorem RotationRawSuccessor.observesSuccessorAtRootIssue (created : RotationRawSuccessor parent)
    (receipt : filePrefix.ExclusiveSync stager raw cache)
    (view : OpenCloseHeapView heap image)
    (storage : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    {rootHandle : IO.FS.Handle} {issued : heap}
    (loadedRoot : raw.readDirectory cache.directory synced = .ok (some rootHandle) issued)
    (atOpen : created.files.ObservesWalChild parent.root directory
      writer.rotationInstalled.activeFirst (storage receipt.opened) (visible receipt.opened))
    (openedInode : (view.handle receipt.opened receipt.handle).1.inode
      (view.handle receipt.opened receipt.handle).2.1.description = inventory.inode created.raw.description)
    (target : RawFsyncTarget view receipt.opened receipt.issued receipt.handle)
    (beforeFileSync :
      let inode := inventory.inode created.raw.description
      let frame before after := (storage before).Frames (· = successorPath) (storage after) ∧
        visible after inode = visible before inode
      frame receipt.opened filePrefix.beforeSync ∧ frame filePrefix.beforeSync receipt.loaded ∧
        frame receipt.loaded receipt.issued)
    (fileEffect : raw.fsync receipt.handle receipt.issued = .ok () synced →
      (view.handle receipt.issued receipt.handle).2.1 ∈ (view.descriptors receipt.issued).slots →
      let inode := (view.descriptors receipt.issued).inode (view.handle receipt.issued receipt.handle).2.1.description
      (storage receipt.issued).files.names successorPath = some inode →
      RegularFileSyncEffect inode [visible receipt.issued inode] (storage receipt.issued) (storage synced))
    (rootFrame : raw.readDirectory cache.directory synced = .ok (some rootHandle) issued →
      (storage synced).Frames (· = successorPath) (storage issued)) :
    RotationSuccessorAtSync directory writer.rotationInstalled.activeFirst (inventory.inode created.raw.description)
      (storage issued) := by
  let inode := inventory.inode created.raw.description
  obtain ⟨remember, load, consume⟩ := beforeFileSync
  obtain ⟨openedName, openedChoices⟩ := created.observesSuccessorBinding atOpen
  have openedEmpty : visible receipt.opened inode = ByteArray.empty :=
    (atOpen.bytes inode openedName).2.trans created.empty
  have retained := remember.1.trans (load.1.trans consume.1)
  have nameAtSync := (retained.visible successorPath rfl).1.trans openedName
  have emptyAtSync : visible receipt.issued inode = ByteArray.empty :=
    consume.2.trans (load.2.trans (remember.2.trans openedEmpty))
  have sameInode : (view.descriptors receipt.issued).inode
      (view.handle receipt.issued receipt.handle).2.1.description = inode :=
    target.inode.trans openedInode
  have observed := fileEffect receipt.sync target.live (sameInode.symm ▸ nameAtSync)
  rw [sameInode, emptyAtSync] at observed
  have fileSynced : (storage synced).files.names successorPath = some inode :=
    (congrFun observed.names _).trans nameAtSync
  have bytesSynced : (storage synced).files.bytes inode = [ByteArray.empty] := by
    simpa using observed.bytes inode
  have rootKeeps := rootFrame loadedRoot
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
  have fresh : successor ∉ wal.segments.map WalSegment.first := by
    intro present
    obtain ⟨segment, member, atEnd⟩ := List.mem_map.mp present
    have rotates := valid.retained.rotationInput nonempty
    rcases List.mem_append.mp member with earlier | active
    · exact Nat.ne_of_lt (Nat.lt_trans (rotates.sealedBefore segment earlier) rotates.nonempty) (atEnd.trans sameEnd.symm)
    · obtain rfl := List.mem_singleton.mp active
      exact Nat.ne_of_lt rotates.nonempty (atEnd.trans sameEnd.symm)
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

/-- At the error heap of the actual cached directory sync, preserve the
old recovery files and select the keeper using the observed reboot map.
The directory effect applies to the file handle issued by the cache read. -/
theorem NativeOpenedPosition.samplesFailedRotationDirectory {heap image : Type}
    {opened : NativeOpenedHandle heap} (current : NativeOpenedPosition opened)
    (raw : RawSyncCalls heap) (view : OpenCloseHeapView heap image)
    (cache : OpenSyncCacheRefs opened.files current.current.ready.state.session.directory.path)
    (storage : heap → CheckpointStorageObservation) {afterFileSync issued failed rebooted : heap}
    {handle : IO.FS.Handle} {cause : IO.Error} {effective : Bool} {inode first through : Nat}
    (loaded : raw.readDirectory cache.directory afterFileSync = .ok (some handle) issued)
    (target : RawFsyncTarget view afterFileSync issued handle)
    (root : (storage issued).files.names current.current.ready.state.session.directory.path =
      some ((view.descriptors issued).inode (view.handle issued handle).2.1.description))
    (failedSync : raw.fsync handle issued = .error cause failed)
    (syncEffect : raw.readDirectory cache.directory afterFileSync = .ok (some handle) issued →
      raw.fsync handle issued = .error cause failed →
      (view.handle issued handle).2.1 ∈ (view.descriptors issued).slots →
      (storage issued).files.names current.current.ready.state.session.directory.path =
        some ((view.descriptors issued).inode (view.handle issued handle).2.1.description) →
      WalRootSyncEffect current.current.ready.state.session.directory effective (storage issued) (storage failed))
    (nonempty : current.current.ready.state.writer.installed.activeFirst <
      current.current.ready.state.writer.installed.walBytes / WAL.frameSize)
    (successor : RotationSuccessorAtSync current.current.ready.state.session.directory
      current.current.ready.state.writer.rotationInstalled.activeFirst inode (storage issued))
    (initial : NativeReadyStorage current.current.ready.state (storage current.reached))
    (files : (storage current.reached).Frames current.current.ready.state.crashPath (storage failed))
    (window : ∀ start, first ≤ start → start ≤ through →
      start ≠ current.current.ready.state.writer.rotationInstalled.activeFirst →
      current.current.ready.state.writer.wal.SettledNamespaceWindow current.current.ready.state.session.directory
        start start (storage current.reached))
    (namesFrame : RotationWalNameFrame current.current.ready.state.session.directory first through
      current.current.ready.state.writer.rotationInstalled.activeFirst (storage current.reached) (storage failed))
    (chosen : (storage rebooted).files.names ∈ (storage failed).crashNames) :
    let state := current.current.ready.state
    let directory := state.session.directory
    let names := (storage rebooted).files.names
    let path := directory.file (.walSegment state.writer.rotationInstalled.activeFirst)
    let selected := state.rotationWriterAtSample current.current.ready.readPrefix.refines.1 names
    NativeReadyStorage state (storage failed) ∧ selected.RetainedReady directory state.session.descriptor ∧
    selected.history = state.writer.history ∧ selected.target.pair = state.writer.target.pair ∧
    selected.wal.NamespaceWindow directory first through names ∧
    (names path = none ∨ names path = some inode ∧ (storage failed).files.bytes inode = [ByteArray.empty]) ∧
    (effective = true → names path = some inode) := by
  intro state directory names path selected
  let valid := current.current.ready.readPrefix.refines.1
  have effect := syncEffect loaded failedSync target.live root
  obtain ⟨survives, settled⟩ := effect.selectsRotationSuccessor successor chosen
  exact ⟨initial.frame files, state.rotationWriterAtSample_retained valid nonempty names,
    state.rotationWriterAtSample_history valid names, state.rotationWriterAtSample_pair valid names,
    state.rotationWriterAtSample_namespace valid nonempty window namesFrame chosen, survives, settled⟩

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
theorem RawWriteRebootEntry.replaysRotationSample
    (seen : RawWriteRebootEntry picked view storage names visible failed rebooted)
    (old : NativeReadyStorage state (storage failed))
    (ready : (picked).writer.RetainedReady directory state.session.descriptor)
    {inode : Nat}
    (choice : names rebooted ((directory).file (.walSegment successor)) = none ∨
      names rebooted ((directory).file (.walSegment successor)) = some inode ∧ (storage failed).files.bytes inode = [ByteArray.empty])
    (window : (picked).writer.wal.NamespaceWindow directory 0 (picked).writer.target.range.through (names rebooted))
    (noManifest : state.writer.target.pair.manifest = none) :
    source.ReplaysWalBeforeCheckpointAtOpen view directory (picked).writer.wal.active.first
      storage visible rebooted namespaceView root state.writer.history := by
  have history := state.rotationWriterAtSample_history valid (names rebooted)
  have pairEq := state.rotationWriterAtSample_pair valid (names rebooted)
  have oldName (path : FilePath) (inside : state.crashPath path) :
      names rebooted path = (storage failed).files.names path :=
    old.settled _ seen.chosen path inside
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
  obtain ⟨protectedFiles, manifest⟩ := frame.1.samplesRebootFiles (names rebooted) (visible rebooted)
    (fun path inside => oldName path (frame.2 path inside)) seen.sampled
  let markerPath := (directory).file .walBoundary
  have marker : state.writer.target.pair.walBoundary = some (WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64) :=
    (congrArg DirectoryPublication.Bindings.walBoundary valid.retained.resumed.ready.selected).symm.trans
      (congrArg Publication.Image.active valid.retained.resumed.markerImage)
  obtain ⟨markerInode, markerNamed, markerBytes⟩ :=
    old.marker.samplesAtBinding (names rebooted) (visible rebooted)
      (oldName markerPath (NativeReadyState.crashPath_iff_write.mpr (.inl rfl)))
      (fun inode => seen.samplesWal markerPath inode (.inr (.inl rfl)))
  have marked : (names rebooted markerPath).map (visible rebooted) = (picked).writer.target.pair.walBoundary := by
    rw [markerNamed, Option.map_some, markerBytes, pairEq, marker]
  have pair : (picked).writer.target.pair =
      ⟨(names rebooted ((directory).file .manifest)).map (visible rebooted), (names rebooted markerPath).map (visible rebooted)⟩ := by
    rw [manifest, marked]
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
        (fun inode bound => seen.samplesWal keeperPath inode (.inr (.inr rfl)) (path.symm ▸ bound))
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
      have bytes := seen.samplesWal keeperPath inode (.inr (.inr rfl)) atKeeper
      rw [durable] at bytes
      rw [atKeeper, Option.map_some, List.mem_singleton.mp bytes, rotated]
      rfl
  have accepts : (picked).writer.target.Accepts ((names rebooted keeperPath).map (visible rebooted)) :=
    payload.symm ▸ (picked).writer.target.acceptsTrimmed
  obtain ⟨selected, _, _⟩ := seen.selectsSampledRetry ready.active rfl protectedFiles pair accepts
  obtain ⟨layout, target, sameKeeper, _, descriptors, offsets, _⟩ := selected.readyRebootLayout ready payload
  have through : layout.range.through = (picked).writer.target.range.through :=
    congrArg (fun target : Target => target.range.through) target
  have wal := selected.visibleReadyWal layout target descriptors offsets (window.restrict (Nat.zero_le _) (Nat.le_of_eq through))
  have absent : (picked).writer.target.pair.manifest = none := (congrArg DirectoryPublication.Bindings.manifest pairEq).trans noManifest
  have sameFirst := congrArg WalSegment.first sameKeeper
  rw [← sameFirst, ← history]
  exact @RawOpenRetryTrace.SelectedEntry.replaysWalBeforeCheckpointAtOpen
    (source := source) (namespaceView := namespaceView) (root := root) (selected := selected) (layout := layout)
    (noManifest := absent) (following := (layout.modeledWindow _ offsets).2)
    (ordered := ready.resumed.ordered) (wal := wal)

end SampledReader

end Alvoki.Storage.DiskSession
