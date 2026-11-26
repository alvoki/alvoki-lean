import Alvoki.Storage.Disk.NativeWalPublicationTail
import Alvoki.Storage.Disk.NativeCheckpointSourceCrash

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentCommit
open WAL.Boundary (WalInodeImage)

/-- Local observations used at the distinct append, stage, and file-sync
heaps. The keeper and canonical-marker frames are independent of the
staged marker's bytes and of the later rename outcome. -/
structure RawSyncCalls.WalGroupEffects {heap image : Type} (calls : RawSyncCalls heap)
    {directory : DiskDirectory} {files : DiskTable.OpenSyncFiles}
    (cache : OpenSyncCacheRefs files directory.path) (view : OpenCloseHeapView heap image)
    (appender : RawWalAppendCalls heap) (stager : RawWalStageCalls heap)
    (inodes : heap → WalInodeImage) {runs : heap → RunUnlinkImage}
    (observe : ∀ heap, RunDirectoryInodeView directory (inodes heap) (runs heap))
    (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray)
    (first count : Nat) (priorBytes bytes : ByteArray) (entry appended staged grouped : heap) : Prop where
  keeperLive : ∀ keeper, (observe entry).visible (directory.file (.walSegment first)) = some keeper →
    (inodes entry).visible keeper = priorBytes
  stagedNames : ∀ names ∈ (observe staged).crashBindings, names (directory.file (.walSegment first)) =
    (observe entry).visible (directory.file (.walSegment first))
  markerFrame : (observe entry).storageObservation.Frames (· = directory.file .walBoundary)
    (observe grouped).storageObservation
  appendFile : ∀ keeper, (observe entry).visible (directory.file (.walSegment first)) = some keeper →
    appender.KeeperEffects view cache.active (directory.file (.walSegment first)) bytes entry appended
      (fun heap => (observe heap).visible) (fun heap => (inodes heap).visible) inode buffered keeper
  stageFile : ∀ keeper, (observe appended).visible (directory.file (.walSegment first)) = some keeper →
    stager.MarkerEffects cache view (WAL.Boundary.encode count.toUInt64) appended staged
      (fun heap => (observe heap).visible) (fun heap => (inodes heap).visible) inode buffered keeper
  fileBarriers : ∀ {keeper keeperHandle markerHandle},
    (observe appended).visible (directory.file (.walSegment first)) = some keeper →
    inode keeperHandle = keeper →
    view.active appended cache.active = some (directory.file (.walSegment first), keeperHandle) →
    view.literalCacheAt staged cache.directory cache.active cache.pending =
      (view.literalCacheAt appended cache.directory cache.active cache.pending).remember
        (directory.file .stagedWalBoundary) markerHandle →
    ∃ consumed, calls.GroupedFileEffects cache view inodes observe first appended staged consumed grouped
      keeperHandle markerHandle keeper (inode markerHandle)

/-- Exact file payloads and namespace choices at a reached late write
error. The live marker and the admitted crash choices remain independent. -/
def WalPublicationPayloads.ReachedWrite (state : NativeReadyState) (batch : List WAL.Write)
    (rows : List (UInt64 × Option UInt64)) (atHeap : CheckpointStorageObservation)
    (liveNew : Bool) (allows : Bool → Prop) : Prop :=
  ∃ payloads : WalPublicationPayloads,
    payloads.keeperBytes = state.writer.wal.active.bytes ++ WAL.encodeBatch batch ∧
    payloads.oldMarkerBytes = WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64 ∧
    payloads.newMarkerBytes = WAL.Boundary.encode (state.writer.installed.walBytes + WAL.frameSize * rows.length).toUInt64 ∧
    payloads.Selections state.session.directory state.writer.wal.active.first atHeap liveNew allows

/-- A failed final barrier always reaches the cache read. A successful
lookup of a handle can additionally issue an fsync against the named
database root. Only that syscall has a directory settlement effect. -/
structure RawSyncCalls.FinalRootEffects {heap image : Type} (calls : RawSyncCalls heap)
    {directory : DiskDirectory} {files : DiskTable.OpenSyncFiles}
    (cache : OpenSyncCacheRefs files directory.path) (view : OpenCloseHeapView heap image)
    (storage : heap → CheckpointStorageObservation) (first : Nat)
    (renamed reached : heap) (effective : Bool) : Prop where
  cacheRead : WalPublicationPayloads.CacheReadFrame directory first (storage renamed)
    (storage (reachedState (calls.readDirectory cache.directory renamed)))
  target : ∀ {handle issued syncCause},
    calls.readDirectory cache.directory renamed = .ok (some handle) issued →
    calls.fsync handle issued = .error syncCause reached →
    RawFsyncTarget view renamed issued handle ∧
      (storage renamed).files.names directory.path =
        some ((view.handle renamed handle).1.inode (view.handle renamed handle).2.1.description) ∧
      (storage issued).files.names directory.path = (storage renamed).files.names directory.path
  sync : ∀ {handle issued syncCause},
    calls.readDirectory cache.directory renamed = .ok (some handle) issued →
    calls.fsync handle issued = .error syncCause reached →
    (view.handle issued handle).2.1 ∈ (view.descriptors issued).slots →
    (storage issued).files.names directory.path =
      some ((view.descriptors issued).inode (view.handle issued handle).2.1.description) →
    WalRootSyncEffect directory effective (storage issued) (storage reached)

section

variable {heap image : Type} {state : NativeReadyState}
  (calls : RawSyncCalls heap) {files : DiskTable.OpenSyncFiles}
  (cache : OpenSyncCacheRefs files state.session.directory.path) (view : OpenCloseHeapView heap image)
  (appender : RawWalAppendCalls heap) (stager : RawWalStageCalls heap)
  (inodes : heap → WalInodeImage) {runs : heap → RunUnlinkImage}
  (observe : ∀ heap, RunDirectoryInodeView state.session.directory (inodes heap) (runs heap))
  (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray)
  {entry appended staged grouped : heap} {rows : List (UInt64 × Option UInt64)} {batch : List WAL.Write}

local notation "dir" => state.session.directory
local notation "first" => state.writer.installed.activeFirst
local notation "keeperPath" => state.session.directory.file (DiskFile.walSegment state.writer.installed.activeFirst)
local notation "markerPath" => state.session.directory.file DiskFile.walBoundary
local notation "stagedPath" => state.session.directory.file DiskFile.stagedWalBoundary
local notation "priorBytes" => state.writer.wal.active.bytes
local notation "bytes" => WAL.encodeBatch batch
local notation "count" => state.writer.installed.walBytes + WAL.frameSize * rows.length
local notation "mark" => WAL.Boundary.encode (Nat.toUInt64 (state.writer.installed.walBytes + WAL.frameSize * rows.length))
local notation "append" => appender.run cache.active
local notation "stage" => stager.run cache.pending
local notation "sync" => calls.group state.session.directory.path cache.directory cache.active cache.pending

/-- The successful file group derives the stored keeper and staged
marker at its return heap. The existing ready marker is carried by
its independent frame into that same heap. -/
theorem RawSyncCalls.groupedWalPayloadsFromPublication (valid : state.Valid)
    (old : NativeReadyStorage state (observe entry).storageObservation)
    (wrote : append keeperPath bytes entry = .ok () appended)
    (remembered : stage stagedPath mark appended = .ok () staged)
    (synced : sync #[keeperPath, stagedPath] staged = .ok () grouped)
    (effects : calls.WalGroupEffects cache view appender stager inodes observe inode buffered
      first count priorBytes bytes entry appended staged grouped) :
    ∃ payloads : WalPublicationPayloads,
      payloads.Grouped dir first (observe grouped).storageObservation ∧
      payloads.keeperBytes = priorBytes ++ bytes ∧
      payloads.oldMarkerBytes = WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64 ∧
      payloads.newMarkerBytes = mark := by
  have firstExact : first = state.writer.wal.active.first := valid.retained.resumed.keeper.trans valid.retained.active
  obtain ⟨keeper, named, _⟩ := old.keeper
  change (observe entry).visible ((dir).file (.walSegment state.writer.wal.active.first)) = some keeper at named
  have priorBinding : (observe entry).visible keeperPath = some keeper := by
    simpa only [firstExact] using named
  obtain ⟨keeperStored, stageStored, keeperName, _, reachedNames⟩ :=
    calls.groupedStorageFromPublication cache view appender stager inodes observe inode buffered
      priorBinding (effects.keeperLive keeper priorBinding) wrote remembered synced
      (effects.appendFile keeper priorBinding) (effects.stageFile keeper) effects.fileBarriers
  obtain ⟨storedKeeper, keeperBound, keeperBytes⟩ := keeperStored
  obtain ⟨stageInode, stagedBound, stagedBytes⟩ := stageStored
  obtain ⟨oldMarker, oldNamed, oldBytes⟩ := effects.markerFrame.visible.stored rfl old.marker
  have oldSettled := effects.markerFrame.settledFrom (fun names possible path same =>
    old.settled names possible path (NativeReadyState.crashPath_iff_write.mpr (.inl same)))
  have sameKeeper := Option.some.inj (keeperBound.symm.trans keeperName)
  subst storedKeeper
  let payloads : WalPublicationPayloads := ⟨keeper, oldMarker, stageInode, priorBytes ++ bytes,
    WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64, mark⟩
  refine ⟨payloads, ⟨keeperBound, oldNamed, stagedBound, keeperBytes, oldBytes, stagedBytes, ?_⟩, rfl, rfl, rfl⟩
  intro names possible
  obtain ⟨prior, earlier, same⟩ := reachedNames names possible
  exact ⟨same.trans ((effects.stagedNames prior earlier).trans priorBinding), (oldSettled names possible _ rfl).trans oldNamed⟩

/-- A returned rename error follows the successful file group at the
same heap. The rename effect acts on the inode actually named by the
staged path there, and there is no later directory sync in this return. -/
theorem RawSyncCalls.failedMarkerRenameSelects (valid : state.Valid)
    (old : NativeReadyStorage state (observe entry).storageObservation)
    (wrote : append keeperPath bytes entry = .ok () appended)
    (remembered : stage stagedPath mark appended = .ok () staged)
    (synced : sync #[keeperPath, stagedPath] staged = .ok () grouped)
    (effects : calls.WalGroupEffects cache view appender stager inodes observe inode buffered
      first count priorBytes bytes entry appended staged grouped)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit) {reached : heap} {cause : IO.Error} {effective : Bool}
    (failed : rename stagedPath markerPath grouped = .error cause reached)
    (effect : ∀ inode, (observe grouped).visible stagedPath = some inode →
      WalMarkerRenameEffect dir inode effective (observe grouped).storageObservation (observe reached).storageObservation) :
    commitBytesAt dir first bytes count append stage sync rename entry = .error cause reached ∧
    WalPublicationPayloads.ReachedWrite state batch rows (observe reached).storageObservation effective
      (fun published => published = true → effective = true) := by
  obtain ⟨payloads, selected, keeper, oldMarker, newMarker⟩ :=
    calls.groupedWalPayloadsFromPublication cache view appender stager inodes observe inode buffered
      (rows := rows) valid old wrote remembered synced effects
  have selectedReturn := (effect payloads.newMarker selected.stagedNamed).selects selected
  have firstExact : first = state.writer.wal.active.first := valid.retained.resumed.keeper.trans valid.retained.active
  rw [firstExact] at selectedReturn
  refine ⟨?_, payloads, keeper, oldMarker, newMarker, selectedReturn⟩
  simp only [calls.commitAfterStaging cache appender stager rename wrote remembered, synced, failed]

/-- Follow the actual successful file group and rename to the final
barrier error. A cache failure or missing handle carries the rename's
survivors to the returned heap. An issued fsync may settle the new
marker even when it reports an error. -/
theorem RawSyncCalls.failedRootSyncFromPublication (valid : state.Valid)
    (old : NativeReadyStorage state (observe entry).storageObservation)
    (wrote : append keeperPath bytes entry = .ok () appended)
    (remembered : stage stagedPath mark appended = .ok () staged)
    (synced : sync #[keeperPath, stagedPath] staged = .ok () grouped)
    (effects : calls.WalGroupEffects cache view appender stager inodes observe inode buffered
      first count priorBytes bytes entry appended staged grouped)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {renamed reached : heap} {cause : IO.Error} {effective : Bool}
    (moved : rename stagedPath markerPath grouped = .ok () renamed)
    (failedGroup : sync #[(dir).path] renamed = .error cause reached)
    (renameEffect : ∀ ino, (observe grouped).visible stagedPath = some ino →
      WalMarkerRenameEffect dir ino true (observe grouped).storageObservation (observe renamed).storageObservation)
    (rootEffects : calls.FinalRootEffects cache view (fun atHeap => (observe atHeap).storageObservation)
      first renamed reached effective) :
    let settled := match calls.readDirectory cache.directory renamed with
      | .ok (some _) _ => effective
      | _ => false
    commitBytesAt dir first bytes count append stage sync rename entry = .error cause reached ∧
    WalPublicationPayloads.ReachedWrite state batch rows (observe reached).storageObservation true
      (fun published => settled = true → published = true) := by
  intro settled
  obtain ⟨payloads, selected, keeper, oldMarker, newMarker⟩ :=
    calls.groupedWalPayloadsFromPublication cache view appender stager inodes observe inode buffered
      (rows := rows) valid old wrote remembered synced effects
  have atRename := (renameEffect payloads.newMarker selected.stagedNamed).selects selected
  have afterCache := atRename.frameCacheRead rootEffects.cacheRead
  have raw := (calls.rootBarrierResult cache renamed).symm.trans failedGroup
  have selections : payloads.Selections dir first (observe reached).storageObservation true
      (fun published => settled = true → published = true) := by
    cases load : calls.readDirectory cache.directory renamed with
    | error diagnostic after =>
      simp only [load] at raw
      have same := (EStateM.Result.error.inj raw).2
      subst after
      have kept := (congrArg reachedState load) ▸ afterCache
      simpa [settled, load, reachedState] using kept
    | ok cached issued =>
      cases cached with
      | none =>
        simp only [load] at raw
        have same := (EStateM.Result.error.inj raw).2
        subst issued
        have kept := (congrArg reachedState load) ▸ afterCache
        simpa [settled, load, reachedState] using kept
      | some handle =>
        simp only [load] at raw
        cases failed : calls.fsync handle issued with
        | ok value after =>
          cases value
          simp [failed] at raw
        | error diagnostic after =>
          simp only [failed] at raw
          have same := (EStateM.Result.error.inj raw).2
          subst after
          obtain ⟨target, rootAtRename, keptRoot⟩ := rootEffects.target load failed
          have issuedRoot := keptRoot.trans (rootAtRename.trans (congrArg some target.inode.symm))
          have atIssue := (congrArg reachedState load) ▸ afterCache
          obtain ⟨live, survivors⟩ := (rootEffects.sync load failed target.live issuedRoot).selects atIssue
          refine ⟨live, fun names allowed => ?_⟩
          obtain ⟨published, permit, observed⟩ := survivors names allowed
          refine ⟨published, fun applied => ?_, observed⟩
          have barrier : effective = true := by simpa only [settled, load] using applied
          simpa only [barrier, ite_true] using permit
  have firstExact : first = state.writer.wal.active.first := valid.retained.resumed.keeper.trans valid.retained.active
  rw [firstExact] at selections
  refine ⟨?_, payloads, keeper, oldMarker, newMarker, selections⟩
  simpa only [synced, moved, failedGroup] using calls.commitAfterStaging cache appender stager rename wrote remembered

end
end Alvoki.Storage.DiskSession
