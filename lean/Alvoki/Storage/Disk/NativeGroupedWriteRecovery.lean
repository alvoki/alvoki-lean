import Alvoki.Storage.Disk.NativeGroupedWriteReboot
import Alvoki.Storage.Disk.NativeSourceLedger

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentCommit WalSegmentRepair
open WAL.Boundary (WalInodeImage)

section

variable {heap stream : Type} {opened : NativeOpenedHandle heap}
  (current : NativeOpenedPosition opened) (view : OpenCloseHeapView heap FileImage)
  (cache : OpenSyncCacheRefs opened.files current.current.ready.state.session.directory.path)
  (appender : RawWalAppendCalls heap) (stager : RawWalStageCalls heap) (syncer : RawSyncCalls heap)
  (inodes : heap → WalInodeImage) {runs : heap → RunUnlinkImage}
  (observe : ∀ heap, RunDirectoryInodeView current.current.ready.state.session.directory (inodes heap) (runs heap))
  (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray)

local notation "ready" => current.current.ready
local notation "state" => current.current.ready.state
local notation "dir" => current.current.ready.state.session.directory
local notation "installed" => current.current.ready.state.writer.installed
local notation "storage" => fun heap => RunDirectoryInodeView.storageObservation (observe heap)
local notation "append" => appender.run cache.active
local notation "stage" => stager.run cache.pending
local notation "sync" => syncer.group current.current.ready.state.session.directory.path cache.directory cache.active cache.pending

local notation "keeperPath" => DiskDirectory.file dir
  (DiskFile.walSegment (Installed.activeFirst installed))
local notation "stagedPath" => DiskDirectory.file dir DiskFile.stagedWalBoundary
local notation "appendBatch" => fun batch => append keeperPath (WAL.encodeBatch batch)
local notation "writeMarker" => fun rows => stage stagedPath
  (WAL.Boundary.encode (Nat.toUInt64 (Installed.walBytes installed + WAL.frameSize * List.length rows)))
local notation "syncFiles" => sync #[keeperPath, stagedPath]

/-- Local effect law for the exact source receipts on the group-error
branch. The preparation and reported call results are executable values. -/
def NativeOpenedPosition.GroupedErrorEffects
    (request : WriteRequest) (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (failed : heap) (cause : IO.Error) : Prop :=
  ∀ {batch table guarded poisoned appended staged},
      prepareBatch (installed).table request.rows = some (batch, table) →
      checkActiveSegmentWith dir installed lookup current.reached = .ok () guarded →
      opened.set opened.phase .poisoned guarded = .ok () poisoned →
      appendBatch batch poisoned = .ok () appended → writeMarker request.rows appended = .ok () staged →
      syncFiles staged = .error cause failed →
      (storage current.reached).Frames (state).writeFramePath (storage poisoned) ∧
      (storage poisoned).Frames (state).writeFramePath (storage appended) ∧
      (storage appended).Frames (state).writeFramePath (storage staged) ∧
      (storage staged).Frames (state).writeFramePath (storage failed) ∧
      syncer.GroupFailureEffects cache view appender stager inodes observe inode buffered
        request.rows batch current.reached poisoned appended staged

/-- Classify the literal uncertain return and sample its group-error
reboot. The group leaves the old target selected. The next open is
independent of this selection. -/
theorem NativeOpenedPosition.selectsAfterGroupedError
    (request : WriteRequest) (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {failed rebooted : heap} {cause : IO.Error}
    (nonempty : request.rows ≠ [])
    (returned : request.runOnRawOpenPhase dir lookup append stage sync rename opened.phase opened.get opened.set current.reached =
      .error (.commitUnknown cause) failed)
    (initial : NativeReadyStorage state (storage current.reached))
    (groupEffects : current.GroupedErrorEffects view cache appender stager syncer inodes observe inode buffered
      request lookup failed cause)
    {names : heap → FilePath → Option Nat} {visible : heap → Nat → ByteArray}
    (reboot : RawWriteRebootEntry state view storage names visible failed rebooted)
    (later : ∀ ordinal ∈ (view.files rebooted).image.later.visible, (state).writer.target.range.through < ordinal)
 :
    opened.table.UsesOpenWriteSchedules dir opened.files opened.phase ∧
    ∃ batch table guarded poisoned,
      prepareBatch (installed).table request.rows = some (batch, table) ∧
      (installed).walBytes + WAL.frameSize * request.rows.length < UInt64.size ∧
      checkActiveSegmentWith dir installed lookup current.reached = .ok () guarded ∧
      opened.set opened.phase .poisoned guarded = .ok () poisoned ∧
      let groupFailed := ∃ appended staged, appendBatch batch poisoned = .ok () appended ∧
        writeMarker request.rows appended = .ok () staged ∧ syncFiles staged = .error cause failed
      (groupFailed ∧
        BatchRetryTarget (state).writer.history batch (state).writer.wal.active.first (state).writer.target ∧
        RawOpenRetryTrace.SelectedEntry view state (state).writer.target names visible rebooted ∧
        TryLockObserves (view.files rebooted).owners dir (.ok true) ∧
        (view.descriptors rebooted).slots = []) ∨
      ¬ groupFailed := by
  obtain ⟨batch, table, guarded, poisoned, prepared, fits, guard, assigned, _, outcome⟩ :=
    current.classifiesCommitUnknown appender stager syncer cache request lookup rename nonempty returned
  refine ⟨current.uses.writeSchedules, batch, table, guarded, poisoned, prepared, fits, guard, assigned, ?_⟩
  have passedGroup {appended staged grouped} (wrote : appendBatch batch poisoned = .ok () appended)
      (remembered : writeMarker request.rows appended = .ok () staged)
      (synced : syncFiles staged = .ok () grouped) :
      ¬ ∃ a s, appendBatch batch poisoned = .ok () a ∧
        writeMarker request.rows a = .ok () s ∧ syncFiles s = .error cause failed := by
    rintro ⟨_, _, w, m, f⟩
    obtain rfl := (EStateM.Result.ok.inj (wrote.symm.trans w)).2
    obtain rfl := (EStateM.Result.ok.inj (remembered.symm.trans m)).2
    rw [synced] at f
    contradiction
  cases outcome with
  | appendError failedAppend =>
    right
    rintro ⟨_, _, wrote, _, _⟩
    have impossible := failedAppend.symm.trans wrote
    contradiction
  | stageError wrote failedStage =>
    right
    rintro ⟨_, _, w, remembered, _⟩
    obtain rfl := (EStateM.Result.ok.inj (wrote.symm.trans w)).2
    have impossible := failedStage.symm.trans remembered
    contradiction
  | groupError wrote remembered failedGroup =>
    have valid := (ready).readPrefix.refines.1
    obtain ⟨prefixFrame, appendFrame, stageFrame, syncFrame, effects⟩ :=
      groupEffects prepared guard assigned wrote remembered failedGroup
    have protectedFrame := prefixFrame.trans (appendFrame.trans (stageFrame.trans syncFrame))
    obtain ⟨_, admitted, selected, rebootVacant, slots⟩ :=
      RawWriteRebootEntry.selectsGroupErrorRetry cache view appender stager syncer inodes observe inode buffered rename
        valid initial protectedFrame wrote remembered failedGroup effects reboot later
    exact .inl ⟨⟨_, _, wrote, remembered, failedGroup⟩, admitted, selected, rebootVacant, slots⟩
  | renameError wrote remembered synced _ => exact .inr (passedGroup wrote remembered synced)
  | directory wrote remembered synced _ _ => exact .inr (passedGroup wrote remembered synced)

/-- Feed the sampled group-error target to the existing reported retry
reader. The group classification and reboot selection also serve the
literal opener independently of this reported path. -/
theorem NativeOpenedPosition.recoversGroupedWriteError
    (request : WriteRequest) (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {failed rebooted reached : heap} {cause : IO.Error}
    (nonempty : request.rows ≠ [])
    (returned : request.runOnRawOpenPhase dir lookup append stage sync rename opened.phase opened.get opened.set current.reached =
      .error (.commitUnknown cause) failed)
    (initial : NativeReadyStorage state (storage current.reached))
    (groupEffects : current.GroupedErrorEffects view cache appender stager syncer inodes observe inode buffered
      request lookup failed cause)
    {names : heap → FilePath → Option Nat} {visible : heap → Nat → ByteArray}
    (reboot : RawWriteRebootEntry state view storage names visible failed rebooted)
    (later : ∀ ordinal ∈ (view.files rebooted).image.later.visible, (state).writer.target.range.through < ordinal)
    (source : RawMarkedOpenInterpreter heap stream) {input : FilePath} {returns : List (FilePath × IO.Error)}
    {keep : heap → Prop} {attempts : source.FailedCalls rebooted returns reached}
    (retryEffects : RawOpenRetryTrace.SelectedEffects view source rebooted (state).writer.target
      (fun heap => ⟨names heap, fun inode => [visible heap inode]⟩) (state).selectedRetryPath
      keep attempts)
    (starts : RawOpenRetryTrace.SelectedEntry view state (state).writer.target names visible rebooted → keep rebooted)
    (liveKeeper : keep reached → RawOpenRetryTrace.KeeperAt view dir (state).writer.target names visible reached)
    (vacant : TryLockObserves (view.files reached).owners dir (.ok true))
    {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
    (healthy : ∀ {batch table}, prepareBatch (installed).table request.rows = some (batch, table) →
      (ready).ObservesHealthyWriteRetry (input := input) (view := view) (batch := batch)
        (target := (state).writer.target) (reached := reached) (phaseIdentity := phaseIdentity) (tokenIdentity := tokenIdentity)
        source names vacant)
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (phase : OpenPhaseCellEffects view.phase get set)
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool) :
    opened.table.UsesOpenWriteSchedules dir opened.files opened.phase ∧
    ∃ batch table guarded poisoned,
      prepareBatch (installed).table request.rows = some (batch, table) ∧
      (installed).walBytes + WAL.frameSize * request.rows.length < UInt64.size ∧
      checkActiveSegmentWith dir installed lookup current.reached = .ok () guarded ∧
      opened.set opened.phase .poisoned guarded = .ok () poisoned ∧
      let groupFailed := ∃ appended staged, appendBatch batch poisoned = .ok () appended ∧
        writeMarker request.rows appended = .ok () staged ∧ syncFiles staged = .error cause failed
      (groupFailed ∧
        TryLockObserves (view.files rebooted).owners dir (.ok true) ∧
        (view.descriptors rebooted).slots = [] ∧
        keep reached ∧
        (ready).SelectedWriteRecovery (returns := returns) (input := input) (view := view) (batch := batch)
          (target := (state).writer.target) (reached := reached) (phaseIdentity := phaseIdentity) (tokenIdentity := tokenIdentity)
          source names visible rebooted vacant get set ptrEq ∧
        (ready).ReopenedLedger current.current.history batch [] request input cause (source.openTable input reached)) ∨
      ¬ groupFailed := by
  obtain ⟨schedules, batch, table, guarded, poisoned, prepared, fits, guard, assigned, classified⟩ :=
    current.selectsAfterGroupedError view cache appender stager syncer inodes observe inode buffered
      request lookup rename nonempty returned initial groupEffects reboot later
  refine ⟨schedules, batch, table, guarded, poisoned, prepared, fits, guard, assigned, ?_⟩
  rcases classified with ⟨group, admitted, selected, rebootVacant, slots⟩ | elsewhere
  · obtain ⟨carried, recovered⟩ :=
      (ready).opensAfterWriteRetries source prepared fits admitted names visible retryEffects selected
        (starts selected) liveKeeper vacant (healthy prepared) phase ptrEq
    exact .inl ⟨group, rebootVacant, slots, carried, recovered, recovered.replaysOldTarget request cause⟩
  · exact .inr elsewhere

end

end Alvoki.Storage.DiskSession
