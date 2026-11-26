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

/-- Compose the literal write prefix and failed file group with one
reboot observation. Recovery has its own chronological trace and file
effects, with the same interpreter for all attempts and the final table. -/
theorem NativeOpenedPosition.recoversGroupedWriteError
    (request : WriteRequest) (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {batch : List WAL.Write} {table : PackedTable}
    {guarded poisoned appended staged failed rebooted reached : heap} {cause : IO.Error}
    (nonempty : request.rows ≠ [])
    (prepared : prepareBatch (installed).table request.rows = some (batch, table))
    (fits : (installed).walBytes + WAL.frameSize * request.rows.length < UInt64.size)
    (guard : checkActiveSegmentWith dir installed lookup current.reached = .ok () guarded)
    (assigned : opened.set opened.phase .poisoned guarded = .ok () poisoned)
    (wrote : append ((dir).file (.walSegment (installed).activeFirst)) (WAL.encodeBatch batch) poisoned = .ok () appended)
    (stagedMarker : stage ((dir).file .stagedWalBoundary)
      (WAL.Boundary.encode ((installed).walBytes + WAL.frameSize * request.rows.length).toUInt64)
      appended = .ok () staged)
    (fileError : sync #[(dir).file (.walSegment (installed).activeFirst), (dir).file .stagedWalBoundary]
      staged = .error cause failed)
    (initial : NativeReadyStorage state (storage current.reached))
    (prefixFrame : (storage current.reached).Frames (state).writeFramePath (storage poisoned))
    (appendFrame : (storage poisoned).Frames (state).writeFramePath (storage appended))
    (stageFrame : (storage appended).Frames (state).writeFramePath (storage staged))
    (syncFrame : (storage staged).Frames (state).writeFramePath (storage failed))
    (groupEffects : syncer.GroupFailureEffects cache view appender stager inodes observe inode buffered
      request.rows batch current.reached poisoned appended staged)
    {names : heap → FilePath → Option Nat} {visible : heap → Nat → ByteArray}
    (reboot : RawWriteRebootEntry state view storage names visible failed rebooted)
    (later : ∀ ordinal ∈ (view.files rebooted).image.later.visible, (state).writer.target.range.through < ordinal)
    (source : RawMarkedOpenInterpreter heap stream) {input : FilePath} {returns : List (FilePath × IO.Error)}
    {attempts : source.FailedCalls rebooted returns reached}
    (retryEffects : RawOpenRetryTrace.SelectedEffects view source rebooted (state).writer.target
      (fun heap => ⟨names heap, fun inode => [visible heap inode]⟩) (state).selectedRetryPath
      (RawOpenRetryTrace.KeeperAt view dir (state).writer.target names visible) attempts)
    (vacant : TryLockObserves (view.files reached).owners dir (.ok true))
    {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
    (healthy : (ready).ObservesHealthyWriteRetry (input := input) (view := view) (batch := batch)
      (target := (state).writer.target) (reached := reached) (phaseIdentity := phaseIdentity) (tokenIdentity := tokenIdentity)
      source names vacant)
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (phase : OpenPhaseCellEffects view.phase get set)
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool) :
    opened.table.UsesOpenWriteSchedules dir opened.files opened.phase ∧
    request.runOnRawOpenPhase dir lookup append stage sync rename opened.phase opened.get opened.set current.reached =
      .error (.commitUnknown cause) failed ∧
    TryLockObserves (view.files rebooted).owners dir (.ok true) ∧
    (view.descriptors rebooted).slots = [] ∧
    (ready).SelectedWriteRecovery (returns := returns) (input := input) (view := view) (batch := batch)
      (target := (state).writer.target) (reached := reached) (phaseIdentity := phaseIdentity) (tokenIdentity := tokenIdentity)
      source names visible rebooted vacant get set ptrEq ∧
    (ready).ReopenedLedger current.current.history batch [] request input cause (source.openTable input reached) := by
  have valid := (ready).readPrefix.refines.1
  have loaded := opened.phaseEffects.reads current.reached opened.phase _ (current.stored.trans (congrArg some valid.phase))
  obtain ⟨committed, admitted, selected, rebootVacant, slots⟩ :=
    RawWriteRebootEntry.selectsGroupErrorRetry cache view appender stager syncer inodes observe inode buffered rename
      valid initial (prefixFrame.trans (appendFrame.trans (stageFrame.trans syncFrame)))
      prepared fits wrote stagedMarker fileError groupEffects reboot later
  refine ⟨current.uses.writeSchedules, ?_, rebootVacant, slots, ?_⟩
  · rw [request.runOnRawOpenPhase_afterPreparation dir lookup append stage sync rename opened.phase opened.get opened.set
      loaded nonempty prepared fits]
    simp only [guard, assigned, committed]
  · have recovered := (ready).opensAfterWriteRetries source prepared fits admitted names visible retryEffects selected vacant healthy phase ptrEq
    exact ⟨recovered, recovered.replaysOldTarget request cause⟩

end

end Alvoki.Storage.DiskSession
