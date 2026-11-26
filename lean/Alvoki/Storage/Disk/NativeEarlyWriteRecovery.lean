import Alvoki.Storage.Disk.NativeGroupedWalRetryTarget
import Alvoki.Storage.Disk.NativeSourceLedger

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentCommit WalSegmentRepair
open WAL.Boundary (WalInodeImage)

/-- Neither early error enters the file-fsync group. Compose the frame of
only the callbacks reached by the literal append and staging returns. -/
theorem RawSyncCalls.earlyErrorKeeps {heap : Type} (calls : RawSyncCalls heap)
    {directory : DiskDirectory} {files : DiskTable.OpenSyncFiles}
    (cache : OpenSyncCacheRefs files directory.path) (appender : RawWalAppendCalls heap) (stager : RawWalStageCalls heap)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (frame : heap → heap → Prop) (compose : ∀ {a b c}, frame a b → frame b c → frame a c)
    {first count : Nat} {bytes : ByteArray} {entry failed : heap} {cause : IO.Error} :
    let append := appender.run cache.active (directory.file (.walSegment first)) bytes
    let stage := stager.run cache.pending (directory.file .stagedWalBoundary) (WAL.Boundary.encode count.toUInt64)
    (append entry = .error cause failed ∨
      ∃ appended, append entry = .ok () appended ∧ stage appended = .error cause failed) →
    frame entry (reachedState (append entry)) →
    (∀ {appended}, append entry = .ok () appended → stage appended = .error cause failed → frame appended failed) →
    commitBytesAt directory first bytes count (appender.run cache.active) (stager.run cache.pending)
      (calls.group directory.path cache.directory cache.active cache.pending) rename entry = .error cause failed ∧
    frame entry failed := by
  intro append stage early appendFrame stageFrame
  rcases early with rejected | ⟨appended, wrote, rejected⟩
  · dsimp only [append] at rejected
    refine ⟨?_, ?_⟩
    · simp only [commitBytesAt_fileEffects, WAL.Boundary.commit, Bind.bind, EStateM.bind, rejected]
    · simpa only [append, rejected, reachedState] using appendFrame
  · dsimp only [append] at wrote
    dsimp only [stage] at rejected
    refine ⟨?_, compose ?_ (stageFrame wrote rejected)⟩
    · simp only [commitBytesAt_fileEffects, WAL.Boundary.commit, Bind.bind, EStateM.bind, wrote, rejected]
    · simpa only [append, wrote, reachedState] using appendFrame

/-- Until the marker is replaced, an append may extend the keeper but
must preserve the independent marker and protected-file observations. -/
def NativeReadyState.BeforeMarkerWriteFrame (state : NativeReadyState) (keeper : Nat)
    (entry reached : CheckpointStorageObservation) : Prop :=
  entry.Frames state.selectedRetryPath reached ∧
  WalKeeperPrefixFrame (state.session.directory.file (.walSegment state.writer.wal.active.first)) keeper entry reached


theorem NativeReadyState.BeforeMarkerWriteFrame.refl (state : NativeReadyState) (keeper : Nat)
    (storage : CheckpointStorageObservation) : state.BeforeMarkerWriteFrame keeper storage storage :=
  ⟨.refl _ _, .refl _ _ _⟩

theorem NativeReadyState.BeforeMarkerWriteFrame.trans {state : NativeReadyState} {keeper : Nat}
    {entry middle reached : CheckpointStorageObservation}
    (first : state.BeforeMarkerWriteFrame keeper entry middle)
    (last : state.BeforeMarkerWriteFrame keeper middle reached) : state.BeforeMarkerWriteFrame keeper entry reached :=
  ⟨first.1.trans last.1, first.2.trans last.2⟩

section

variable {heap stream : Type} {opened : NativeOpenedHandle heap}
  (current : NativeOpenedPosition opened) (view : OpenCloseHeapView heap FileImage)
  (cache : OpenSyncCacheRefs opened.files current.current.ready.state.session.directory.path)
  (appender : RawWalAppendCalls heap) (stager : RawWalStageCalls heap) (syncer : RawSyncCalls heap)
  (inodes : heap → WalInodeImage) {runs : heap → RunUnlinkImage}
  (observe : ∀ heap, RunDirectoryInodeView current.current.ready.state.session.directory (inodes heap) (runs heap))

local notation "ready" => current.current.ready
local notation "state" => current.current.ready.state
local notation "dir" => current.current.ready.state.session.directory
local notation "installed" => current.current.ready.state.writer.installed
local notation "storage" => fun heap => RunDirectoryInodeView.storageObservation (observe heap)
local notation "append" => appender.run cache.active
local notation "stage" => stager.run cache.pending
local notation "sync" => syncer.group current.current.ready.state.session.directory.path cache.directory cache.active cache.pending

/-- A returned append or staging error keeps the old cutoff. The same
sampled reboot and fixed marked interpreter recover the returned table
for either error, including any admitted sequence of failed attempts. -/
theorem NativeOpenedPosition.recoversEarlyWriteError
    (request : WriteRequest) (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {batch : List WAL.Write} {table : PackedTable}
    {guarded poisoned failed rebooted reached : heap} {cause : IO.Error}
    (nonempty : request.rows ≠ [])
    (prepared : prepareBatch (installed).table request.rows = some (batch, table))
    (fits : (installed).walBytes + WAL.frameSize * request.rows.length < UInt64.size)
    (guard : checkActiveSegmentWith dir installed lookup current.reached = .ok () guarded)
    (assigned : opened.set opened.phase .poisoned guarded = .ok () poisoned)
    (initial : NativeReadyStorage state (storage current.reached))
    (prefixFrame : (storage current.reached).Frames (state).crashPath (storage poisoned))
    (early : let runAppend := append ((dir).file (.walSegment (installed).activeFirst)) (WAL.encodeBatch batch)
      runAppend poisoned = .error cause failed ∨ ∃ appended, runAppend poisoned = .ok () appended ∧
        stage ((dir).file .stagedWalBoundary)
          (WAL.Boundary.encode ((installed).walBytes + WAL.frameSize * request.rows.length).toUInt64)
          appended = .error cause failed)
    (appendFrame : ∀ keeper, (observe current.reached).visible ((dir).file (.walSegment (state).writer.wal.active.first)) = some keeper →
      (state).BeforeMarkerWriteFrame keeper (storage poisoned) (storage (reachedState
        (append ((dir).file (.walSegment (installed).activeFirst)) (WAL.encodeBatch batch) poisoned))))
    (stageFrame : ∀ {appended keeper},
      (observe current.reached).visible ((dir).file (.walSegment (state).writer.wal.active.first)) = some keeper →
      append ((dir).file (.walSegment (installed).activeFirst)) (WAL.encodeBatch batch) poisoned = .ok () appended →
      stage ((dir).file .stagedWalBoundary)
        (WAL.Boundary.encode ((installed).walBytes + WAL.frameSize * request.rows.length).toUInt64)
        appended = .error cause failed →
      (state).BeforeMarkerWriteFrame keeper (storage appended) (storage failed))
    {names : heap → FilePath → Option Nat} {visible : heap → Nat → ByteArray}
    (reboot : RawWriteRebootEntry state view storage names visible failed rebooted)
    (source : RawMarkedOpenInterpreter heap stream) {input : FilePath} {returns : List (FilePath × IO.Error)}
    {keep : heap → Prop} {attempts : source.FailedCalls rebooted returns reached}
    (retryEffects : RawOpenRetryTrace.SelectedEffects view source rebooted (state).writer.target
      (fun heap => ⟨names heap, fun inode => [visible heap inode]⟩) (state).selectedRetryPath
      keep attempts)
    (starts : RawOpenRetryTrace.SelectedEntry view state (state).writer.target names visible rebooted → keep rebooted)
    (liveKeeper : keep reached → RawOpenRetryTrace.KeeperAt view dir (state).writer.target names visible reached)
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
    keep reached ∧
    (ready).SelectedWriteRecovery (returns := returns) (input := input) (view := view) (batch := batch)
      (target := (state).writer.target) (reached := reached) (phaseIdentity := phaseIdentity) (tokenIdentity := tokenIdentity)
      source names visible rebooted vacant get set ptrEq ∧
    (ready).ReopenedLedger current.current.history batch [] request input cause (source.openTable input reached) := by
  have valid := (ready).readPrefix.refines.1
  obtain ⟨keeper, named, _⟩ := initial.keeper
  have keeperBefore := WalKeeperPrefixFrame.ofFileFrame
    (prefixFrame.weaken fun _ member => NativeReadyState.crashPath_iff_write.mpr (.inr (.inl member))) named
  have othersBefore := prefixFrame.weaken (scope := (state).selectedRetryPath) fun _ member =>
    NativeReadyState.crashPath_iff_write.mpr (member.imp_right (fun keep => .inr keep))
  let frame (first last : heap) := (state).BeforeMarkerWriteFrame keeper (storage first) (storage last)
  have compose {first middle last : heap} (start : frame first middle) (finish : frame middle last) : frame first last :=
    start.trans finish
  obtain ⟨committed, kept⟩ := syncer.earlyErrorKeeps cache appender stager rename frame compose early
    (appendFrame keeper named) (stageFrame named)
  have markerFrame := (othersBefore.trans kept.1).weaken (scope := (· = (dir).file .walBoundary)) fun _ member => .inl member
  have protectedFrame := (othersBefore.trans kept.1).weaken (scope := (state).writeFramePath) fun _ member => .inr member
  have keeperFrame := keeperBefore.trans kept.2
  obtain ⟨admitted, pair, accepts⟩ := NativeReadyState.priorWriteTargetOfSample valid batch initial protectedFrame
    markerFrame (fun selected bound => (Option.some.inj (named.symm.trans bound)) ▸ keeperFrame)
    (names rebooted) reboot.chosen (visible rebooted) reboot.samplesWal
  obtain ⟨selected, rebootVacant, slots⟩ := reboot.selectsRetry initial protectedFrame admitted pair accepts
  have loaded := opened.phaseEffects.reads current.reached opened.phase _ (current.stored.trans (congrArg some valid.phase))
  refine ⟨current.uses.writeSchedules, ?_, rebootVacant, slots, ?_⟩
  · rw [request.runOnRawOpenPhase_afterPreparation dir lookup append stage sync rename opened.phase opened.get opened.set
      loaded nonempty prepared fits]
    simp only [guard, assigned, committed]
  · obtain ⟨carried, recovered⟩ :=
      (ready).opensAfterWriteRetries source prepared fits admitted names visible retryEffects selected
        (starts selected) liveKeeper vacant healthy phase ptrEq
    exact ⟨carried, recovered, recovered.replaysOldTarget request cause⟩

end
end Alvoki.Storage.DiskSession
