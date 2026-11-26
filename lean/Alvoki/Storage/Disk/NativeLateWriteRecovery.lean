import Alvoki.Storage.Disk.NativeWalGroupedTail
import Alvoki.Storage.Disk.NativeRawWriteReboot
import Alvoki.Storage.Disk.NativeAlignedWriteRecovery

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentCommit WalSegmentRepair

section

variable {heap stream : Type} {opened : NativeOpenedHandle heap}
  (current : NativeOpenedPosition opened) (view : OpenCloseHeapView heap FileImage)
  (cache : OpenSyncCacheRefs opened.files current.current.ready.state.session.directory.path)
  (appender : RawWalAppendCalls heap) (stager : RawWalStageCalls heap) (syncer : RawSyncCalls heap)
  (storage : heap → CheckpointStorageObservation)

local notation "ready" => current.current.ready
local notation "state" => current.current.ready.state
local notation "dir" => current.current.ready.state.session.directory
local notation "installed" => current.current.ready.state.writer.installed
local notation "append" => appender.run cache.active
local notation "stage" => stager.run cache.pending
local notation "sync" => syncer.group current.current.ready.state.session.directory.path cache.directory cache.active cache.pending
local notation "storageNames" => fun atHeap => CheckpointSurvivingFiles.names (CheckpointStorageObservation.files (storage atHeap))

/-- Take one joint reboot sample at the exact heap of the failed write.
The rename and final directory errors select a retry entry without
assuming any subsequent open has returned. -/
theorem NativeOpenedPosition.selectsAfterPublicationError
    (request : WriteRequest) (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {batch : List WAL.Write} {table : PackedTable}
    {guarded poisoned failed rebooted : heap} {cause : IO.Error}
    (nonempty : request.rows ≠ [])
    (prepared : prepareBatch (installed).table request.rows = some (batch, table))
    (fits : (installed).walBytes + WAL.frameSize * request.rows.length < UInt64.size)
    (guard : checkActiveSegmentWith dir installed lookup current.reached = .ok () guarded)
    (assigned : opened.set opened.phase .poisoned guarded = .ok () poisoned)
    (initial : NativeReadyStorage state (storage current.reached))
    (prefixFrame : (storage current.reached).Frames (state).crashPath (storage poisoned))
    (publishFrame : (storage poisoned).Frames (state).writeFramePath (storage failed))
    {liveNew : Bool} {allows : Bool → Prop}
    (publication :
      NativeReadyStorage state (storage poisoned) →
      commitBytesAt dir (installed).activeFirst (WAL.encodeBatch batch)
        ((installed).walBytes + WAL.frameSize * request.rows.length) append stage sync rename poisoned =
        .error cause failed ∧
      WalPublicationPayloads.ReachedWrite state batch request.rows (storage failed) liveNew allows)
    {names : heap → FilePath → Option Nat} {visible : heap → Nat → ByteArray}
    (reboot : RawWriteRebootEntry state view storage names visible failed rebooted)
    (later : ∀ target : Target, BatchRetryTarget (state).writer.history batch (state).writer.wal.active.first target →
      target.pair = (view.files rebooted).image.directory.active →
      ∀ ordinal ∈ (view.files rebooted).image.later.visible, target.range.through < ordinal) :
    opened.table.UsesOpenWriteSchedules dir opened.files opened.phase ∧
    request.runOnRawOpenPhase dir lookup append stage sync rename opened.phase opened.get opened.set current.reached =
      .error (.commitUnknown cause) failed ∧
    TryLockObserves (view.files rebooted).owners dir (.ok true) ∧
    (view.descriptors rebooted).slots = [] ∧
    ∃ target : Target, BatchRetryTarget (state).writer.history batch (state).writer.wal.active.first target ∧
      target.pair = (view.files rebooted).image.directory.active ∧
      RawOpenRetryTrace.SelectedEntry view state target names visible rebooted := by
  have valid := (ready).readPrefix.refines.1
  have loaded := opened.phaseEffects.reads current.reached opened.phase _ (current.stored.trans (congrArg some valid.phase))
  have protectedPrefix := prefixFrame.weaken fun _ kept => NativeReadyState.crashPath_iff_write.mpr (.inr (.inr kept))
  have frame := protectedPrefix.trans publishFrame
  obtain ⟨failedCommit, payloads, sameKeeper, oldMarker, newMarker, selections⟩ := publication (initial.frame prefixFrame)
  obtain ⟨target, admitted, pair, keeper⟩ :=
    selections.retryTargetAtReboot valid prepared fits initial frame sameKeeper oldMarker newMarker reboot
  have active : target.pair = (view.files rebooted).image.directory.active := by
    rw [reboot.image]
    exact pair
  obtain ⟨selected, rebootVacant, slots⟩ := reboot.selectsRetry initial frame admitted pair keeper (later target admitted active)
  refine ⟨current.uses.writeSchedules, ?_, rebootVacant, slots, target, admitted, active, selected⟩
  · rw [request.runOnRawOpenPhase_afterPreparation dir lookup append stage sync rename opened.phase opened.get opened.set
      loaded nonempty prepared fits]
    simp only [guard, assigned, failedCommit]

/-- Both late publication failures supply a commit return and the local
payloads at its reached heap. Sample that heap's reboot once, then use
the same recovery proof for either publication error. The open effects
are required only for the target determined by the rebooted marker. -/
theorem NativeOpenedPosition.recoversAfterPublicationError
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
    (publishFrame : (storage poisoned).Frames (state).writeFramePath (storage failed))
    {liveNew : Bool} {allows : Bool → Prop}
    (publication :
      NativeReadyStorage state (storage poisoned) →
      commitBytesAt dir (installed).activeFirst (WAL.encodeBatch batch)
        ((installed).walBytes + WAL.frameSize * request.rows.length) append stage sync rename poisoned =
        .error cause failed ∧
      WalPublicationPayloads.ReachedWrite state batch request.rows (storage failed) liveNew allows)
    {names : heap → FilePath → Option Nat} {visible : heap → Nat → ByteArray}
    (reboot : RawWriteRebootEntry state view storage names visible failed rebooted)
    (source : RawMarkedOpenInterpreter heap stream) {input : FilePath} {returns : List (FilePath × IO.Error)}
    {keep : Target → heap → Prop} {attempts : source.FailedCalls rebooted returns reached}
    (vacant : TryLockObserves (view.files reached).owners dir (.ok true))
    {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
    (observes : ∀ target : Target,
      BatchRetryTarget (state).writer.history batch (state).writer.wal.active.first target →
      target.pair = (view.files rebooted).image.directory.active →
      (∀ ordinal ∈ (view.files rebooted).image.later.visible, target.range.through < ordinal) ∧
      RawOpenRetryTrace.SelectedEffects view source rebooted target
        (fun heap => ⟨names heap, fun inode => [visible heap inode]⟩) (state).selectedRetryPath
        (keep target) attempts ∧
      (RawOpenRetryTrace.SelectedEntry view state target names visible rebooted → keep target rebooted) ∧
      (keep target reached → RawOpenRetryTrace.KeeperAt view dir target names visible reached) ∧
      (ready).ObservesHealthyWriteRetry (input := input) (view := view) (batch := batch)
        (target := target) (reached := reached) (phaseIdentity := phaseIdentity) (tokenIdentity := tokenIdentity)
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
    ∃ target : Target, target.pair = (view.files rebooted).image.directory.active ∧
      keep target reached ∧
      (ready).SelectedWriteRecovery (returns := returns) (input := input) (view := view) (batch := batch)
        (target := target) (reached := reached) (phaseIdentity := phaseIdentity) (tokenIdentity := tokenIdentity)
        source names visible rebooted vacant get set ptrEq ∧
      ∃ (plan : (ready).SelectedWritePlan batch target (view.files reached).image) (retained : List WAL.Write),
        (ready).ReopenedLedger plan.history batch retained request input cause (source.openTable input reached) := by
  obtain ⟨schedules, returned, rebootVacant, slots, target, admitted, active, selected⟩ :=
    current.selectsAfterPublicationError view cache appender stager syncer storage request lookup rename
      nonempty prepared fits guard assigned initial prefixFrame publishFrame publication reboot
      (fun target admitted pair => (observes target admitted pair).1)
  obtain ⟨_, retries, starts, liveKeeper, healthy⟩ := observes target admitted active
  obtain ⟨carried, recovered⟩ :=
    (ready).opensAfterWriteRetries source prepared fits admitted names visible retries selected
      (starts selected) liveKeeper vacant healthy phase ptrEq
  exact ⟨schedules, returned, rebootVacant, slots, target, active, carried, recovered,
    recovered.replaysSelectedLedger request cause⟩


/-- A late publication error and its joint reboot reach the ready table
through the same interpreter's failed opens. The recovery event uses
the exact issued request and diagnostic of the failed source call. -/
theorem NativeOpenedPosition.reopensReadyAfterPublicationError
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
    (publishFrame : (storage poisoned).Frames (state).writeFramePath (storage failed))
    {liveNew : Bool} {allows : Bool → Prop}
    (publication :
      NativeReadyStorage state (storage poisoned) →
      commitBytesAt dir (installed).activeFirst (WAL.encodeBatch batch)
        ((installed).walBytes + WAL.frameSize * request.rows.length) append stage sync rename poisoned =
        .error cause failed ∧
      WalPublicationPayloads.ReachedWrite state batch request.rows (storage failed) liveNew allows)
    (visible : heap → Nat → ByteArray)
    (reboot : RawWriteRebootEntry state view storage storageNames visible failed rebooted)
    (reset : reboot.DurableReset)
    (source : RawMarkedOpenInterpreter heap stream) {input : FilePath} {returns : List (FilePath × IO.Error)}
    {attempts : source.FailedCalls rebooted returns reached}
    (vacant : TryLockObserves (view.files reached).owners dir (.ok true))
    {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
    (later : ∀ target : Target, BatchRetryTarget (state).writer.history batch (state).writer.wal.active.first target →
      target.pair = (view.files rebooted).image.directory.active →
      ∀ ordinal ∈ (view.files rebooted).image.later.visible, target.range.through < ordinal)
    (observe : ∀ target : Target,
      BatchRetryTarget (state).writer.history batch (state).writer.wal.active.first target →
      target.pair = (view.files rebooted).image.directory.active →
      RawOpenRetryTrace.SelectedEffects view source rebooted target
        (fun atHeap => ⟨storageNames atHeap, fun inode => [visible atHeap inode]⟩) (state).selectedRetryPath
        (fun atHeap => RawOpenRetryTrace.KeeperAt view dir target storageNames visible atHeap ∧
          (state).SelectedRetryDurability target (storage atHeap)) attempts ∧
      (view.files reached).image.keeper.active = some target.trimmed ∧
      (view.files reached).image.later.visible = [] ∧
      (ready).ObservesHealthyWriteRetry (input := input) (view := view) (batch := batch)
        (target := target) (reached := reached) (phaseIdentity := phaseIdentity) (tokenIdentity := tokenIdentity)
        source storageNames vacant ∧
      NativeReadPosition.AlignedRetryEffects (current := ready) (batch := batch) (target := target)
        (input := input) (view := view) (reached := reached) (vacant := vacant) (source := source)
        (phaseIdentity := phaseIdentity) (tokenIdentity := tokenIdentity) storage visible)
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (phase : OpenPhaseCellEffects view.phase get set)
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool) :
    opened.table.UsesOpenWriteSchedules dir opened.files opened.phase ∧
    request.runOnRawOpenPhase dir lookup append stage sync rename opened.phase opened.get opened.set current.reached =
      .error (.commitUnknown cause) failed ∧
    TryLockObserves (view.files rebooted).owners dir (.ok true) ∧
    (view.descriptors rebooted).slots = [] ∧
    ∃ (target : Target) (plan : (ready).SelectedWritePlan batch target (view.files reached).image)
      (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle)
      (nextCache : OpenSyncCacheRefs handle.files start.current.ready.state.session.directory.path)
      (retained : List WAL.Write),
      target.pair = (view.files rebooted).image.directory.active ∧
      source.openTable input reached = .ok handle.table start.reached ∧
      start.current.history = plan.history ∧ (retained = [] ∨ retained = batch) ∧
      current.current.LedgerSuffix [.uncertainWriteCrashRecovered request input cause batch retained] start.current ∧
      InstalledClientReplay start.current.submissions start.current.ready.reads start.current.history
        start.current.ready.state.writer.installed start.current.ready.state.session ∧
      start.WriteStorageEntry view nextCache (storage start.reached) (visible start.reached) := by
  obtain ⟨schedules, returned, rebootVacant, slots, target, admitted, active, selected⟩ :=
    current.selectsAfterPublicationError view cache appender stager syncer storage request lookup rename
      nonempty prepared fits guard assigned initial prefixFrame publishFrame publication reboot later
  obtain ⟨effects, exactKeeper, noLater, healthy, aligned⟩ := observe target admitted active
  obtain ⟨plan, handle, start, nextCache, retained, opened, history, ledger, replay, physical⟩ :=
    (ready).opensReadyAfterAlignedRetries storage visible request cause prepared fits admitted effects selected
      (reboot.startsDurableRetry reset selected).2 exactKeeper noLater healthy phase ptrEq aligned
  have whole : retained = [] ∨ retained = batch := ledger.whole _ (List.mem_singleton_self _)
  exact ⟨schedules, returned, rebootVacant, slots, target, plan, handle, start, nextCache, retained,
    active, opened, history, whole, ledger, replay, physical⟩

end

end Alvoki.Storage.DiskSession
