import Alvoki.Storage.Disk.NativeWalGroupedTail
import Alvoki.Storage.Disk.NativeRawWriteReboot
import Alvoki.Storage.Disk.NativeAlignedWriteRecovery
import Alvoki.Storage.Disk.NativePublishedWriteSnapshot
import Alvoki.Storage.Disk.NativeFailedOpenTerminalLedger

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentCommit WalSegmentRepair
open WAL.Boundary (WalInodeImage)
open Sequential (SnapshotTable)

/-- The file group is the append, staging write and grouped sync
already executed by the commit schedule before marker rename. -/
noncomputable def RawSyncCalls.publicationFileGroup
    {heap : Type} {files : DiskTable.OpenSyncFiles} {directory : DiskDirectory}
    (calls : RawSyncCalls heap) (cache : OpenSyncCacheRefs files directory.path)
    (appender : RawWalAppendCalls heap) (stager : RawWalStageCalls heap)
    (first count : Nat) (bytes : ByteArray) : EStateM IO.Error heap Unit := do
  appender.run cache.active (directory.file (.walSegment first)) bytes
  stager.run cache.pending (directory.file .stagedWalBoundary) (WAL.Boundary.encode count.toUInt64)
  calls.group directory.path cache.directory cache.active cache.pending
    #[directory.file (.walSegment first), directory.file .stagedWalBoundary]

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

/-- Classify the publication tail from the public return of the issued
write. The local effects apply only after the reached file group, at
the literal rename or returned directory-barrier error. -/
theorem NativeOpenedPosition.reachedLatePublicationPayloads
    (request : WriteRequest) (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ atHeap, RunDirectoryInodeView dir (inodes atHeap) (runs atHeap))
    (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray)
    {cause : IO.Error} {failed : heap} (nonempty : request.rows ≠ [])
    (returned : request.runOnRawOpenPhase dir lookup append stage sync rename opened.phase opened.get opened.set current.reached =
      .error (.commitUnknown cause) failed)
    (initial : NativeReadyStorage state (observe current.reached).storageObservation)
    (effects : ∀ {batch : List WAL.Write} {table guarded poisoned appended staged grouped},
      prepareBatch (installed).table request.rows = some (batch, table) →
      checkActiveSegmentWith dir installed lookup current.reached = .ok () guarded →
      opened.set opened.phase .poisoned guarded = .ok () poisoned →
      append ((dir).file (.walSegment (installed).activeFirst)) (WAL.encodeBatch batch) poisoned = .ok () appended →
      stage ((dir).file .stagedWalBoundary)
        (WAL.Boundary.encode ((installed).walBytes + WAL.frameSize * request.rows.length).toUInt64)
        appended = .ok () staged →
      sync #[((dir).file (.walSegment (installed).activeFirst)), ((dir).file .stagedWalBoundary)] staged = .ok () grouped →
      (observe current.reached).storageObservation.Frames (state).crashPath (observe poisoned).storageObservation ∧
      syncer.WalGroupEffects cache view appender stager inodes observe inode buffered (installed).activeFirst
        ((installed).walBytes + WAL.frameSize * request.rows.length) (state).writer.wal.active.bytes
        (WAL.encodeBatch batch) poisoned appended staged grouped ∧
      (rename ((dir).file .stagedWalBoundary) ((dir).file .walBoundary) grouped = .error cause failed →
        ∃ effective : Bool, ∀ marker, (observe grouped).visible ((dir).file .stagedWalBoundary) = some marker →
          WalMarkerRenameEffect dir marker effective (observe grouped).storageObservation (observe failed).storageObservation) ∧
      (∀ {renamed}, rename ((dir).file .stagedWalBoundary) ((dir).file .walBoundary) grouped = .ok () renamed →
        sync #[(dir).path] renamed = .error cause failed →
        (∀ marker, (observe grouped).visible ((dir).file .stagedWalBoundary) = some marker →
          WalMarkerRenameEffect dir marker true (observe grouped).storageObservation (observe renamed).storageObservation) ∧
        ∃ effective, syncer.FinalRootEffects cache view (fun atHeap => (observe atHeap).storageObservation)
          (installed).activeFirst renamed failed effective)) :
    ∃ batch table guarded poisoned,
      prepareBatch (installed).table request.rows = some (batch, table) ∧
      (installed).walBytes + WAL.frameSize * request.rows.length < UInt64.size ∧
      checkActiveSegmentWith dir installed lookup current.reached = .ok () guarded ∧
      opened.set opened.phase .poisoned guarded = .ok () poisoned ∧
      let fileGroup := syncer.publicationFileGroup cache appender stager (installed).activeFirst
        ((installed).walBytes + WAL.frameSize * request.rows.length) (WAL.encodeBatch batch)
      fileGroup poisoned = .error cause failed ∨
      ∃ grouped, fileGroup poisoned = .ok () grouped ∧
        (rename ((dir).file .stagedWalBoundary) ((dir).file .walBoundary) grouped = .error cause failed ∨
          ∃ renamed, rename ((dir).file .stagedWalBoundary) ((dir).file .walBoundary) grouped = .ok () renamed ∧
            sync #[(dir).path] renamed = .error cause failed) ∧
        ∃ liveNew allows,
          WalPublicationPayloads.ReachedWrite state batch request.rows (observe failed).storageObservation liveNew allows := by
  obtain ⟨batch, table, guarded, poisoned, prepared, fits, guard, assigned, _, outcome⟩ :=
    current.classifiesCommitUnknown appender stager syncer cache request lookup rename nonempty returned
  refine ⟨batch, table, guarded, poisoned, prepared, fits, guard, assigned, ?_⟩
  have valid := (ready).readPrefix.refines.1
  cases outcome with
  | appendError stopped =>
    exact .inl (by simp only [RawSyncCalls.publicationFileGroup, Bind.bind, EStateM.bind, stopped])
  | stageError wrote stopped =>
    exact .inl (by simp only [RawSyncCalls.publicationFileGroup, Bind.bind, EStateM.bind, wrote, stopped])
  | groupError wrote remembered stopped =>
    exact .inl (by simp only [RawSyncCalls.publicationFileGroup, Bind.bind, EStateM.bind, wrote, remembered, stopped])
  | renameError wrote remembered synced failedRename =>
    obtain ⟨frame, group, renameError, _⟩ := effects prepared guard assigned wrote remembered synced
    obtain ⟨effective, renamed⟩ := renameError failedRename
    obtain ⟨_, payloads⟩ := syncer.failedMarkerRenameSelects cache view appender stager inodes observe inode buffered
      (rows := request.rows) valid (initial.frame frame) wrote remembered synced group rename failedRename renamed
    exact .inr ⟨_, by simp only [RawSyncCalls.publicationFileGroup, Bind.bind, EStateM.bind, wrote, remembered, synced],
      .inl failedRename, effective, _, payloads⟩
  | directory wrote remembered synced moved barrier =>
    obtain ⟨frame, group, _, directoryError⟩ := effects prepared guard assigned wrote remembered synced
    obtain ⟨renamed, effective, root⟩ := directoryError moved barrier
    obtain ⟨_, payloads⟩ := syncer.failedRootSyncFromPublication cache view appender stager inodes observe inode buffered
      (rows := request.rows) valid (initial.frame frame) wrote remembered synced group rename moved barrier renamed root
    exact .inr ⟨_, by simp only [RawSyncCalls.publicationFileGroup, Bind.bind, EStateM.bind, wrote, remembered, synced],
      .inr ⟨_, moved, barrier⟩, true, _, payloads⟩

private theorem NativeOpenedPosition.selectsReachedWrite
    {batch : List WAL.Write} {table : PackedTable} {rows : List (UInt64 × Option UInt64)}
    (prepared : prepareBatch (installed).table rows = some (batch, table))
    (fits : (installed).walBytes + WAL.frameSize * rows.length < UInt64.size)
    {failed rebooted : heap} (initial : NativeReadyStorage state (storage current.reached))
    (frame : (storage current.reached).Frames (state).writeFramePath (storage failed))
    {liveNew : Bool} {allows : Bool → Prop}
    (published : WalPublicationPayloads.ReachedWrite state batch rows (storage failed) liveNew allows)
    {names : heap → FilePath → Option Nat} {visible : heap → Nat → ByteArray}
    (reboot : RawWriteRebootEntry state view storage names visible failed rebooted) :
    TryLockObserves (view.files rebooted).owners dir (.ok true) ∧
    (view.descriptors rebooted).slots = [] ∧
    ∃ target : Target, BatchRetryTarget (state).writer.history batch (state).writer.wal.active.first target ∧
      target.pair = (view.files rebooted).image.directory.active ∧
      RawOpenRetryTrace.SelectedEntry view state target names visible rebooted := by
  obtain ⟨_, sameKeeper, oldMarker, newMarker, selections⟩ := published
  obtain ⟨target, admitted, pair, keeper⟩ :=
    selections.retryTargetAtReboot (ready).readPrefix.refines.1 prepared fits initial frame sameKeeper oldMarker newMarker reboot
  obtain ⟨selected, rebootVacant, slots⟩ := reboot.selectsRetry initial frame admitted pair keeper
  exact ⟨rebootVacant, slots, target, admitted, pair.trans reboot.activePair.symm, selected⟩

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
    (reboot : RawWriteRebootEntry state view storage names visible failed rebooted) :
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
  obtain ⟨failedCommit, physical⟩ := publication (initial.frame prefixFrame)
  obtain ⟨rebootVacant, slots, target, admitted, active, selected⟩ :=
    current.selectsReachedWrite view storage prepared fits initial frame physical reboot
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
  obtain ⟨retries, starts, liveKeeper, healthy⟩ := observes target admitted active
  obtain ⟨carried, recovered⟩ :=
    (ready).opensAfterWriteRetries source prepared fits admitted names visible retries selected
      (starts selected) liveKeeper vacant healthy phase ptrEq
  exact ⟨schedules, returned, rebootVacant, slots, target, active, carried, recovered,
    recovered.replaysSelectedLedger request cause⟩


section LiteralRetry

variable
    (request : WriteRequest) (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {batch : List WAL.Write} {table : PackedTable}
    {failed rebooted reached : heap} {cause : IO.Error}
    (nonempty : request.rows ≠ [])
    (prepared : prepareBatch current.current.ready.state.writer.installed.table request.rows = some (batch, table))
    (returned : request.runOnRawOpenPhase current.current.ready.state.session.directory lookup
      (appender.run cache.active) (stager.run cache.pending)
      (syncer.group current.current.ready.state.session.directory.path cache.directory cache.active cache.pending)
      rename opened.phase opened.get opened.set current.reached = .error (.commitUnknown cause) failed)
    (initial : NativeReadyStorage current.current.ready.state (storage current.reached))
    (protectedFiles : (storage current.reached).Frames current.current.ready.state.writeFramePath (storage failed))
    {liveNew : Bool} {allows : Bool → Prop}
    (publication : WalPublicationPayloads.ReachedWrite current.current.ready.state batch request.rows
      (storage failed) liveNew allows)
    (visible : heap → Nat → ByteArray)
    (reboot : RawWriteRebootEntry current.current.ready.state view storage
      (fun atHeap => (storage atHeap).files.names) visible failed rebooted)
    (reset : reboot.DurableReset)
    (source : RawMarkedOpenInterpreter heap stream) {input : FilePath} {returns : List (FilePath × IO.Error)}
    {attempts : source.FailedCalls rebooted returns reached}
    {firstOffset : Nat}
    (nameEffects : current.WalNameEffects appender stager syncer cache request lookup rename storage firstOffset
      (current.current.history.length + request.rows.length))
    (initialWindow : current.WalWindowAt storage firstOffset (current.current.history.length + request.rows.length))

include nonempty prepared returned initial protectedFiles publication reset nameEffects initialWindow

/-- The public return fixes the prepared write's bound. Its separately
observed publication payloads select one reboot before any open. -/

theorem NativeOpenedPosition.selectsDurableAfterPublicationError :
    opened.table.UsesOpenWriteSchedules dir opened.files opened.phase ∧
    (installed).walBytes + WAL.frameSize * request.rows.length < UInt64.size ∧
    TryLockObserves (view.files rebooted).owners dir (.ok true) ∧
    (view.descriptors rebooted).slots = [] ∧
    ∃ target : Target, BatchRetryTarget (state).writer.history batch (state).writer.wal.active.first target ∧
      target.pair = (view.files rebooted).image.directory.active ∧
      RawOpenRetryTrace.SelectedEntry view state target storageNames visible rebooted ∧
      RawOpenRetryTrace.RecoveryObservations view state target storage visible firstOffset
        target.range.through rebooted := by
  obtain ⟨_, _, _, _, _, fits, _, _, _, _⟩ :=
    current.classifiesCommitUnknown appender stager syncer cache request lookup rename nonempty returned
  obtain ⟨rebootVacant, slots, target, admitted, active, selected⟩ :=
    current.selectsReachedWrite view storage prepared fits initial protectedFiles publication reboot
  have nameFrame := current.preservesWalNamesAfterCommitUnknown appender stager syncer cache request lookup rename
    nonempty returned nameEffects
  have cutoff := current.current.ready.retryThrough_le prepared admitted
  have window := reboot.walNamespace nameFrame initialWindow.2
  exact ⟨current.uses.writeSchedules, fits, rebootVacant, slots, target, admitted, active, selected,
    reboot.startsRecoveryObservations reset selected (window.restrict (Nat.le_refl _) cutoff)⟩

/-- A late publication error and its joint reboot reach the ready table
through the same interpreter's failed opens. The recovery event uses
the exact issued request and diagnostic. Either keeper repair leaves
the table ready for another observed write and snapshot on that ledger. -/
theorem NativeOpenedPosition.reopensReadyAfterPublicationError
    (admission : source.AlignedAdmissionEffects view state input reached storage visible)
    (namespaceView : DirectoryReadNamespace) (root : DeviceInode)
    (rootBinding : (storageNames reached) (dir).path = some (namespaceView.modelObject root))
    {returnedAt : heap} {reopened : DiskTable}
    (openedTable : source.openTable input reached = .ok reopened returnedAt)
    (phaseIdentity : IO.Ref (Phase Installed) → Nat) (tokenIdentity : IO.Ref Unit → Nat)
    (retryEffects : ∀ target : Target,
      BatchRetryTarget (state).writer.history batch (state).writer.wal.active.first target →
      target.pair = (view.files rebooted).image.directory.active →
      RawOpenRetryTrace.SelectedEffects view source rebooted target
        (fun atHeap => ⟨storageNames atHeap, fun inode => [visible atHeap inode]⟩) (state).selectedRetryPath
        (RawOpenRetryTrace.RecoveryObservations view state target storage visible firstOffset
          target.range.through) attempts)
    (openEffects : ∀ target : Target, BatchRetryTarget (state).writer.history batch (state).writer.wal.active.first target →
      target.pair = (view.files rebooted).image.directory.active →
      ∀ (cache : HeldOpenCache heap) (plan : (ready).SelectedWritePlan batch target (view.files reached).image),
        LiteralOpenAuthority view dir cache cache.ready →
        namespaceView.modelObject root = cache.captured.inode cache.rootSlot.description →
        source.LiteralOpenEffects cache namespaceView root plan storage visible)
    (alignedEffects : ∀ target : Target, BatchRetryTarget (state).writer.history batch (state).writer.wal.active.first target →
      target.pair = (view.files rebooted).image.directory.active →
      ∀ (cache : HeldOpenCache heap) (plan : (ready).SelectedWritePlan batch target (view.files reached).image),
        LiteralOpenAuthority view dir cache cache.ready →
        namespaceView.modelObject root = cache.captured.inode cache.rootSlot.description →
        plan.layout.tail.size = 0 →
        source.LiteralAlignedRepairEffects cache plan storage visible)
    (replacementEffects : ∀ target : Target, BatchRetryTarget (state).writer.history batch (state).writer.wal.active.first target →
      target.pair = (view.files rebooted).image.directory.active →
      ∀ (cache : HeldOpenCache heap) (plan : (ready).SelectedWritePlan batch target (view.files reached).image),
        LiteralOpenAuthority view dir cache cache.ready →
        namespaceView.modelObject root = cache.captured.inode cache.rootSlot.description →
        0 < plan.layout.tail.size →
        source.LiteralKeeperReplacementEffects cache (current := ready) plan storage visible)
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (phase : OpenPhaseCellEffects view.phase get set)
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool) :
    opened.table.UsesOpenWriteSchedules dir opened.files opened.phase ∧
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
      start.WriteStorageEntry view nextCache (storage start.reached) (visible start.reached) ∧
      start.current.ready.state.session.directory = dir ∧
      (∀ offset ∈ start.current.ready.state.writer.wal.segments.map WalSegment.first, firstOffset ≤ offset) ∧
      (∀ through, start.current.ready.state.writer.wal.SettledNamespaceWindow
        start.current.ready.state.session.directory firstOffset through (storage start.reached)) ∧
      ∀ (α : Type) (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
        (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray)
        (nextRequest : WriteRequest) (sequence : UInt64) (writeHeap : heap),
        (inodes start.reached).visible = visible start.reached →
        nextRequest.rows ≠ [] →
        start.ObservesPublishedWrite appender stager syncer view nextCache inodes runs storage
          inode buffered nextRequest lookup rename sequence writeHeap →
        ∀ (read : SnapshotReadRequest α), handle.ObservesSnapshotToken writeHeap →
        let directory := start.current.ready.state.session.directory
        nextRequest.runOnRawOpenPhase directory lookup (appender.run nextCache.active) (stager.run nextCache.pending)
          (syncer.group directory.path nextCache.directory nextCache.active nextCache.pending)
          rename handle.phase handle.get handle.set start.reached = .ok sequence writeHeap ∧
        ∃ (nextBatch : List WAL.Write) (written last : NativeOpenedPosition handle)
          (events : List NativeExecutionEvent) (reference : SnapshotTable UInt64),
          written.reached = writeHeap ∧
          NativeOpenedTrace written [.acquire, .readAt written.pins.length read] events last ∧
          current.current.LedgerSuffix
            (.uncertainWriteCrashRecovered request input cause batch retained :: .acknowledged nextRequest nextBatch :: events)
            last.current ∧
          SnapshotWalReplay .empty (plan.history ++ nextBatch) reference ∧
          (∀ observed ∈ last.current.ready.reads, observed.agrees reference) := by
  obtain ⟨schedules, fits, rebootVacant, slots, target, admitted, active, selected, recovery⟩ :=
    current.selectsDurableAfterPublicationError view cache appender stager syncer storage request lookup rename
      nonempty prepared returned initial protectedFiles publication visible reboot reset nameEffects initialWindow
  obtain ⟨plan, handle, start, nextCache, retained, opened, history, ledger, replay, physical, sameDirectory, coversNext,
    _, nextWindow⟩ :=
    (ready).opensLiteralRepairedAfterWriteRetries storage visible request cause prepared fits admitted
      initialWindow.1 selected recovery (retryEffects target admitted active)
      admission namespaceView root rootBinding (openEffects target admitted active)
      (alignedEffects target admitted active) (replacementEffects target admitted active)
      phaseIdentity tokenIdentity phase ptrEq openedTable
  have whole : retained = [] ∨ retained = batch := ledger.whole _ (List.mem_singleton_self _)
  refine ⟨schedules, rebootVacant, slots, target, plan, handle, start, nextCache, retained,
    active, opened, history, whole, ledger, replay, physical, sameDirectory, coversNext, nextWindow, ?_⟩
  intro α inodes runs inode buffered nextRequest sequence writeHeap sameVisible nextNonempty seen read token
  obtain ⟨_, writeReturn, nextBatch, _, written, last, reference, events, _, _, writtenAt, snapshots, wrote,
    nextReplay, agrees, _⟩ :=
    start.acknowledgesAndReadsLatest ledger appender stager syncer view nextCache inodes runs storage inode buffered
      nextRequest lookup rename nextNonempty (sameVisible ▸ physical) seen read token
  exact ⟨writeReturn, nextBatch, written, last, events, reference, writtenAt, snapshots,
    wrote, history ▸ nextReplay, agrees⟩

/-- After the late error, a nonempty sequence of actual failed opens
may end the execution. The marker selected at reboot fixes the committed
history after the final failed open, including all or none of the pending batch. -/
theorem NativeOpenedPosition.stopsAfterPublicationErrorRetries
    {origin : NativeExecutionPosition} {events : List NativeExecutionEvent}
    (prior : origin.LedgerSuffix events current.current) (retried : returns ≠ [])
    (retryEffects : ∀ target : Target,
      BatchRetryTarget (state).writer.history batch (state).writer.wal.active.first target →
      target.pair = (view.files rebooted).image.directory.active →
      RawOpenRetryTrace.SelectedEffects view source rebooted target
        (fun atHeap => ⟨storageNames atHeap, fun inode => [visible atHeap inode]⟩) (state).selectedRetryPath
        (RawOpenRetryTrace.RecoveryObservations view state target storage visible firstOffset
          target.range.through) attempts) :
    opened.table.UsesOpenWriteSchedules dir opened.files opened.phase ∧
    (∀ event ∈ events, event.uncertainBatchWhole) ∧
    ∃ (target : Target) (earlier : List (FilePath × IO.Error)) (lastInput : FilePath) (diagnostic : IO.Error) (issued : heap),
      target.pair = (view.files rebooted).image.directory.active ∧
      returns = earlier ++ [(lastInput, diagnostic)] ∧ source.FailedCalls rebooted earlier issued ∧
      source.openTable lastInput issued = .error diagnostic reached ∧
      ∃ plan : (ready).SelectedWritePlan batch target (view.files reached).image,
        plan.layout.VisibleWal dir (storageNames reached) (visible reached) ∧
        RawOpenRetryTrace.SelectedEntry view state target storageNames visible reached ∧
        (state).SelectedRetryDurability target (storage reached) ∧
        RawOpenRetryTrace.LaterWalAt view dir target storageNames reached ∧
        target.range.through = plan.history.length ∧
        let history := origin.history ++ events.flatMap NativeExecutionEvent.writes
        let submissions := (origin.submissions ++ events.flatMap NativeExecutionEvent.submissions) ++ [.uncertainBatch batch]
        let reads := origin.ready.reads ++ events.flatMap NativeExecutionEvent.reads
        (plan.history = history ∨ plan.history = history ++ batch) ∧
        PendingClientReplay submissions reads plan.history ∧ ∀ read ∈ reads, read.BoundedBy plan.history.length := by
  obtain ⟨schedules, fits, _, _, target, admitted, active, selected, recovery⟩ :=
    current.selectsDurableAfterPublicationError view cache appender stager syncer storage request lookup rename
      nonempty prepared returned initial protectedFiles publication visible reboot reset nameEffects initialWindow
  obtain ⟨whole, earlier, lastInput, diagnostic, issued, reported, previous, call, plan, physical, last, settled,
    later, allowed, replay, bounds⟩ :=
    NativeExecutionPosition.refinesFailedOpenTerminalLedger (current := current.current) prior prepared fits admitted
      storage visible initialWindow.1 selected recovery attempts retried (retryEffects target admitted active)
  have through := (congrArg (fun target : Target => target.range.through) plan.targetEq).symm.trans plan.layout.through
  exact ⟨schedules, whole, target, earlier, lastInput, diagnostic, issued, active, reported, previous, call,
    plan, physical, last, settled, later, through, allowed, replay, bounds⟩

end LiteralRetry

end

end Alvoki.Storage.DiskSession
