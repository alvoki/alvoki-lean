import Alvoki.Storage.Disk.NativeWalGroupedTail
import Alvoki.Storage.Disk.NativeRawWriteReboot
import Alvoki.Storage.Disk.NativeAlignedWriteRecovery
import Alvoki.Storage.Disk.NativeFailedOpenTerminalLedger
import Alvoki.Storage.Disk.NativeReadyCallRefinement

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting WalSegmentCommit WalSegmentRepair
open WAL.Boundary (WalInodeImage)

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

/-- The handoff after one observed reboot. The write fixes the batch,
and the sampled files fix a target before the interpreter tries to open. -/
structure NativeExecutionPosition.SelectedWriteReboot
    {heap : Type} (current : NativeExecutionPosition) (view : OpenCloseHeapView heap FileImage)
    (storage : heap → CheckpointStorageObservation) (visible : heap → Nat → ByteArray)
    (firstOffset : Nat) (request : WriteRequest) (batch : List WAL.Write) (table : PackedTable)
    (target : Target) (failed rebooted : heap) : Prop where
  prepared : prepareBatch current.ready.state.writer.installed.table request.rows = some (batch, table)
  fits : current.ready.state.writer.installed.walBytes + WAL.frameSize * request.rows.length < UInt64.size
  covers : ∀ offset ∈ current.ready.state.writer.wal.segments.map WalSegment.first, firstOffset ≤ offset
  vacant : TryLockObserves (view.files rebooted).owners current.ready.state.session.directory (.ok true)
  sample : RawWriteRebootEntry current.ready.state view storage (fun atHeap => (storage atHeap).files.names)
    visible failed rebooted
  admitted : BatchRetryTarget current.ready.state.writer.history batch current.ready.state.writer.wal.active.first target
  selected : RawOpenRetryTrace.SelectedEntry view current.ready.state target
    (fun atHeap => (storage atHeap).files.names) visible rebooted
  recovery : RawOpenRetryTrace.RecoveryObservations view current.ready.state target storage visible firstOffset
    target.range.through rebooted

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

/-- Local physical effects of the reached file group and a late publication callback. -/
def NativeOpenedPosition.LatePublicationEffects
    (request : WriteRequest) (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ atHeap, RunDirectoryInodeView dir (inodes atHeap) (runs atHeap))
    (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray)
    (cause : IO.Error) (failed : heap) : Prop :=
  ∀ {batch : List WAL.Write} {table guarded poisoned appended staged grouped},
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
        (installed).activeFirst renamed failed effective)

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
    (effects : current.LatePublicationEffects view cache appender stager syncer request lookup rename
      inodes runs observe inode buffered cause failed) :
    ∃ batch table guarded poisoned,
      prepareBatch (installed).table request.rows = some (batch, table) ∧
      (installed).walBytes + WAL.frameSize * request.rows.length < UInt64.size ∧
      checkActiveSegmentWith dir installed lookup current.reached = .ok () guarded ∧
      opened.set opened.phase .poisoned guarded = .ok () poisoned ∧
      syncer.PublicationOutcome cache appender stager rename (installed).activeFirst
        ((installed).walBytes + WAL.frameSize * request.rows.length) (WAL.encodeBatch batch) poisoned
        (.error cause failed) ∧
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
  refine ⟨batch, table, guarded, poisoned, prepared, fits, guard, assigned, outcome, ?_⟩
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


/-- Select the next recovery input from physical publication effects at the
reached heap, whether the outstanding write has returned or stopped. -/
theorem NativeOpenedPosition.selectsDurableReachedWrite
    {request : WriteRequest} {batch : List WAL.Write} {table : PackedTable}
    (prepared : prepareBatch (installed).table request.rows = some (batch, table))
    (fits : (installed).walBytes + WAL.frameSize * request.rows.length < UInt64.size)
    {failed rebooted : heap} (initial : NativeReadyStorage state (storage current.reached))
    (frame : (storage current.reached).Frames (state).writeFramePath (storage failed))
    {liveNew : Bool} {allows : Bool → Prop}
    (published : WalPublicationPayloads.ReachedWrite state batch request.rows (storage failed) liveNew allows)
    (visible : heap → Nat → ByteArray)
    (reboot : RawWriteRebootEntry state view storage storageNames visible failed rebooted)
    (reset : reboot.DurableReset) {firstOffset : Nat}
    (names : WalNamePresenceFrame dir firstOffset (current.current.history.length + request.rows.length)
      (storage current.reached) (storage failed))
    (initialWindow : current.WalWindowAt storage firstOffset (current.current.history.length + request.rows.length)) :
    ∃ target : Target, current.current.SelectedWriteReboot view storage visible firstOffset request batch table
      target failed rebooted := by
  obtain ⟨rebootVacant, _, target, admitted, _, selected⟩ :=
    current.selectsReachedWrite view storage prepared fits initial frame published reboot
  have cutoff := current.current.ready.retryThrough_le prepared admitted
  have window := reboot.walNamespace names initialWindow.2
  exact ⟨target, prepared, fits, initialWindow.1, rebootVacant, reboot, admitted, selected,
    reboot.startsRecoveryObservations reset selected (window.restrict (Nat.le_refl _) cutoff)⟩

section LiteralRetry

variable
    (request : WriteRequest) (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {batch : List WAL.Write} {table : PackedTable}
    {failed rebooted : heap} {cause : IO.Error}
    (nonempty : request.rows ≠ [])
    (prepared : prepareBatch current.current.ready.state.writer.installed.table request.rows = some (batch, table))
    (returned : request.runOnRawOpenPhase current.current.ready.state.session.directory lookup
      (appender.run cache.active) (stager.run cache.pending)
      (syncer.group current.current.ready.state.session.directory.path cache.directory cache.active cache.pending)
      rename opened.phase opened.get opened.set current.reached = .error (.commitUnknown cause) failed)
    (initial : NativeReadyStorage current.current.ready.state (storage current.reached))
    (fileFrames : current.WriteCallbackFrames appender stager syncer cache request lookup rename
      (fun before after => (storage before).Frames current.current.ready.state.writeFramePath (storage after)))
    {liveNew : Bool} {allows : Bool → Prop}
    (publication : WalPublicationPayloads.ReachedWrite current.current.ready.state batch request.rows
      (storage failed) liveNew allows)
    (visible : heap → Nat → ByteArray)
    (reboot : RawWriteRebootEntry current.current.ready.state view storage
      (fun atHeap => (storage atHeap).files.names) visible failed rebooted)
    (reset : reboot.DurableReset)
    {firstOffset : Nat}
    (nameEffects : current.WalNameEffects appender stager syncer cache request lookup rename storage firstOffset
      (current.current.history.length + request.rows.length))
    (initialWindow : current.WalWindowAt storage firstOffset (current.current.history.length + request.rows.length))

include nonempty prepared returned initial fileFrames publication reset nameEffects initialWindow

/-- The public return fixes the prepared write's bound. Its separately
observed publication payloads select one reboot before any open. -/

theorem NativeOpenedPosition.selectsDurableAfterPublicationError :
    opened.table.UsesOpenWriteSchedules dir opened.files opened.phase ∧
    ∃ target : Target,
      current.current.SelectedWriteReboot view storage visible firstOffset request batch table target failed rebooted := by
  obtain ⟨_, _, _, _, actualBatch, fits, guarded, poisoned, _, outcome⟩ :=
    current.classifiesCommitUnknown appender stager syncer cache request lookup rename nonempty returned
  have protectedFiles := fileFrames.throughPublication CheckpointStorageObservation.Frames.trans
    actualBatch guarded poisoned outcome
  have nameFrame := nameEffects.throughPublication WalNamePresenceFrame.trans actualBatch guarded poisoned outcome
  exact ⟨current.uses.writeSchedules, current.selectsDurableReachedWrite view storage prepared fits initial protectedFiles
    publication visible reboot reset nameFrame initialWindow⟩

end LiteralRetry

end

namespace NativeExecutionPosition.SelectedWriteReboot

section

variable {heap stream : Type} {source : RawMarkedOpenInterpreter heap stream}
  {view : OpenCloseHeapView heap FileImage}
  {storage : heap → CheckpointStorageObservation} {visible : heap → Nat → ByteArray}
  {firstOffset : Nat}
  {request : WriteRequest} {batch : List WAL.Write} {table : PackedTable} {target : Target}
  {failed rebooted reached : heap} {returns : List (FilePath × IO.Error)}
  {attempts : source.FailedCalls rebooted returns reached}

local notation "names" => fun atHeap => CheckpointSurvivingFiles.names (CheckpointStorageObservation.files (storage atHeap))

/-- The crash image fixes the plan before the opener or its outcome is
chosen. Its history is either the prior history or the whole prepared batch. -/
theorem sampledPlan {current : NativeExecutionPosition}
    (handoff : current.SelectedWriteReboot view storage visible firstOffset request batch table target failed rebooted) :
    ∃ plan : current.ready.SelectedWritePlan batch target (view.files rebooted).image,
      ∀ {stream : Type} (opener : RawMarkedOpenInterpreter heap stream) namespaceView root,
        current.ready.state.writer.target.pair.manifest = none →
        opener.ReplaysWalBeforeCheckpointAtOpen view current.ready.state.session.directory current.ready.state.writer.wal.active.first
          storage visible rebooted namespaceView root
          plan.history := by
  obtain ⟨plan⟩ := current.ready.preparesSelectedWrite handoff.prepared handoff.fits handoff.admitted
    handoff.selected.valid handoff.selected.manifest
  refine ⟨plan, ?_⟩
  intro stream opener namespaceView root absent
  exact @NativeReadPosition.SelectedWritePlan.replaysWalBeforeCheckpointAtOpen
    (source := opener) (namespaceView := namespaceView) (root := root) (plan := plan)
    (selected := handoff.selected) (recovery := handoff.recovery) (covers := handoff.covers)
    (noManifest := absent)

/-- End at a literal failed open on the selected reboot's retry prefix. -/
theorem stopsAfterRetries
    {origin current : NativeExecutionPosition} {events : List NativeExecutionEvent}
    (handoff : current.SelectedWriteReboot view storage visible firstOffset request batch table target failed rebooted)
    (prior : origin.LedgerSuffix events current)
    (retried : returns ≠ [])
    (effects : RawOpenRetryTrace.SelectedEffects view source rebooted target
      (fun atHeap => ⟨names atHeap, fun inode => [visible atHeap inode]⟩) current.ready.state.selectedRetryPath
      (RawOpenRetryTrace.RecoveryObservations view current.ready.state target storage visible firstOffset
        target.range.through) attempts) :
    (∀ event ∈ events, event.uncertainBatchWhole) ∧
    ∃ earlier input diagnostic issued,
      returns = earlier ++ [(input, diagnostic)] ∧ source.FailedCalls rebooted earlier issued ∧
      source.openTable input issued = .error diagnostic reached ∧
      ∃ plan : current.ready.SelectedWritePlan batch target (view.files reached).image,
        plan.layout.VisibleWal current.ready.state.session.directory (names reached) (visible reached) ∧
        RawOpenRetryTrace.SelectedEntry view current.ready.state target names visible reached ∧
        current.ready.state.SelectedRetryDurability target (storage reached) ∧
        RawOpenRetryTrace.LaterWalAt view current.ready.state.session.directory target names reached ∧
        target.range.through = plan.history.length ∧
        let history := origin.history ++ events.flatMap NativeExecutionEvent.writes
        let submissions := (origin.submissions ++ events.flatMap NativeExecutionEvent.submissions) ++ [.uncertainBatch batch]
        let reads := origin.ready.reads ++ events.flatMap NativeExecutionEvent.reads
        (plan.history = history ∨ plan.history = history ++ batch) ∧
        PendingClientReplay submissions reads plan.history ∧ ∀ read ∈ reads, read.BoundedBy plan.history.length := by
  obtain ⟨whole, earlier, input, diagnostic, issued, reported, previous, call, plan, physical, selected,
    durable, later, allowed, replay, bounded⟩ :=
    NativeExecutionPosition.refinesFailedOpenTerminalLedger (current := current) prior handoff.prepared handoff.fits handoff.admitted storage visible
      handoff.covers handoff.selected handoff.recovery attempts retried effects
  exact ⟨whole, earlier, input, diagnostic, issued, reported, previous, call, plan, physical, selected, durable, later,
    (congrArg (fun target : Target => target.range.through) plan.targetEq).symm.trans plan.layout.through,
    allowed, replay, bounded⟩

variable {opened : NativeOpenedHandle heap} {last : NativeOpenedPosition opened}

local notation "ready" => last.current.ready
local notation "state" => last.current.ready.state
local notation "dir" => last.current.ready.state.session.directory

/-- Given a selected reboot and the incoming ledger, interpret the actual
successful public open following that reboot's own block of reported errors.
Subsequent calls carry the same ledger from the returned handle and fresh pins.
The native write interpreter supplies `fun h => (inodes h).visible` for
`readBytes`, so the ready-entry byte equality is reflexive for those inodes. -/
abbrev OpenContinuation (position : NativeOpenedPosition opened)
    (openView : OpenCloseHeapView heap FileImage) (observe : heap → CheckpointStorageObservation)
    (readBytes : heap → Nat → ByteArray) (firstOffset : Nat) (request : WriteRequest)
    (batch : List WAL.Write) (target : Target) (rebooted : heap)
    (opener : RawMarkedOpenInterpreter heap stream)
    (origin : NativeExecutionPosition) (events : List NativeExecutionEvent) (cause : IO.Error) : Prop :=
    let files := fun atHeap => (observe atHeap).files.names
    let previous := position.current.ready
    let directory := previous.state.session.directory
    ∀ {returns : List (FilePath × IO.Error)} {reached : heap} {attempts : opener.FailedCalls rebooted returns reached}
    (_retryEffects : RawOpenRetryTrace.SelectedEffects openView opener rebooted target
      (fun atHeap => ⟨files atHeap, fun inode => [readBytes atHeap inode]⟩) previous.state.selectedRetryPath
      (RawOpenRetryTrace.RecoveryObservations openView previous.state target observe readBytes firstOffset
        target.range.through) attempts)
    {input : FilePath} (_admission : opener.AlignedAdmissionEffects openView previous.state input reached observe readBytes)
    (namespaceView : DirectoryReadNamespace) (root : DeviceInode)
    (_rootBinding : (files reached) directory.path = some (namespaceView.modelObject root))
    (_openEffects : ∀ (cache : HeldOpenCache heap) (plan : previous.SelectedWritePlan batch target (openView.files reached).image),
      LiteralOpenAuthority openView directory cache cache.ready →
      namespaceView.modelObject root = cache.captured.inode cache.rootSlot.description →
      opener.LiteralOpenEffects cache namespaceView root plan observe readBytes)
    (_alignedEffects : ∀ (cache : HeldOpenCache heap) (plan : previous.SelectedWritePlan batch target (openView.files reached).image),
      LiteralOpenAuthority openView directory cache cache.ready →
      namespaceView.modelObject root = cache.captured.inode cache.rootSlot.description →
      plan.layout.tail.size = 0 →
      opener.LiteralAlignedRepairEffects cache plan observe readBytes)
    (_replacementEffects : ∀ (cache : HeldOpenCache heap) (plan : previous.SelectedWritePlan batch target (openView.files reached).image),
      LiteralOpenAuthority openView directory cache cache.ready →
      namespaceView.modelObject root = cache.captured.inode cache.rootSlot.description →
      0 < plan.layout.tail.size →
      opener.LiteralKeeperReplacementEffects cache (current := previous) plan observe readBytes)
    (_phaseIdentity : IO.Ref (Phase Installed) → Nat) (_tokenIdentity : IO.Ref Unit → Nat)
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (_phase : OpenPhaseCellEffects openView.phase get set)
    (_ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool)
    {returnedAt : heap} {tableReturned : DiskTable}
    (_returned : opener.openTable input reached = .ok tableReturned returnedAt),
    ∃ (plan : previous.SelectedWritePlan batch target (openView.files reached).image)
      (handle : NativeOpenedHandle heap) (start : NativeOpenedPosition handle)
      (nextCache : OpenSyncCacheRefs handle.files start.current.ready.state.session.directory.path)
      (retained : List WAL.Write),
      let resumed := events ++ [.uncertainWriteCrashRecovered request input cause batch retained]
      tableReturned = handle.table ∧ start.reached = returnedAt ∧
      start.current.history = plan.history ∧ target.range.through = plan.history.length ∧ (retained = [] ∨ retained = batch) ∧
      origin.LedgerSuffix resumed start.current ∧
      InstalledClientReplay start.current.submissions start.current.ready.reads start.current.history
        start.current.ready.state.writer.installed start.current.ready.state.session ∧
      start.WriteStorageEntry openView nextCache (observe start.reached) (readBytes start.reached) ∧ start.pins = [] ∧
      start.current.ready.state.session.directory = directory ∧
      (∀ offset ∈ start.current.ready.state.writer.wal.segments.map WalSegment.first, firstOffset ≤ offset) ∧
      (∀ through, start.current.ready.state.writer.wal.SettledNamespaceWindow
        start.current.ready.state.session.directory firstOffset through (observe start.reached)) ∧
      ∀ (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage),
        readBytes start.reached = (inodes start.reached).visible →
        start.ContinuesReadyCalls nextCache openView inodes runs observe origin resumed firstOffset

private theorem openContinuation
    (handoff : last.current.SelectedWriteReboot view storage visible firstOffset request batch table target failed rebooted)
    {origin : NativeExecutionPosition} {events : List NativeExecutionEvent} {cause : IO.Error}
    (prior : origin.LedgerSuffix events last.current) :
    OpenContinuation last view storage visible firstOffset request batch target rebooted source origin events cause := by
  intro returns reached attempts retryEffects input admission namespaceView root rootBinding
    openEffects alignedEffects replacementEffects phaseIdentity tokenIdentity get set phase ptrEq returnedAt tableReturned returned
  obtain ⟨plan, handle, start, nextCache, opened, history, submissions, reads, replay, physical, pins, sameDirectory, covers,
    _, window⟩ :=
    (ready).opensLiteralRepairedAfterWriteRetries storage visible handoff.prepared handoff.fits
      handoff.admitted handoff.covers handoff.selected handoff.recovery retryEffects admission namespaceView root rootBinding
      openEffects alignedEffects replacementEffects phaseIdentity tokenIdentity phase ptrEq returned
  obtain ⟨retained, ledger⟩ := plan.ledgerAfterReopen start.current history submissions reads request input cause
  have endpoints := returned.symm.trans opened
  have resumed := prior.append ledger
  refine ⟨plan, handle, start, nextCache, retained, (EStateM.Result.ok.inj endpoints).1, (EStateM.Result.ok.inj endpoints).2.symm,
    history, (congrArg (fun target : Target => target.range.through) plan.targetEq).symm.trans plan.layout.through,
    ledger.whole _ (List.mem_singleton_self _), resumed, replay, physical, pins, sameDirectory, covers, window, ?_⟩
  intro inodes runs sameBytes
  exact start.continuesReadyCalls nextCache view inodes runs storage origin _ firstOffset pins resumed
    (by rw [← sameBytes]; exact physical) window

/-- The actual uncertain write returned at the heap sampled by this reboot. -/
theorem opensReadyAfterRetries
    (handoff : last.current.SelectedWriteReboot view storage visible firstOffset request batch table target failed rebooted)
    {writes : NativeReadyWriteCalls opened} {issuer : opened.LatestIssuer} {cause : IO.Error}
    (_returnedWrite : (NativeReturnedCall.write request (.error (.commitUnknown cause))).Reaches
      writes issuer (last.pins.map NativeOpenedPin.raw) last.reached failed)
    {origin : NativeExecutionPosition} {events : List NativeExecutionEvent}
    (prior : origin.LedgerSuffix events last.current) :
    OpenContinuation last view storage visible firstOffset request batch target rebooted source origin events cause :=
  openContinuation handoff prior

/-- A reported failed open finishes the first retry block. The second
reboot supplies a new physical selection of the same target. Keep the
original write's batch and ledger when interpreting the next returned table. -/
theorem opensReadyAfterRetryReboot
    {first issued afterFailure : heap} {earlier : List (FilePath × IO.Error)}
    (handoff : last.current.SelectedWriteReboot view storage visible firstOffset request batch table target failed first)
    {writes : NativeReadyWriteCalls opened} {issuer : opened.LatestIssuer} {cause : IO.Error}
    (_returnedWrite : (NativeReturnedCall.write request (.error (.commitUnknown cause))).Reaches
      writes issuer (last.pins.map NativeOpenedPin.raw) last.reached failed)
    {origin : NativeExecutionPosition} {events : List NativeExecutionEvent}
    (prior : origin.LedgerSuffix events last.current)
    (_firstAttempts : source.FailedCalls first earlier issued) {failedInput : FilePath} {diagnostic : IO.Error}
    (_failedOpen : source.openTable failedInput issued = .error diagnostic afterFailure)
    {observedState : NativeReadyState} (sameState : observedState = (state))
    (secondBoot : RawWriteRebootEntry observedState view storage names visible afterFailure rebooted)
    (selected : RawOpenRetryTrace.SelectedEntry view observedState target names visible rebooted)
    (vacant : TryLockObserves (view.files rebooted).owners observedState.session.directory (.ok true))
    (recovery : RawOpenRetryTrace.RecoveryObservations view observedState target storage visible firstOffset target.range.through rebooted) :
    OpenContinuation last view storage visible firstOffset request batch target rebooted source origin events cause := by
  subst observedState
  have resumed : last.current.SelectedWriteReboot view storage visible firstOffset request batch table target afterFailure rebooted :=
    ⟨handoff.prepared, handoff.fits, handoff.covers, vacant, secondBoot, handoff.admitted, selected, recovery⟩
  intro returns reached attempts
  exact openContinuation (source := source) (cause := cause) resumed prior
    (returns := returns) (reached := reached) (attempts := attempts)

end

end NativeExecutionPosition.SelectedWriteReboot

/-- The observed ready prefix and the uncertain write share a handle and
an entry heap. Sample the resulting publication at its returned heap and
place the selected old-or-whole batch after that exact client prefix. -/
theorem NativeReturnedCalls.selectsAfterLatePublicationError
    {heap : Type} {opened : NativeOpenedHandle heap} {writes : NativeReadyWriteCalls opened}
    {issuer : opened.LatestIssuer} {request : WriteRequest} {cause : IO.Error}
    {calls : List (NativeReturnedCall opened)} {failed : heap}
    (start : NativeOpenedPosition opened)
    (executed : NativeReturnedCalls writes issuer start.reached (start.pins.map NativeOpenedPin.raw)
      (calls ++ [.write request (.error (.commitUnknown cause))]) failed)
    {origin : NativeExecutionPosition} {earlier : List NativeExecutionEvent}
    (prior : origin.LedgerSuffix earlier start.current)
    (view : OpenCloseHeapView heap FileImage) (inodes : heap → WalInodeImage) (runs : heap → RunUnlinkImage)
    (observe : ∀ atHeap, RunDirectoryInodeView opened.directory (inodes atHeap) (runs atHeap))
    (inode : IO.FS.Handle → Nat) (buffered : heap → IO.FS.Handle → ByteArray)
    (effects : writes.ReturnEffects view inodes runs (fun atHeap => (observe atHeap).storageObservation) inode buffered)
    (initial : writes.StorageAt view (fun atHeap => (observe atHeap).storageObservation)
      (fun atHeap => (inodes atHeap).visible) start)
    {firstOffset : Nat}
    (readyNames : writes.WalWindowEffects (fun atHeap => (observe atHeap).storageObservation) firstOffset
      (start.current.history.length + (calls.map NativeReturnedCall.requestedRows).sum + request.rows.length))
    (initialWindow : start.WalWindowAt (fun atHeap => (observe atHeap).storageObservation) firstOffset
      (start.current.history.length + (calls.map NativeReturnedCall.requestedRows).sum + request.rows.length)) :
    ∃ (last : NativeOpenedPosition opened) (events : List NativeExecutionEvent),
      NativeReturnedCalls writes issuer start.reached (start.pins.map NativeOpenedPin.raw) calls last.reached ∧
      events.length = calls.length ∧ (∀ pair ∈ calls.zip events, pair.1.Records pair.2) ∧
      origin.LedgerSuffix (earlier ++ events) last.current ∧
      (NativeReturnedCall.write request (.error (.commitUnknown cause))).Reaches
        writes issuer (last.pins.map NativeOpenedPin.raw) last.reached failed ∧
      let state := last.current.ready.state
      let files := fun atHeap => last.directory.symm ▸ observe atHeap
      let storage := fun atHeap => (files atHeap).storageObservation
      let names := fun atHeap => (storage atHeap).files.names
      let visible := fun atHeap => (inodes atHeap).visible
      let cache := writes.cacheAtPosition last
      last.LatePublicationEffects view cache writes.appender writes.stager writes.syncer request writes.lookup
        writes.rename inodes runs files inode buffered cause failed →
      last.WriteCallbackFrames writes.appender writes.stager writes.syncer cache request writes.lookup writes.rename
        (fun before after => (storage before).Frames state.writeFramePath (storage after)) →
      last.WalNameEffects writes.appender writes.stager writes.syncer cache request writes.lookup writes.rename
        storage firstOffset (last.current.history.length + request.rows.length) →
      ∃ batch table guarded poisoned,
        prepareBatch state.writer.installed.table request.rows = some (batch, table) ∧
        state.writer.installed.walBytes + WAL.frameSize * request.rows.length < UInt64.size ∧
        checkActiveSegmentWith state.session.directory state.writer.installed writes.lookup last.reached = .ok () guarded ∧
        opened.set opened.phase .poisoned guarded = .ok () poisoned ∧
        let fileGroup := writes.syncer.publicationFileGroup cache writes.appender writes.stager
          state.writer.installed.activeFirst (state.writer.installed.walBytes + WAL.frameSize * request.rows.length)
          (WAL.encodeBatch batch)
        fileGroup poisoned = .error cause failed ∨
        ∃ grouped, fileGroup poisoned = .ok () grouped ∧
          ∀ {rebooted : heap} (reboot : RawWriteRebootEntry state view storage names visible failed rebooted),
            reboot.DurableReset →
            ∃ (target : Target) (plan : last.current.ready.SelectedWritePlan batch target (view.files rebooted).image),
              last.current.SelectedWriteReboot view storage visible firstOffset request batch table target failed rebooted ∧
              target.range.through = plan.history.length ∧
              let history := origin.history ++ (earlier ++ events).flatMap NativeExecutionEvent.writes
              let submissions := (origin.submissions ++ (earlier ++ events).flatMap NativeExecutionEvent.submissions) ++
                [.uncertainBatch batch]
              let reads := origin.ready.reads ++ (earlier ++ events).flatMap NativeExecutionEvent.reads
              (plan.history = history ∨ plan.history = history ++ batch) ∧
              PendingClientReplay submissions reads plan.history ∧
              (∀ read ∈ reads, read.BoundedBy plan.history.length) ∧
              ∀ {stream : Type} (opener : RawMarkedOpenInterpreter heap stream) namespaceView root,
                state.writer.target.pair.manifest = none →
                opener.ReplaysWalBeforeCheckpointAtOpen view (state).session.directory (state).writer.wal.active.first
                  storage visible rebooted namespaceView root plan.history := by
  obtain ⟨last, events, ran, length, records, through, write⟩ :=
    executed.refinesReadyBeforeCommitUnknown start prior view inodes runs observe inode buffered effects
      initial readyNames initialWindow
  refine ⟨last, events, ran, length, records, through, write.observed, ?_⟩
  intro state files storage names visible cache lateEffects fileFrames nameEffects
  obtain ⟨batch, table, guarded, poisoned, prepared, fits, guard, assigned, source, classified⟩ :=
    last.reachedLatePublicationPayloads view cache writes.appender writes.stager writes.syncer request writes.lookup
      writes.rename inodes runs files inode buffered write.nonempty write.returned write.physical lateEffects
  refine ⟨batch, table, guarded, poisoned, prepared, fits, guard, assigned, ?_⟩
  rcases classified with early | ⟨grouped, groupReturned, _, _, _, publication⟩
  · exact .inl early
  refine .inr ⟨grouped, groupReturned, ?_⟩
  intro rebooted reboot reset
  have fileFrame := fileFrames.throughPublication CheckpointStorageObservation.Frames.trans prepared guard assigned source
  have nameFrame := nameEffects.throughPublication WalNamePresenceFrame.trans prepared guard assigned source
  obtain ⟨target, handoff⟩ :=
    last.selectsDurableReachedWrite view storage prepared fits write.physical fileFrame publication visible reboot
      reset nameFrame write.window
  obtain ⟨plan, opens⟩ := handoff.sampledPlan
  refine ⟨target, plan, handoff,
    (congrArg (fun target : Target => target.range.through) plan.targetEq).symm.trans plan.layout.through, ?_, ?_, ?_, @opens⟩
  · simpa only [← through.history] using plan.allowed
  · simpa only [← through.submissions, ← through.reads] using plan.pending
  · simpa only [← through.reads] using plan.bounded

end Alvoki.Storage.DiskSession
