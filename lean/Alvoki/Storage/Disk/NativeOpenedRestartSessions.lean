import Alvoki.Storage.Disk.NativeQuietPowerLossTableOpen
import Alvoki.Storage.Disk.NativeOpenedAlignedCloseReport
import Alvoki.Storage.Disk.NativeOpenedFailedCloseReport
import Alvoki.Storage.Disk.NativeOpenedFinalizedRetryReport
import Alvoki.Storage.Disk.NativeOpenedManifestRenameReport
import Alvoki.Storage.Disk.NativeOpenedStoppedCheckpointReport
import Alvoki.Storage.Disk.NativeOpenedEarlyCheckpointReport
import Alvoki.Storage.Disk.Proofs.Write.NativeOpenedUncertainWriteReport
import Alvoki.Storage.Disk.Proofs.Write.NativeUncertainWriteExitTableOpen
import Alvoki.Storage.Disk.NativeOpenedStoppedMarkerReport
import Alvoki.Storage.Disk.Proofs.Append.NativeOpenedFirstAppendReport
import Alvoki.Storage.Disk.Proofs.Append.NativeStoppedFirstAppendExitTableOpen
import Alvoki.Storage.Disk.NativeRawContendedAliasOpen
import Alvoki.Storage.Disk.NativeOpenedStoppedObsoleteRunReport
import Alvoki.Storage.Disk.NativeOpenedProcessExitReport

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- Concatenate finite executions at their exact shared position. -/
theorem NativeExecutionTrace.append
    (first : NativeExecutionTrace start earlier middle) (second : NativeExecutionTrace middle later last) :
    NativeExecutionTrace start (earlier ++ later) last := by
  induction second with
  | empty => simpa using first
  | step _ next joined =>
    simpa only [List.append_assoc] using NativeExecutionTrace.step joined next

variable {heap : Type}

/-- A position can move to a newly opened handle across sessions. -/
structure NativeOpenedSessionPoint (heap : Type) where
  handle : NativeOpenedHandle heap
  position : NativeOpenedPosition handle

variable {view : OpenCloseHeapView heap FileImage}
  {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray}
  {input : FilePath} {before : NativeOpenedSessionPoint heap}

/-- One reported quiet restart from the actual preceding position.
All raw reports use one selected survivor and one post-reboot heap. -/
structure NativeQuietRestartReport (before : NativeOpenedSessionPoint heap) (input : FilePath)
    (view : OpenCloseHeapView heap FileImage) (names : heap → FilePath → Option Nat) (bytes : heap → Nat → ByteArray) where
  crash : NativeReadyQuietCrash before.position.current.ready.state
  layout : CanonicalKeeperLayout crash.retry.image before.position.current.ready.state.writer.history
  target : layout.target = before.position.current.ready.state.writer.target
  keeper : layout.keeper = before.position.current.ready.state.writer.wal.active
  descriptors : layout.sealed ++ [layout.keeper] =
    before.position.current.ready.state.writer.wal.readDescriptors layout.range.watermark
  offsets : selectWalSegmentReads (before.position.current.ready.state.writer.wal.segments.map WalSegment.first)
    layout.range.watermark = some (layout.first,
      (before.position.current.ready.state.writer.wal.readDescriptors layout.range.watermark).map WalSegment.first)
  prepared : Prepared crash.retry.image layout.target layout.plan
  selected : SelectedIntegrityCheckpoint before.position.current.ready.state.writer.published.durable
    crash.retry.image.directory.active.manifest before.position.current.ready.state.writer.checkpoint
  reader : NativeReadyRestartReads crash input layout selected
  afterReboot : heap
  stream : Type
  admission : RawOpenAdmissionCallbacks heap
  init : OpenSyncCacheCallbacks heap
  phaseIdentity : IO.Ref (Phase Installed) → Nat
  tokenIdentity : IO.Ref Unit → Nat
  allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))
  allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)
  observed : RawQuietRestartEffects reader view admission init names bytes before.position.reached afterReboot
    phaseIdentity tokenIdentity allocatePhase allocateToken stream
  remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)
  write : FilePath → ByteArray → EStateM IO.Error heap Unit
  rename : FilePath → FilePath → EStateM IO.Error heap Unit
  bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened
  assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles →
    IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable
  constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files)
  get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)
  set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit
  phaseEffects : OpenPhaseCellEffects view.phase get set
  ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool

/-- The following position belongs to the exact table returned by this
restart. Retain the source cache initializer and the physical state of
that same raw open alongside the client event. -/
structure NativeQuietRestartReport.Returned (seen : NativeQuietRestartReport before input view names bytes)
    (next : NativeOpenedSessionPoint heap) : Prop where
  common : NativeExecutionStep before.position.current (.readOrRestart (.restart input)) next.position.current
  emptyCensus : (view.descriptors seen.afterReboot).slots = []
  source : ∃ (cacheOpen : IO DiskTable.OpenSyncFiles)
    (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles),
    let directory := before.position.current.ready.state.session.directory
    DiskTable.OpenSyncFiles.IsOpenAction directory.path cacheOpen ∧
    cacheOpen = openSyncFilesWith (m := IO) (IO.FS.Handle.mk directory.path .read)
      (fun value => liftM (IO.mkRef value)) (fun value => liftM (IO.mkRef value))
      (fun value => liftM (IO.mkRef value)) makeCache ∧
    seen.observed.openTable seen.remove seen.write seen.rename seen.bootstrap seen.assemble makeCache =
      .ok next.handle.table next.position.reached
  reader : seen.reader.run = next.position.current.ready.opened
  replay : seen.reader.ReachedSession next.position.current.ready.state before.position.current.history
    before.position.current.submissions before.position.current.ready.reads
  lock : next.handle.lock = seen.observed.admission.raw.lock
  cache : next.handle.files.UsesCacheReferences seen.observed.admission.seed.activeRef
    seen.observed.admission.seed.pendingRef seen.observed.admission.seed.directoryRef
  contents : next.handle.contents = view.phase
  get : next.handle.get = seen.get
  set : next.handle.set = seen.set
  ptrEq : next.handle.ptrEq = seen.ptrEq
  unpinned : next.position.pins = []
  files : view.files next.position.reached = next.position.current.ready.state.files
  census : view.descriptors next.position.reached = next.position.current.ready.state.census
  cached : view.cacheAt next.position.reached seen.observed.admission.seed.directoryRef
    seen.observed.admission.seed.activeRef seen.observed.admission.seed.pendingRef = next.position.current.ready.state.cache

/-- Derive the exact raw restart return without assuming the next table
or its replay. The empty within-session prefix starts at this call. -/
theorem NativeQuietRestartReport.reaches (seen : NativeQuietRestartReport before input view names bytes) :
    ∃ next, seen.Returned next := by
  let current := before.position.current.ready
  obtain ⟨next, step, sameReads, sameReader, replay⟩ :=
    current.restartsAtReader seen.reader seen.target seen.keeper seen.descriptors seen.offsets seen.prepared
  obtain ⟨valid, history, _⟩ := current.readPrefix.refines
  obtain ⟨installed⟩ := seen.observed.toRawAlignedCheckpointReopenEffects.installsQuietSelectionAt
    valid history seen.target seen.keeper seen.descriptors seen.offsets seen.prepared next sameReader.symm
    (sameReads.symm ▸ replay) seen.remove seen.write seen.rename seen.bootstrap seen.assemble
    seen.constructs seen.phaseEffects seen.ptrEq
  refine ⟨⟨installed.handle, installed.start⟩, ?_, ?_,
    ⟨installed.cacheOpen, installed.makeCache, installed.cacheAction, installed.cacheSource, installed.rawOpen⟩,
    ?_, ?_, installed.lock, installed.references, installed.contents, installed.readsPhase, installed.writesPhase,
    installed.comparesTokens, installed.pins, ?_, ?_, ?_⟩
  · change NativeExecutionStep before.position.current _ installed.start.current
    rw [installed.position]
    exact .readOrRestart before.position.current step
  · rw [seen.observed.admission.raw.entryCensus]
    rfl
  · dsimp only
    rw [installed.position]
    exact sameReader.symm
  · dsimp only
    rw [installed.position]
    exact replay
  · dsimp only
    rw [installed.position]
    exact installed.files
  · dsimp only
    rw [installed.position]
    exact installed.census
  · dsimp only
    rw [installed.position]
    exact installed.cache

inductive NativeOpenedSessionAction : Type 1 where
  | calls (instructions : List NativeOpenedInstruction)
  | quietRestart (input : FilePath)
  | processExitAndReopen (input : FilePath)
  | closeAndReopen (input : FilePath)
  | closeRetriesAndReopen (inputs : List FilePath) (input : FilePath)
  | checkpointRenameReboot (input : FilePath)
  | stoppedCheckpointReboot (input : FilePath)
  | stoppedCheckpointEarlyReboot (stage : CheckpointPublication.Step) (input : FilePath)
  | uncertainWriteReboot (request : WriteRequest) (input : FilePath)
  | uncertainWriteExitAndReopen (request : WriteRequest) (input : FilePath)
  | stoppedWalWriteReboot (request : WriteRequest) (input : FilePath)
  | stoppedFirstAppendExit (request : WriteRequest) (input : FilePath)
  | stoppedFirstAppendExitRetries (request : WriteRequest) (inputs : List FilePath) (input : FilePath)
  | stoppedFirstAppendContendedRetries (request : WriteRequest) (contended : FilePath)
      (inputs : List FilePath) (input : FilePath)
  | stoppedObsoleteRunUnlink (held : List UInt64) (input : FilePath)

/-- Same-handle calls and the supported reopen routes compose at
the exact handle and ready position reached by the preceding segment. -/
inductive NativeOpenedSessionStep (view : OpenCloseHeapView heap FileImage)
    (names : heap → FilePath → Option Nat) (bytes : heap → Nat → ByteArray) (before : NativeOpenedSessionPoint heap) :
    NativeOpenedSessionAction → List NativeExecutionEvent → NativeOpenedSessionPoint heap → Prop where
  | calls {instructions : List NativeOpenedInstruction} {events : List NativeExecutionEvent}
      {next : NativeOpenedPosition before.handle} (ran : NativeOpenedTrace before.position instructions events next) :
      NativeOpenedSessionStep view names bytes before (.calls instructions) events ⟨before.handle, next⟩
  | quiet {input : FilePath} (seen : NativeQuietRestartReport before input view names bytes)
      {next : NativeOpenedSessionPoint heap} (returned : seen.Returned next) :
      NativeOpenedSessionStep view names bytes before (.quietRestart input) [.readOrRestart (.restart input)] next
  | processExit {input : FilePath} (seen : NativeOpenedProcessExitReport before.position input view names bytes)
      {next : NativeOpenedSessionPoint heap} (returned : seen.Returned next.position) :
      NativeOpenedSessionStep view names bytes before (.processExitAndReopen input)
        [.readyExitRecovered input before.position.current.ready.state.owner.reference.process] next
  | close {input : FilePath} (seen : NativeOpenedAlignedCloseReport before.position input view)
      {next : NativeOpenedSessionPoint heap} (returned : seen.Returned next.position) :
      NativeOpenedSessionStep view names bytes before (.closeAndReopen input) [.closedAndReopened input (.ok ())] next
  | closeAfterFailedUnlock {input : FilePath} (seen : NativeOpenedFailedCloseReport before.position input view)
      {next : NativeOpenedSessionPoint heap} (returned : seen.Returned next.position) :
      NativeOpenedSessionStep view names bytes before (.closeAndReopen input) [.closedAndReopened input (.error seen.cause)] next
  | closeRetries {inputs : List FilePath} {input : FilePath}
      (seen : NativeOpenedFinalizedRetryReport before.position inputs input view)
      {errors : List (FilePath × IO.Error)} {next : NativeOpenedSessionPoint heap}
      (returned : seen.Returned next.position errors) :
      NativeOpenedSessionStep view names bytes before (.closeRetriesAndReopen inputs input)
        [.rejectedOpenSequenceRecovered inputs input (errors.map Prod.snd)] next
  | checkpointRename {input : FilePath} (seen : NativeOpenedManifestRenameReport before.position input view names bytes)
      {next : NativeOpenedSessionPoint heap} (returned : seen.Returned next.position) :
      NativeOpenedSessionStep view names bytes before (.checkpointRenameReboot input) [seen.event] next
  | stoppedCheckpoint {input : FilePath} (seen : NativeOpenedStoppedCheckpointReport before.position input view names bytes)
      {next : NativeOpenedSessionPoint heap} (returned : seen.Returned next.position) :
      NativeOpenedSessionStep view names bytes before (.stoppedCheckpointReboot input) [seen.event] next
  | stoppedCheckpointEarly {input : FilePath}
      (seen : NativeOpenedEarlyCheckpointReport before.position input view names bytes)
      {next : NativeOpenedSessionPoint heap} (returned : seen.Returned next.position) :
      NativeOpenedSessionStep view names bytes before (.stoppedCheckpointEarlyReboot seen.recovery.stage input) [seen.event] next
  | uncertainWrite {request : WriteRequest} {input : FilePath}
      (seen : NativeOpenedUncertainWriteReport before.position request input view names bytes)
      {retained : List WAL.Write} {next : NativeOpenedSessionPoint heap} (returned : seen.Returned retained next.position) :
      NativeOpenedSessionStep view names bytes before (.uncertainWriteReboot request input) [seen.event retained] next
  | uncertainWriteExit {request : WriteRequest} {input : FilePath}
      (seen : NativeUncertainWriteExitTableOpen before.position request input view names bytes)
      {retained : List WAL.Write} {next : NativeOpenedSessionPoint heap} (returned : seen.Returned retained next.position) :
      NativeOpenedSessionStep view names bytes before (.uncertainWriteExitAndReopen request input) [seen.event retained] next
  | stoppedWalWrite {request : WriteRequest} {input : FilePath}
      (seen : NativeOpenedStoppedMarkerReport before.position request input view names bytes)
      {retained : List WAL.Write} {next : NativeOpenedSessionPoint heap} (returned : seen.Returned retained next.position) :
      NativeOpenedSessionStep view names bytes before (.stoppedWalWriteReboot request input) [seen.event retained] next
  | stoppedFirstAppend {request : WriteRequest} {input : FilePath}
      (seen : NativeOpenedFirstAppendReport before.position request input view names bytes)
      {next : NativeOpenedSessionPoint heap} (returned : seen.Returned next.position) :
      NativeOpenedSessionStep view names bytes before (.stoppedWalWriteReboot request input) [seen.event] next
  | stoppedFirstAppendExit {request : WriteRequest} {input : FilePath}
      (seen : NativeStoppedFirstAppendExitTableOpen before.position request input view names bytes)
      {next : NativeOpenedSessionPoint heap} (returned : seen.Returned next.position) :
      NativeOpenedSessionStep view names bytes before (.stoppedFirstAppendExit request input)
        [.interruptedAppendRecovered request input seen.prepared.batch] next
  | stoppedFirstAppendExitRetries {request : WriteRequest} {inputs : List FilePath} {input : FilePath}
      (seen : NativeStoppedAppendFinalizedRetry before.position request inputs input view names bytes)
      {next : NativeOpenedSessionPoint heap} (returned : seen.Returned next.position) :
      NativeOpenedSessionStep view names bytes before (.stoppedFirstAppendExitRetries request inputs input) [seen.event] next
  | stoppedFirstAppendContendedRetries {request : WriteRequest} {inputs : List FilePath} {input contended : FilePath}
      (seen : NativeStoppedAppendFinalizedRetry before.position request inputs input view names bytes)
      (attempt : RawContendedAliasOpen view seen.calls seen.release before.position.current.ready.state.session.directory
        before.position.current.ready.state.session.descriptor seen.stop.view seen.stop.root contended seen.rawExit.afterExit)
      (busy : seen.rawExit.ContendedReturn attempt)
      {next : NativeOpenedSessionPoint heap} (returned : seen.Returned next.position (some (contended, attempt.diagnostic))) :
      NativeOpenedSessionStep view names bytes before (.stoppedFirstAppendContendedRetries request contended inputs input)
        [seen.event (some (contended, attempt.diagnostic))] next
  | stoppedObsoleteRunUnlink {held : List UInt64} {input : FilePath}
      (seen : NativeOpenedStoppedObsoleteRunReport before.position held input view names bytes)
      {next : NativeOpenedSessionPoint heap} (returned : seen.Returned next.position) :
      NativeOpenedSessionStep view names bytes before (.stoppedObsoleteRunUnlink held input)
        [.interruptedRunUnlinkRecovered held input] next

/-- Derive the ledger update at the actual reached session boundary. -/
theorem NativeOpenedSessionStep.ledgerSuffix
    (step : NativeOpenedSessionStep view names bytes before action added after) :
    before.position.current.LedgerSuffix added after.position.current := by
  cases step with
  | calls ran => exact ran.common.ledgerSuffix
  | quiet _ returned => exact returned.common.ledgerSuffix
  | processExit _ returned => exact returned.common.ledgerSuffix
  | close _ returned => exact returned.common.ledgerSuffix
  | closeAfterFailedUnlock _ returned => exact returned.common.ledgerSuffix
  | closeRetries _ returned => exact returned.common.ledgerSuffix
  | checkpointRename _ returned => exact returned.ledgerSuffix
  | stoppedCheckpoint _ returned => exact returned.common.ledgerSuffix
  | stoppedCheckpointEarly _ returned => exact returned.common.ledgerSuffix
  | uncertainWrite _ returned => exact returned.common.ledgerSuffix
  | uncertainWriteExit _ returned => exact returned.common.ledgerSuffix
  | stoppedWalWrite _ returned => exact returned.common.ledgerSuffix
  | stoppedFirstAppend _ returned => exact returned.common.ledgerSuffix
  | stoppedFirstAppendExit _ returned => exact returned.common.ledgerSuffix
  | stoppedFirstAppendExitRetries _ returned => exact returned.common.ledgerSuffix
  | stoppedFirstAppendContendedRetries _ _ _ returned => exact returned.common.ledgerSuffix
  | stoppedObsoleteRunUnlink _ returned => exact returned.common.ledgerSuffix

inductive NativeOpenedSessionTrace (view : OpenCloseHeapView heap FileImage)
    (names : heap → FilePath → Option Nat) (bytes : heap → Nat → ByteArray) (start : NativeOpenedSessionPoint heap) :
    List NativeOpenedSessionAction → List NativeExecutionEvent → NativeOpenedSessionPoint heap → Prop where
  | empty : NativeOpenedSessionTrace view names bytes start [] [] start
  | step {before after : NativeOpenedSessionPoint heap}
      (prior : NativeOpenedSessionTrace view names bytes start actions events before)
      (next : NativeOpenedSessionStep view names bytes before action added after) :
      NativeOpenedSessionTrace view names bytes start (actions ++ [action]) (events ++ added) after

/-- Compose the local ledger updates along successive reached sessions. -/
theorem NativeOpenedSessionTrace.ledgerSuffix
    (trace : NativeOpenedSessionTrace view names bytes start actions events last) :
    start.position.current.LedgerSuffix events last.position.current := by
  induction trace with
  | empty => exact .empty _
  | step _ next earlier => exact earlier.append next.ledgerSuffix

/-- The common ledger spans the same exact ready positions as the raw
session trace, including every covered reopen. -/
theorem NativeOpenedSessionTrace.common (trace : NativeOpenedSessionTrace view names bytes start actions events last) :
    NativeExecutionTrace start.position.current events last.position.current := by
  induction trace with
  | empty => exact .empty
  | step _ next prior =>
    cases next with
    | calls ran => exact prior.append ran.common
    | quiet _ returned => exact .step prior returned.common
    | processExit _ returned => exact .step prior returned.common
    | close _ returned => exact .step prior returned.common
    | closeAfterFailedUnlock _ returned => exact .step prior returned.common
    | closeRetries _ returned => exact .step prior returned.common
    | checkpointRename _ returned => exact .step prior returned.common
    | stoppedCheckpoint _ returned => exact .step prior returned.common
    | stoppedCheckpointEarly _ returned => exact .step prior returned.common
    | uncertainWrite _ returned => exact .step prior returned.common
    | uncertainWriteExit _ returned => exact .step prior returned.common
    | stoppedWalWrite _ returned => exact .step prior returned.common
    | stoppedFirstAppend _ returned => exact .step prior returned.common
    | stoppedFirstAppendExit _ returned => exact .step prior returned.common
    | stoppedFirstAppendExitRetries _ returned => exact .step prior returned.common
    | stoppedFirstAppendContendedRetries _ _ _ returned => exact .step prior returned.common
    | stoppedObsoleteRunUnlink _ returned => exact .step prior returned.common

/-- A report for the next prescribed block of calls or reopen. -/
inductive NativeOpenedSessionReport (view : OpenCloseHeapView heap FileImage)
    (names : heap → FilePath → Option Nat) (bytes : heap → Nat → ByteArray)
    (before : NativeOpenedSessionPoint heap) : NativeOpenedSessionAction → Type 1 where
  | calls (instructions : List NativeOpenedInstruction) (reports : NativeOpenedTrace.Reports before.position instructions) :
      NativeOpenedSessionReport view names bytes before (.calls instructions)
  | quiet (input : FilePath) (report : NativeQuietRestartReport before input view names bytes) :
      NativeOpenedSessionReport view names bytes before (.quietRestart input)
  | processExit (input : FilePath) (report : NativeOpenedProcessExitReport before.position input view names bytes) :
      NativeOpenedSessionReport view names bytes before (.processExitAndReopen input)
  | close (input : FilePath) (report : NativeOpenedAlignedCloseReport before.position input view) :
      NativeOpenedSessionReport view names bytes before (.closeAndReopen input)
  | closeAfterFailedUnlock (input : FilePath) (report : NativeOpenedFailedCloseReport before.position input view) :
      NativeOpenedSessionReport view names bytes before (.closeAndReopen input)
  | closeRetries (inputs : List FilePath) (input : FilePath)
      (report : NativeOpenedFinalizedRetryReport before.position inputs input view) :
      NativeOpenedSessionReport view names bytes before (.closeRetriesAndReopen inputs input)
  | checkpointRename (input : FilePath) (report : NativeOpenedManifestRenameReport before.position input view names bytes) :
      NativeOpenedSessionReport view names bytes before (.checkpointRenameReboot input)
  | stoppedCheckpoint (input : FilePath) (report : NativeOpenedStoppedCheckpointReport before.position input view names bytes) :
      NativeOpenedSessionReport view names bytes before (.stoppedCheckpointReboot input)
  | stoppedCheckpointEarly (input : FilePath)
      (report : NativeOpenedEarlyCheckpointReport before.position input view names bytes) :
      NativeOpenedSessionReport view names bytes before (.stoppedCheckpointEarlyReboot report.recovery.stage input)
  | uncertainWrite (request : WriteRequest) (input : FilePath)
      (report : NativeOpenedUncertainWriteReport before.position request input view names bytes) :
      NativeOpenedSessionReport view names bytes before (.uncertainWriteReboot request input)
  | uncertainWriteExit (request : WriteRequest) (input : FilePath)
      (report : NativeUncertainWriteExitTableOpen before.position request input view names bytes) :
      NativeOpenedSessionReport view names bytes before (.uncertainWriteExitAndReopen request input)
  | stoppedWalWrite (request : WriteRequest) (input : FilePath)
      (report : NativeOpenedStoppedMarkerReport before.position request input view names bytes) :
      NativeOpenedSessionReport view names bytes before (.stoppedWalWriteReboot request input)
  | stoppedFirstAppend (request : WriteRequest) (input : FilePath)
      (report : NativeOpenedFirstAppendReport before.position request input view names bytes) :
      NativeOpenedSessionReport view names bytes before (.stoppedWalWriteReboot request input)
  | stoppedFirstAppendExit (request : WriteRequest) (input : FilePath)
      (report : NativeStoppedFirstAppendExitTableOpen before.position request input view names bytes) :
      NativeOpenedSessionReport view names bytes before (.stoppedFirstAppendExit request input)
  | stoppedFirstAppendExitRetries (request : WriteRequest) (inputs : List FilePath) (input : FilePath)
      (report : NativeStoppedAppendFinalizedRetry before.position request inputs input view names bytes) :
      NativeOpenedSessionReport view names bytes before (.stoppedFirstAppendExitRetries request inputs input)
  | stoppedFirstAppendContendedRetries (request : WriteRequest) (contended : FilePath) (inputs : List FilePath) (input : FilePath)
      (report : NativeStoppedAppendFinalizedRetry before.position request inputs input view names bytes)
      (attempt : RawContendedAliasOpen view report.calls report.release before.position.current.ready.state.session.directory
        before.position.current.ready.state.session.descriptor report.stop.view report.stop.root contended report.rawExit.afterExit) :
      NativeOpenedSessionReport view names bytes before (.stoppedFirstAppendContendedRetries request contended inputs input)
  | stoppedObsoleteRunUnlink (held : List UInt64) (input : FilePath)
      (report : NativeOpenedStoppedObsoleteRunReport before.position held input view names bytes) :
      NativeOpenedSessionReport view names bytes before (.stoppedObsoleteRunUnlink held input)

theorem NativeOpenedSessionReport.reaches (report : NativeOpenedSessionReport view names bytes before action) :
    ∃ events next, NativeOpenedSessionStep view names bytes before action events next := by
  cases report with
  | calls instructions reports =>
    obtain ⟨events, next, ran, _, _⟩ := NativeOpenedTrace.executes before.position instructions reports
    exact ⟨events, ⟨before.handle, next⟩, .calls ran⟩
  | quiet input seen =>
    obtain ⟨next, returned⟩ := seen.reaches
    exact ⟨_, next, .quiet seen returned⟩
  | processExit input seen =>
    obtain ⟨handle, start, returned⟩ := seen.reaches
    exact ⟨_, ⟨handle, start⟩, .processExit seen returned⟩
  | close input seen =>
    obtain ⟨handle, start, returned⟩ := seen.reaches
    exact ⟨_, ⟨handle, start⟩, .close seen returned⟩
  | closeAfterFailedUnlock input seen =>
    obtain ⟨handle, start, returned⟩ := seen.reaches
    exact ⟨_, ⟨handle, start⟩, .closeAfterFailedUnlock seen returned⟩
  | closeRetries _ _ seen =>
    obtain ⟨handle, start, _, returned⟩ := seen.reaches
    exact ⟨_, ⟨handle, start⟩, .closeRetries seen returned⟩
  | checkpointRename input seen =>
    obtain ⟨handle, start, returned⟩ := seen.reaches
    exact ⟨_, ⟨handle, start⟩, .checkpointRename seen returned⟩
  | stoppedCheckpoint input seen =>
    obtain ⟨handle, start, returned⟩ := seen.reaches
    exact ⟨_, ⟨handle, start⟩, .stoppedCheckpoint seen returned⟩
  | stoppedCheckpointEarly input seen =>
    obtain ⟨handle, start, returned⟩ := seen.reaches
    exact ⟨_, ⟨handle, start⟩, .stoppedCheckpointEarly seen returned⟩
  | uncertainWrite request input seen =>
    obtain ⟨_, handle, start, returned⟩ := seen.reaches
    exact ⟨_, ⟨handle, start⟩, .uncertainWrite seen returned⟩
  | uncertainWriteExit request input seen =>
    obtain ⟨_, handle, start, returned⟩ := seen.reaches
    exact ⟨_, ⟨handle, start⟩, .uncertainWriteExit seen returned⟩
  | stoppedWalWrite request input seen =>
    obtain ⟨_, handle, start, returned⟩ := seen.reaches
    exact ⟨_, ⟨handle, start⟩, .stoppedWalWrite seen returned⟩
  | stoppedFirstAppend request input seen =>
    obtain ⟨handle, start, returned⟩ := seen.reaches
    exact ⟨_, ⟨handle, start⟩, .stoppedFirstAppend seen returned⟩
  | stoppedFirstAppendExit request input seen =>
    obtain ⟨handle, start, returned⟩ := seen.reaches
    exact ⟨_, ⟨handle, start⟩, .stoppedFirstAppendExit seen returned⟩
  | stoppedFirstAppendExitRetries request inputs input seen =>
    obtain ⟨handle, start, returned⟩ := seen.reaches
    exact ⟨_, ⟨handle, start⟩, .stoppedFirstAppendExitRetries seen returned⟩
  | stoppedFirstAppendContendedRetries _ _ _ _ seen attempt =>
    obtain ⟨busy, handle, start, returned⟩ := seen.recordsContendedRetry attempt
    exact ⟨_, ⟨handle, start⟩, .stoppedFirstAppendContendedRetries seen attempt busy returned⟩
  | stoppedObsoleteRunUnlink held input seen =>
    obtain ⟨handle, start, returned⟩ := seen.reaches
    exact ⟨_, ⟨handle, start⟩, .stoppedObsoleteRunUnlink seen returned⟩

/-- Obtain the next local report only at the reached position of this
prescribed prefix. Each reopen can reach a new handle. Quiet restarts
and process exits use the same filesystem view. -/
def NativeOpenedSessionTrace.Reports (view : OpenCloseHeapView heap FileImage)
    (names : heap → FilePath → Option Nat) (bytes : heap → Nat → ByteArray)
    (start : NativeOpenedSessionPoint heap) (actions : List NativeOpenedSessionAction) : Prop :=
  ∀ completed events reached action remaining,
    actions = completed ++ action :: remaining →
    NativeOpenedSessionTrace view names bytes start completed events reached →
    Nonempty (NativeOpenedSessionReport view names bytes reached action)

/-- Execute finite interleavings of ready calls and the supported
aligned reopens. One replay explains the recorded responses and final table. -/
theorem NativeOpenedSessionTrace.executes (start : NativeOpenedSessionPoint heap) (actions : List NativeOpenedSessionAction)
    (reports : Reports view names bytes start actions) :
    ∃ events next, NativeOpenedSessionTrace view names bytes start actions events next ∧
      start.position.current.LedgerSuffix events next.position.current ∧
      InstalledClientReplay next.position.current.submissions next.position.current.ready.reads next.position.current.history
        next.position.current.ready.state.writer.installed next.position.current.ready.state.session := by
  have finish (remaining : List NativeOpenedSessionAction) : ∀ completed events reached,
      actions = completed ++ remaining → NativeOpenedSessionTrace view names bytes start completed events reached →
      ∃ events next, NativeOpenedSessionTrace view names bytes start actions events next := by
    induction remaining with
    | nil =>
      intro completed events reached ordered ran
      exact ⟨events, reached, by simpa only [ordered, List.append_nil] using ran⟩
    | cons action remaining earlier =>
      intro completed events reached ordered ran
      obtain ⟨report⟩ := reports completed events reached action remaining ordered ran
      obtain ⟨added, next, step⟩ := report.reaches
      have follows : actions = (completed ++ [action]) ++ remaining := by
        simpa only [List.append_assoc, List.singleton_append] using ordered
      exact earlier (completed ++ [action]) (events ++ added) next follows (.step ran step)
  obtain ⟨events, next, ran⟩ := finish actions [] [] start (by simp) .empty
  exact ⟨events, next, ran, ran.ledgerSuffix, next.position.current.ready.readPrefix.guardedReplay⟩

end Alvoki.Storage.DiskSession
