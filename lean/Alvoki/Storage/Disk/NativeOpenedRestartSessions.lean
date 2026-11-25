import Alvoki.Storage.Disk.NativeQuietPowerLossTableOpen
import Alvoki.Storage.Disk.NativeOpenedAlignedCloseReport
import Alvoki.Storage.Disk.NativeOpenedFailedCloseReport
import Alvoki.Storage.Disk.NativeOpenedManifestRenameReport
import Alvoki.Storage.Disk.NativeOpenedStoppedCheckpointReport
import Alvoki.Storage.Disk.NativeOpenedUncertainWriteReport
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
  have prior : NativeOpenedTrace before.position [] [] before.position := .empty
  obtain ⟨_, empty, next, cacheOpen, makeCache, handle, start, source, initializer, reads, reader, _, step,
    _, returned, reached, lock, cache, _, contents, get, set, ptrEq, pins, files, census, cached⟩ :=
    prior.restartsThenOpensAligned seen.crash seen.target seen.keeper seen.descriptors seen.offsets seen.prepared
      seen.observed seen.remove seen.write seen.rename seen.bootstrap seen.assemble seen.constructs seen.phaseEffects seen.ptrEq
  refine ⟨⟨handle, start⟩, ?_, empty, ⟨cacheOpen, makeCache, source, initializer, returned⟩,
    ?_, ?_, lock, cache, contents, get, set, ptrEq, pins, ?_, ?_, ?_⟩
  · change NativeExecutionStep before.position.current _ start.current
    rw [reached]
    exact .readOrRestart before.position.current step
  · change seen.reader.run = start.current.ready.opened
    rw [reached]
    exact reader
  · change seen.reader.ReachedSession start.current.ready.state _ _ _
    rw [reached]
    exact reads
  · change view.files start.reached = start.current.ready.state.files
    rw [reached]
    exact files
  · change view.descriptors start.reached = start.current.ready.state.census
    rw [reached]
    exact census
  · change view.cacheAt start.reached seen.observed.admission.seed.directoryRef
      seen.observed.admission.seed.activeRef seen.observed.admission.seed.pendingRef = start.current.ready.state.cache
    rw [reached]
    exact cached

inductive NativeOpenedSessionAction : Type 1 where
  | calls (instructions : List NativeOpenedInstruction)
  | quietRestart (input : FilePath)
  | processExitAndReopen (input : FilePath)
  | closeAndReopen (input : FilePath)
  | checkpointRenameReboot (input : FilePath)
  | stoppedCheckpointReboot (input : FilePath)
  | uncertainWriteReboot (request : WriteRequest) (input : FilePath)

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
  | checkpointRename {input : FilePath} (seen : NativeOpenedManifestRenameReport before.position input view names bytes)
      {next : NativeOpenedSessionPoint heap} (returned : seen.Returned next.position) :
      NativeOpenedSessionStep view names bytes before (.checkpointRenameReboot input) [seen.event] next
  | stoppedCheckpoint {input : FilePath} (seen : NativeOpenedStoppedCheckpointReport before.position input view names bytes)
      {next : NativeOpenedSessionPoint heap} (returned : seen.Returned next.position) :
      NativeOpenedSessionStep view names bytes before (.stoppedCheckpointReboot input) [seen.event] next
  | uncertainWrite {request : WriteRequest} {input : FilePath}
      (seen : NativeOpenedUncertainWriteReport before.position request input view names bytes)
      {retained : List WAL.Write} {next : NativeOpenedSessionPoint heap} (returned : seen.Returned retained next.position) :
      NativeOpenedSessionStep view names bytes before (.uncertainWriteReboot request input) [seen.event retained] next

inductive NativeOpenedSessionTrace (view : OpenCloseHeapView heap FileImage)
    (names : heap → FilePath → Option Nat) (bytes : heap → Nat → ByteArray) (start : NativeOpenedSessionPoint heap) :
    List NativeOpenedSessionAction → List NativeExecutionEvent → NativeOpenedSessionPoint heap → Prop where
  | empty : NativeOpenedSessionTrace view names bytes start [] [] start
  | step {before after : NativeOpenedSessionPoint heap}
      (prior : NativeOpenedSessionTrace view names bytes start actions events before)
      (next : NativeOpenedSessionStep view names bytes before action added after) :
      NativeOpenedSessionTrace view names bytes start (actions ++ [action]) (events ++ added) after

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
    | checkpointRename _ returned => exact .step prior returned.common
    | stoppedCheckpoint _ returned => exact .step prior returned.common
    | uncertainWrite _ returned => exact .step prior returned.common

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
  | checkpointRename (input : FilePath) (report : NativeOpenedManifestRenameReport before.position input view names bytes) :
      NativeOpenedSessionReport view names bytes before (.checkpointRenameReboot input)
  | stoppedCheckpoint (input : FilePath) (report : NativeOpenedStoppedCheckpointReport before.position input view names bytes) :
      NativeOpenedSessionReport view names bytes before (.stoppedCheckpointReboot input)
  | uncertainWrite (request : WriteRequest) (input : FilePath)
      (report : NativeOpenedUncertainWriteReport before.position request input view names bytes) :
      NativeOpenedSessionReport view names bytes before (.uncertainWriteReboot request input)

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
  | checkpointRename input seen =>
    obtain ⟨handle, start, returned⟩ := seen.reaches
    exact ⟨_, ⟨handle, start⟩, .checkpointRename seen returned⟩
  | stoppedCheckpoint input seen =>
    obtain ⟨handle, start, returned⟩ := seen.reaches
    exact ⟨_, ⟨handle, start⟩, .stoppedCheckpoint seen returned⟩
  | uncertainWrite request input seen =>
    obtain ⟨_, handle, start, returned⟩ := seen.reaches
    exact ⟨_, ⟨handle, start⟩, .uncertainWrite seen returned⟩

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
      NativeExecutionTrace start.position.current events next.position.current ∧
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
  exact ⟨events, next, ran, ran.common, ran.common.keyValueRefinement.2.2.2⟩

end Alvoki.Storage.DiskSession
