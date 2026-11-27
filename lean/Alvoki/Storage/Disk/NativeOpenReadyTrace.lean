import Alvoki.Storage.Disk.NativeClassifiedCheckpointPreflight
import Alvoki.Storage.Disk.NativeClassifiedCheckpointSuccess
import Alvoki.Storage.Disk.Proofs.Rotation.NativeOpenRotation
import Alvoki.Storage.Disk.NativeClassifiedWritePreflight
import Alvoki.Storage.Disk.NativeClassifiedWriteAck
import Alvoki.Storage.Disk.NativeOpenSnapshotControls
import Alvoki.Storage.Disk.NativeOpenRunMaintenance
import Alvoki.Storage.Disk.NativeOpenExternalPinRead
import Alvoki.Storage.Disk.NativeOpenedWalPlanning
import Alvoki.Storage.Disk.Proofs.Collection.NativeOpenedWalCollection
import Alvoki.Storage.Disk.Proofs.Collection.NativeOpenObsoleteRunCollection

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair
open Sequential (SnapshotPin)

variable {heap : Type} {opened : NativeOpenedHandle heap}

/-- The source's opaque pin constructor carries the public acquisition's
original token, handle and sequence. -/
def NativeOpenedHandle.LatestIssuer {heap : Type} (opened : NativeOpenedHandle heap) :=
  { issue : SnapshotPin → DiskSnapshotPin //
    (∀ pin, (issue pin).UsesOpenToken opened.token pin) ∧
    opened.table.acquire = acquireLatestWith (m := IO) (do (← opened.phase.get).installed)
      (acquireSnapshotWith (do (← opened.phase.get).installed) opened.phase.set issue) }

theorem NativeOpenedHandle.hasLatestIssuer (opened : NativeOpenedHandle heap) :
    Nonempty opened.LatestIssuer := by
  obtain ⟨issue, owns, _, source⟩ := opened.uses.snapshotAcquisitions
  exact ⟨⟨issue, owns, source⟩⟩

abbrev NativeOpenedHandle.acquireLatestRaw {heap : Type} (opened : NativeOpenedHandle heap)
    (issue : SnapshotPin → DiskSnapshotPin) : EStateM IO.Error heap DiskSnapshotPin :=
  let load : EStateM IO.Error heap Installed := do (← opened.get opened.phase).installed
  acquireLatestWith load (acquireSnapshotWith load (opened.set opened.phase) issue)

inductive NativeOpenedInstruction : Type 1 where
  | write (request : WriteRequest)
  | checkpoint
  | rotateWal
  | rewriteRun (request : RunMaintenance)
  | acquireAt (sequence : UInt64)
  | releaseAt (index : Nat)
  | advanceFloor (floor : UInt64)
  | readAt (index : Nat) (request : SnapshotReadRequest α)
  | readSupplied (pin : DiskSnapshotPin) (request : SnapshotReadRequest α)
  | releaseSupplied (pin : DiskSnapshotPin)
  | acquire
  | planWalCollection
  | collectObsoleteRuns (held : List UInt64)
  | collectCoveredWal

/-- Per-call observations at the reached position. Indexed operands
select tracked pins. A supplied pin retains its original issuer, and
the reached table's registry decides whether a local handle is active. -/
inductive NativeOpenedReport (start : NativeOpenedPosition opened) : NativeOpenedInstruction → Type 1 where
  | write (request : WriteRequest) (nonempty : request.rows ≠ [])
      (calls : WriteRequest.Calls (DescriptorInventory × DescriptorSlot × Nat))
      (cache : calls.cache = start.current.ready.state.cache)
      (observe : ∀ checked : CheckedWriteRequest request start.current.ready.state.session.directory
          start.current.ready.state.writer.installed calls.lookup,
        Nonempty (WriteCallPublication calls checked))
      {sequence : UInt64} {returnedHeap : heap} {reached : OpenWriteFiles}
      (actual : request.runOnOpenPhase start.current.ready.state.session.directory calls opened.phase opened.get opened.set
        (start.reached, (WriteRequest.readyCall start.current.ready.state.writer start.current.ready.state.cache).2.image) =
          .ok sequence (returnedHeap, reached))
      (custody : NativePendingWriteCensus start.current.ready.state reached.1) :
      NativeOpenedReport start (.write request)
  | writePreflight (request : WriteRequest) (calls : WriteRequest.Calls (DescriptorInventory × DescriptorSlot × Nat))
      (cache : calls.cache = start.current.ready.state.cache)
      (preflight : calls.ReturnsPreflight request start.current.ready.state) :
      NativeOpenedReport start (.write request)
  | checkpoint {image : Type}
      {attempt : SegmentedCheckpointReport start.current.ready.state.session.directory start.current.ready.state.writer}
      {reports : CheckpointCompletionReports (CensusDirectoryCache × image) attempt}
      (reported : NativeReadyCheckpoint start.current.ready.state reports)
      {reached : heap} {after : CensusDirectoryCache × image}
      (returned : runCheckpointOnOpenPhase (reported.primitives.cached.perform start.current.ready.state.session.directory)
        opened.phase opened.get opened.set (start.reached, start.current.ready.state.cache, (reports.observed.atRun 0).2) =
          .ok () (reached, after)) :
      NativeOpenedReport start .checkpoint
  | checkpointPreflight {image : Type}
      (calls : CheckpointPrimitiveCalls CheckpointOpenHandle image) (atEntry : image)
      {cause : IO.Error} {reached : heap} {after : CensusDirectoryCache × image}
      (returned : runCheckpointOnOpenPhase (calls.cached.perform start.current.ready.state.session.directory)
        opened.phase opened.get opened.set (start.reached, start.current.ready.state.cache, atEntry) =
          .error cause (reached, after))
      (stillReady : opened.contents reached opened.phase = some start.current.ready.state.session.phase) :
      NativeOpenedReport start .checkpoint
  | rotateCreated (report : NativeReadyCreatedRotation start.current.ready.state)
      (seen : OpenRotationObservation.Created start report) : NativeOpenedReport start .rotateWal
  | rotateExisting (report : NativeReadyExistingRotation start.current.ready.state)
      (seen : OpenRotationObservation.Existing start report) : NativeOpenedReport start .rotateWal
  | rotateEmpty (calls : OpenRotationCallbacks heap) (lookup : FilePath → Except IO.Error IO.FS.Metadata)
      {active pending directory} (references : opened.files.UsesCacheReferences active pending directory)
      (cachePath : opened.files.AtDirectory opened.directory.path)
      (empty : start.current.ready.state.writer.installed.walBytes / WAL.frameSize ≤
        start.current.ready.state.writer.installed.activeFirst) : NativeOpenedReport start .rotateWal
  | rewriteRun (request : RunMaintenance) :
      NativeOpenedReport start (.rewriteRun request)
  | acquireAt (sequence : UInt64) {pin : SnapshotPin} {table : PackedTable}
      (acquired : start.current.ready.state.writer.installed.table.acquireAt sequence = some (pin, table)) :
      NativeOpenedReport start (.acquireAt sequence)
  | acquireAtUnavailable (sequence : UInt64)
      (unavailable : start.current.ready.state.writer.installed.table.acquireAt sequence = none) :
      NativeOpenedReport start (.acquireAt sequence)
  | releaseAt (index : Nat) (pin : NativeOpenedPin opened)
      (issued : start.pins[index]? = some pin)
      (compared : opened.ptrEq opened.token opened.token start.reached = .ok true start.reached) :
      NativeOpenedReport start (.releaseAt index)
  | advanceFloor (floor : UInt64) :
      NativeOpenedReport start (.advanceFloor floor)
  | readAt (index : Nat) (request : SnapshotReadRequest α) (pin : NativeOpenedPin opened)
      (issued : start.pins[index]? = some pin)
      (compared : opened.ptrEq opened.token opened.token start.reached = .ok true start.reached) :
      NativeOpenedReport start (.readAt index request)
  | readSupplied (pin : DiskSnapshotPin) (request : SnapshotReadRequest α)
      {issuer : IO.Ref Unit} {issued : SnapshotPin} (owns : pin.UsesOpenToken issuer issued)
      (tokenIdentity : IO.Ref Unit → Nat)
      (currentToken : tokenIdentity opened.token = start.current.ready.state.session.sessionRef)
      (identifies : tokenIdentity issuer = tokenIdentity opened.token ↔ issuer = opened.token)
      (compared : opened.ptrEq issuer opened.token start.reached =
        .ok (decide (tokenIdentity issuer = tokenIdentity opened.token)) start.reached) :
      NativeOpenedReport start (.readSupplied pin request)
  | releaseSupplied (pin : DiskSnapshotPin)
      {issuer : IO.Ref Unit} {issued : SnapshotPin} (owns : pin.UsesOpenToken issuer issued)
      (tokenIdentity : IO.Ref Unit → Nat)
      (currentToken : tokenIdentity opened.token = start.current.ready.state.session.sessionRef)
      (identifies : tokenIdentity issuer = tokenIdentity opened.token ↔ issuer = opened.token)
      (compared : opened.ptrEq issuer opened.token start.reached =
        .ok (decide (tokenIdentity issuer = tokenIdentity opened.token)) start.reached) :
      NativeOpenedReport start (.releaseSupplied pin)
  | acquire : NativeOpenedReport start .acquire
  | planWalCollection (observed : NativeWalPlanningObservation start.current.ready.state) :
      NativeOpenedReport start .planWalCollection
  | collectObsoleteRuns (held : List UInt64)
      (observed : NativeObsoleteRunCollection start.current.ready.state)
      (seen : OpenObsoleteRunObservation start held observed.toNativeObsoleteRunPass) :
      NativeOpenedReport start (.collectObsoleteRuns held)
  | obsoleteRunBarrierError (held : List UInt64) (failed : NativeObsoleteRunBarrierError start.current.ready.state)
      (seen : OpenObsoleteRunObservation start held failed.toNativeObsoleteRunPass) :
      NativeOpenedReport start (.collectObsoleteRuns held)
  | collectCoveredWal (observed : NativeReadyWalCollection start.current.ready.state)
      (completed : observed.barrier.outcome = .completed) :
      NativeOpenedReport start .collectCoveredWal
  | rejectsCoveredWalPlan (observed : NativeWalPlanningObservation start.current.ready.state)
      (cause : IO.Error) (rejected : observed.extents.result = .error cause) :
      NativeOpenedReport start .collectCoveredWal

namespace NativeOpenedReport

variable {start : NativeOpenedPosition opened} {instruction : NativeOpenedInstruction}

/-- Each reported call retains its actual source schedule and the raw
return at this step's reached phase heap. The common edge certifies the
same returned writer, table, or read response. -/
def Returns (report : NativeOpenedReport start instruction) (event : NativeExecutionEvent)
    (next : NativeOpenedPosition opened) : Prop :=
  match report with
  | .write request _ calls _ _ (sequence := sequence) (reached := reached) _ custody =>
    let state := start.current.ready.state
    let before := WriteRequest.readyCall state.writer state.cache
    opened.table.UsesOpenWriteSchedules state.session.directory opened.files opened.phase ∧
    request.runOnOpenPhase state.session.directory calls opened.phase opened.get opened.set
      (start.reached, before.2.image) = .ok sequence (next.reached, reached) ∧
    ∃ ack : ClassifiedWriteAcknowledgement start.current.ready request calls sequence reached custody,
      next.current = ⟨start.current.history ++ ack.report.batch,
        start.current.submissions ++ [.acknowledgedBatch ack.report.batch], ack.next⟩ ∧
      event = .acknowledged request ack.report.batch ∧ next.pins = start.pins
  | .writePreflight request calls _ _ =>
    let state := start.current.ready.state
    let before := WriteRequest.readyCall state.writer state.cache
    opened.table.UsesOpenWriteSchedules state.session.directory opened.files opened.phase ∧
    ∃ seen : NativeWritePreflightObservation state request,
      seen.lookup = calls.lookup ∧
      calls.run request state.session.directory state.writer = seen.resultAt before ∧
      request.runOnOpenPhase state.session.directory calls opened.phase opened.get opened.set (start.reached, before.2.image) =
        seen.resultAt (next.reached, before.2.image) ∧
      event = .writePreflight request seen.response ∧ next = start
  | .checkpoint (reports := reports) reported _ =>
    opened.table.UsesOpenCheckpointSchedule start.current.ready.state.session.directory opened.files opened.phase ∧
    runCheckpointOnOpenPhase (reported.primitives.cached.perform start.current.ready.state.session.directory)
      opened.phase opened.get opened.set (start.reached, start.current.ready.state.cache, (reports.observed.atRun 0).2) =
        .ok () (next.reached, reports.observed.completed) ∧
    (∃ writer, reported.Completed writer ∧ next.current.ready.state = reported.next writer) ∧
    event = .checkpoint ∧ next.pins = start.pins
  | .checkpointPreflight calls atEntry (cause := cause) _ _ =>
    let state := start.current.ready.state
    opened.table.UsesOpenCheckpointSchedule state.session.directory opened.files opened.phase ∧
    runCheckpointOnOpenPhase (calls.cached.perform state.session.directory)
      opened.phase opened.get opened.set (start.reached, state.cache, atEntry) =
        .error cause (next.reached, state.cache, atEntry) ∧
    CheckpointPreflight (.ready state.writer.installed) (.error cause) ∧
    event = .checkpointRejected cause ∧ next = start
  | .rotateCreated report seen =>
    seen.Reached report.lookup next ∧ event = .rotatedWal ∧
      ∃ returned : NativeReadPosition start.current.history start.current.submissions,
        NativeCreatedRotationContinuation start.current.ready returned report ∧
        next.current = ⟨start.current.history, start.current.submissions, returned⟩
  | .rotateExisting report seen =>
    seen.Reached report.opened.lookup next ∧ event = .rotatedWal ∧
      ∃ returned : NativeReadPosition start.current.history start.current.submissions,
        NativeExistingRotationContinuation start.current.ready returned report ∧
        next.current = ⟨start.current.history, start.current.submissions, returned⟩
  | .rotateEmpty calls lookup (active := active) (pending := pending) (directory := directory) _ _ _ =>
    UsesRotationSchedule opened.table opened.directory opened.phase active pending directory ∧
      calls.run opened lookup active start.reached = .ok () next.reached ∧ event = .rotatedWal ∧ next = start
  | .rewriteRun request =>
    request.publicCall opened.table = rewriteRunWith (m := IO) (do (← opened.phase.get).installed)
      opened.phase.set request.update ∧
    ∃ result : Bool,
      rewriteRunWith (m := EStateM IO.Error heap) (do (← opened.get opened.phase).installed)
        (opened.set opened.phase) request.update start.reached = .ok result next.reached ∧
      (result = false → next.reached = start.reached) ∧
      (result = true →
        opened.set opened.phase next.current.ready.state.session.phase start.reached = .ok () next.reached) ∧
      event = .rewroteRun request result ∧ next.pins = start.pins
  | .acquireAt sequence (pin := pin) _ =>
    ∃ issue : SnapshotPin → DiskSnapshotPin, ∃ returned : NativeOpenedPin opened,
      opened.table.acquireAt sequence = acquireSnapshotWith (m := IO)
        (do (← opened.phase.get).installed) opened.phase.set issue sequence ∧
      acquireSnapshotWith (m := EStateM IO.Error heap) (do (← opened.get opened.phase).installed)
        (opened.set opened.phase) issue sequence start.reached = .ok (some returned.raw) next.reached ∧
      returned.raw = issue pin ∧ returned.localPin = pin ∧ next.pins = start.pins ++ [returned] ∧
      event = .snapshotControl (.acquireAt sequence) (.ok (some (start.current.ready.state.session.sessionRef, pin)))
  | .acquireAtUnavailable sequence _ =>
    ∃ issue : SnapshotPin → DiskSnapshotPin,
      opened.table.acquireAt sequence = acquireSnapshotWith (m := IO)
        (do (← opened.phase.get).installed) opened.phase.set issue sequence ∧
      acquireSnapshotWith (m := EStateM IO.Error heap) (do (← opened.get opened.phase).installed)
        (opened.set opened.phase) issue sequence start.reached = .ok none next.reached ∧
      event = .snapshotControl (.acquireAt sequence) (.ok none) ∧
      next.reached = start.reached ∧ next.current.ready.state = start.current.ready.state ∧ next.pins = start.pins
  | .releaseAt _ pin _ _ =>
    opened.table.release pin.raw.handle = releaseSnapshotWith (m := IO)
      (do (← opened.phase.get).installed) (opened.token.ptrEq opened.token) opened.phase.set pin.localPin.handle ∧
    releaseSnapshotWith (m := EStateM IO.Error heap) (do (← opened.get opened.phase).installed)
      (opened.ptrEq opened.token opened.token) (opened.set opened.phase) pin.localPin.handle start.reached =
        .ok () next.reached ∧
    opened.set opened.phase next.current.ready.state.session.phase start.reached = .ok () next.reached ∧
    event = .snapshotControl (.release start.current.ready.state.session.sessionRef pin.localPin.handle) (.ok ()) ∧
    next.pins = start.pins
  | .advanceFloor floor =>
    opened.table.advanceFloor floor = advanceFloorWith (m := IO)
      (do (← opened.phase.get).installed) opened.phase.set floor ∧
    ∃ accepted : Bool,
      advanceFloorWith (m := EStateM IO.Error heap) (do (← opened.get opened.phase).installed)
        (opened.set opened.phase) floor start.reached = .ok accepted next.reached ∧
      (accepted = false → next.reached = start.reached) ∧
      (accepted = true →
        opened.set opened.phase next.current.ready.state.session.phase start.reached = .ok () next.reached) ∧
      event = .snapshotControl (.advanceFloor floor) (.ok accepted) ∧ next.pins = start.pins
  | .readAt _ request pin _ _ =>
    (match request with
      | .lookup key => opened.table.lookup pin.raw.handle key = readSnapshotWith (m := IO)
          (do (← opened.phase.get).installed) (opened.token.ptrEq opened.token)
          (fun table => table.lookup pin.localPin.handle key)
      | .range lo hi => opened.table.range pin.raw.handle lo hi = readSnapshotWith (m := IO)
          (do (← opened.phase.get).installed) (opened.token.ptrEq opened.token)
          (fun table => table.range pin.localPin.handle lo hi)) ∧
    ∃ response recorded,
      readSnapshotWith (m := EStateM IO.Error heap) (do (← opened.get opened.phase).installed)
        (opened.ptrEq opened.token opened.token) (request.read pin.localPin.handle) start.reached =
          .ok response next.reached ∧
      event = .snapshotHandleRead start.current.ready.state.session.sessionRef pin.localPin.handle
        request response recorded ∧
      next.reached = start.reached ∧ next.pins = start.pins
  | .readSupplied pin request (issuer := issuer) (issued := issued) _ tokenIdentity _ _ _ =>
    (match request with
      | .lookup key => opened.table.lookup pin.handle key = readSnapshotWith (m := IO)
          (do (← opened.phase.get).installed) (issuer.ptrEq opened.token)
          (fun table => table.lookup issued.handle key)
      | .range lo hi => opened.table.range pin.handle lo hi = readSnapshotWith (m := IO)
          (do (← opened.phase.get).installed) (issuer.ptrEq opened.token)
          (fun table => table.range issued.handle lo hi)) ∧
    ∃ response recorded,
      readSnapshotWith (m := EStateM IO.Error heap) (do (← opened.get opened.phase).installed)
        (opened.ptrEq issuer opened.token) (request.read issued.handle) start.reached =
          .ok response next.reached ∧
      (response = none ↔ issuer ≠ opened.token ∨
        (issuer = opened.token ∧ start.current.ready.state.writer.installed.table.pins.find issued.handle = none)) ∧
      event = .snapshotHandleRead (tokenIdentity issuer) issued.handle request response recorded ∧
      next.current.ready.state = start.current.ready.state ∧ next.reached = start.reached ∧ next.pins = start.pins ∧
      next.current.ready.reads = start.current.ready.reads ++ [recorded]
  | .releaseSupplied pin (issuer := issuer) (issued := issued) _ tokenIdentity _ _ _ =>
    let before := start.current.ready.state
    let after := next.current.ready.state
    opened.table.release pin.handle = releaseSnapshotWith (m := IO)
      (do (← opened.phase.get).installed) (issuer.ptrEq opened.token) opened.phase.set issued.handle ∧
    releaseSnapshotWith (m := EStateM IO.Error heap) (do (← opened.get opened.phase).installed)
      (opened.ptrEq issuer opened.token) (opened.set opened.phase) issued.handle start.reached = .ok () next.reached ∧
    (issuer ≠ opened.token → next.reached = start.reached ∧ after = before) ∧
    (issuer = opened.token →
      after = before.withTable (before.writer.installed.table.release issued.handle) ∧
      opened.set opened.phase after.session.phase start.reached = .ok () next.reached ∧
      after.writer.installed.table.pins.find issued.handle = none ∧
      (∀ pin, pin ∈ after.writer.installed.table.pins.active ↔
        pin ∈ before.writer.installed.table.pins.active ∧ pin.handle ≠ issued.handle)) ∧
    event = .snapshotControl (.release (tokenIdentity issuer) issued.handle) (.ok ()) ∧
    after.files = before.files ∧ after.cache = before.cache ∧ after.census = before.census ∧ after.owner = before.owner ∧
    next.pins = start.pins ∧ next.current.history = start.current.history ∧
    next.current.submissions = start.current.submissions ∧ next.current.ready.reads = start.current.ready.reads
  | .acquire =>
    let before := start.current.ready.state
    let after := next.current.ready.state
    let load : EStateM IO.Error heap Installed := do (← opened.get opened.phase).installed
    ∃ (issue : SnapshotPin → DiskSnapshotPin) (returned : NativeOpenedPin opened) (table : PackedTable),
      opened.table.acquire = acquireLatestWith (m := IO) (do (← opened.phase.get).installed)
        (acquireSnapshotWith (do (← opened.phase.get).installed) opened.phase.set issue) ∧
      load start.reached = .ok before.writer.installed start.reached ∧
      acquireSnapshotWith load (opened.set opened.phase) issue before.writer.installed.table.committed start.reached =
        .ok (some returned.raw) next.reached ∧
      opened.acquireLatestRaw issue start.reached = .ok returned.raw next.reached ∧
      opened.set opened.phase after.session.phase start.reached = .ok () next.reached ∧
      before.writer.installed.table.acquireAt before.writer.installed.table.committed = some (returned.localPin, table) ∧
      after = before.withTable table ∧ returned.raw = issue returned.localPin ∧
      returned.raw.sequence = before.writer.installed.table.committed ∧ returned.localPin ∈ table.pins.active ∧
      event = .snapshotControl .acquire (.ok (before.session.sessionRef, returned.localPin)) ∧
      next.pins = start.pins ++ [returned] ∧ next.current.history = start.current.history ∧
      next.current.submissions = start.current.submissions ∧ next.current.ready.reads = start.current.ready.reads
  | .planWalCollection observed =>
    opened.table.UsesOpenWalPlanningSchedule start.current.ready.state.session.directory opened.phase ∧
    observed.calls.runOnOpenPhase opened start.reached = (match observed.extents.result with
      | .ok offsets => .ok offsets next.reached
      | .error cause => .error cause next.reached) ∧
    event = .walCollectionPlan observed.extents.result ∧ next = start
  | .collectObsoleteRuns held _ seen =>
    seen.Reached next ∧ seen.calls.run opened held seen.directory seen.active seen.pending start.reached =
      .ok () next.reached ∧ event = .collectedObsoleteRuns held
  | .obsoleteRunBarrierError held failed seen =>
    seen.Reached next ∧ seen.calls.run opened held seen.directory seen.active seen.pending start.reached =
      .error failed.diagnostic next.reached ∧ event = .obsoleteRunCollectionError held failed.diagnostic
  | .collectCoveredWal observed completed =>
    opened.table.UsesOpenWalCollectionSchedule start.current.ready.state.session.directory opened.files opened.phase ∧
    observed.runOnOpenPhase opened
      (start.reached, start.current.ready.state.cache, .start start.current.ready.state.writer.wal) =
      .ok () (next.reached, next.current.ready.state.cache, observed.barrier.after) ∧
    next.current.ready.state = observed.next completed ∧ next.pins = start.pins ∧
    event = .collectCoveredWal
  | .rejectsCoveredWalPlan observed cause _ =>
    opened.table.UsesOpenWalCollectionSchedule start.current.ready.state.session.directory opened.files opened.phase ∧
    (∀ publication,
      let entry := (start.reached, start.current.ready.state.cache, WalSealedUnlinkImage.start start.current.ready.state.writer.wal)
      observed.calls.collectOnOpenPhase opened publication entry = .error cause entry) ∧
    event = .coveredWalCollectionRejected cause ∧ next = start

structure Reached (report : NativeOpenedReport start instruction) (event : NativeExecutionEvent)
    (next : NativeOpenedPosition opened) : Prop where
  common : NativeExecutionStep start.current event next.current
  returned : report.Returns event next

private theorem reachesSnapshotControl {current : NativeExecutionPosition}
    {observed : NativeSnapshotUpdateObservation current.ready.state α}
    {next : NativeReadPosition current.history current.submissions} {value : α}
    (transition : NativeSnapshotUpdateContinuation current.ready observed next)
    (returned : observed.run = .ok value next.state.session) :
    NativeExecutionStep current (.snapshotControl observed.update (.ok value))
      ⟨current.history, current.submissions, next⟩ ∧
    next.state.session.directory = current.ready.state.session.directory := by
  have step := NativeExecutionStep.snapshotControl current observed next transition
  have response := transition.returned.symm.trans returned
  have state := transition.reached
  generalize observed.update.outcome current.ready.state.session = outcome at step response state
  cases outcome
  case failed => cases response
  all_goals
    have same := (EStateM.Result.ok.inj response).1
    subst value
    have directory := congrArg (fun value : NativeReadyState => value.session.directory) state
    exact ⟨step, directory⟩

/-- Interpret the observed latest-acquisition return of this fixed issuer.
The ready phase and its live cell determine the registered pin and the
setter's exact heap. The observed result fixes both. -/
theorem _root_.Alvoki.Storage.DiskSession.NativeOpenedPosition.refinesAcquireLatest
    (start : NativeOpenedPosition opened) (issuer : opened.LatestIssuer)
    {result : EStateM.Result IO.Error heap DiskSnapshotPin}
    (observed : opened.acquireLatestRaw issuer.val start.reached = result) :
    ∃ (next : NativeOpenedPosition opened) (pin : NativeOpenedPin opened),
      result = .ok pin.raw next.reached ∧ next.pins = start.pins ++ [pin] ∧
      (NativeOpenedReport.acquire (start := start)).Reached
        (.snapshotControl .acquire (.ok (start.current.ready.state.session.sessionRef, pin.localPin))) next := by
  let before := start.current.ready.state
  let data := before.writer.installed.table
  have valid := start.current.ready.readPrefix.refines.1
  obtain ⟨reference, refined, _⟩ := valid.retained.resumed.canonical
  have supported : data.pins.floor ≤ data.committed := by
    change before.writer.installed.table.pins.floor ≤ before.writer.installed.table.committed
    rw [refined.pins, refined.committed]
    exact reference.floor_committed
  have available : (data.acquireAt data.committed).isSome = true := by
    rw [PackedTable.acquireAt, Option.isSome_map, Sequential.SnapshotPins.acquire_iff]
    exact ⟨supported, UInt64.le_refl _⟩
  obtain ⟨⟨pin, table⟩, acquired⟩ := Option.isSome_iff_exists.mp available
  change before.writer.installed.table.acquireAt before.writer.installed.table.committed = some (pin, table) at acquired
  have selected : start.current.ready.state.writer.installed.table.acquireAt
      start.current.ready.state.writer.installed.table.committed = some (pin, table) := acquired
  let issue := issuer.val
  obtain ⟨next, transition⟩ := start.current.ready.updatesSnapshot (.acquire)
  have ready : before.session.phase = .ready before.writer.installed := valid.phase
  have returned : before.session.runAcquire = .ok (before.session.sessionRef, pin) next.state.session := by
    simpa only [NativeSnapshotUpdateObservation.run, NativeSnapshotUpdateObservation.update,
      SnapshotUpdate.outcome, valid.phase, selected] using transition.returned
  have state : next.state = before.withTable table := by
    simpa only [NativeSnapshotUpdateObservation.update, SnapshotUpdate.outcome, valid.phase, selected]
      using transition.reached
  have loaded := opened.phaseEffects.reads start.reached opened.phase before.session.phase start.stored
  let installed := Phase.ready { before.writer.installed with table }
  obtain ⟨reached, wrote, kept⟩ := opened.phaseEffects.writes start.reached opened.phase before.session.phase
    installed start.stored
  let load : EStateM IO.Error heap Installed := do (← opened.get opened.phase).installed
  have atEntry : load start.reached = .ok before.writer.installed start.reached := by
    simp only [load, Bind.bind, EStateM.bind, loaded, ready, Phase.installed, Pure.pure, EStateM.pure]
  have inner : acquireSnapshotWith load (opened.set opened.phase) issue data.committed start.reached =
      .ok (some (issue pin)) reached := by
    simp only [acquireSnapshotWith, Bind.bind, EStateM.bind, atEntry, acquired, wrote, installed, data,
      Pure.pure, EStateM.pure]
  have raw : opened.acquireLatestRaw issue start.reached = .ok (issue pin) reached := by
    change acquireLatestWith load (acquireSnapshotWith load (opened.set opened.phase) issue) start.reached = _
    simp only [acquireLatestWith, Bind.bind, EStateM.bind, atEntry, inner, data, Pure.pure, EStateM.pure]
  obtain ⟨step, directory⟩ := reachesSnapshotControl transition returned
  let actualPin : NativeOpenedPin opened := ⟨issue pin, pin, issuer.property.1 pin⟩
  let position : NativeOpenedPosition opened :=
    ⟨⟨start.current.history, start.current.submissions, next⟩, reached, directory.trans start.directory,
      by rw [state]; exact kept, start.pins ++ [actualPin]⟩
  have pinSpec := PackedTable.acquireAt_spec acquired
  have storedUpdate : opened.set opened.phase position.current.ready.state.session.phase start.reached = .ok () reached := by
    change opened.set opened.phase next.state.session.phase start.reached = .ok () reached
    rw [state]
    exact wrote
  refine ⟨position, actualPin, observed.symm.trans raw, rfl, step, issue, actualPin, table, issuer.property.2,
    atEntry, inner, raw, storedUpdate, acquired, state, rfl,
    (issuer.property.1 pin).2.2.trans pinSpec.sequence, pinSpec.active, rfl, rfl, rfl, rfl, transition.reads⟩

/-- Derive the next common step and the exact raw phase interpretation
from the local report. The step acquires its next position here. -/
theorem reaches (report : NativeOpenedReport start instruction) :
    ∃ event next, report.Reached event next := by
  cases report with
  | @write request nonempty calls cache observe sequence returnedHeap reached actual custody =>
    obtain ⟨ack, stored, _⟩ := start.current.ready.acknowledgesClassifiedWrite opened.table start.uses
      opened.phaseEffects start.stored request nonempty calls cache observe actual custody
    have directory : ack.next.state.session.directory = opened.directory := by
      rw [ack.exactState]
      exact start.directory
    let nextPosition : NativeOpenedPosition opened :=
      ⟨⟨start.current.history ++ ack.report.batch, start.current.submissions ++ [.acknowledgedBatch ack.report.batch],
        ack.next⟩, returnedHeap, directory, stored, start.pins⟩
    exact ⟨_, nextPosition, .acknowledgedClassified start.current ack, start.uses.writeSchedules,
      actual, ack, rfl, rfl, rfl⟩
  | writePreflight request calls cache preflight =>
    obtain ⟨source, seen, lookup, normalized, raw, continuation⟩ :=
      start.current.ready.preflightsClassifiedWriteOnOpenPhase opened.table start.uses opened.phaseEffects start.stored
        request calls cache preflight
    exact ⟨_, start, .writePreflight start.current seen continuation, source, seen, lookup, normalized, raw, rfl, rfl⟩
  | @checkpoint _ _ reports reported _ _ returned =>
    obtain ⟨source, writer, next, completed, reached, after, state, step, _, _, _, pins⟩ :=
      start.checkpointsFromReturn reported.primitives (reports.observed.atRun 0).2 reported rfl rfl returned
    exact ⟨_, next, step, source, by simpa only [reached, ← after] using returned,
      ⟨writer, completed, state⟩, rfl, pins⟩
  | checkpointPreflight calls atEntry returned stillReady =>
    obtain ⟨source, reached, after, preflight, _, step⟩ :=
      start.rejectsCheckpointFromReturn calls atEntry returned stillReady
    exact ⟨_, start, step, source, by simpa only [reached, after] using returned, preflight, rfl, rfl⟩
  | rotateCreated report seen =>
    obtain ⟨next, position, physical, common, same, returned⟩ := start.rotatesCreatedOnOpenPhase report seen
    exact ⟨_, position, common, returned, rfl, next, physical, same⟩
  | rotateExisting report seen =>
    obtain ⟨next, position, physical, common, same, returned⟩ := start.rotatesExistingOnOpenPhase report seen
    exact ⟨_, position, common, returned, rfl, next, physical, same⟩
  | rotateEmpty calls lookup references cachePath empty =>
    obtain ⟨source, returned, common⟩ := start.rotatesEmptyOnOpenPhase calls lookup references cachePath empty
    exact ⟨_, start, common, source, returned, rfl, rfl⟩
  | rewriteRun request =>
    obtain ⟨source, result, next, reached, returned, raw, stored, directory, refused, setter⟩ :=
      start.rewritesRunViaOpenReferences request
    let position : NativeOpenedPosition opened :=
      ⟨⟨start.current.history, start.current.submissions, next⟩, reached, directory, stored, start.pins⟩
    exact ⟨_, position, .rewriteRun start.current request result next returned, source, result,
      raw, refused, setter, rfl, rfl⟩
  | @acquireAt sequence pin table acquired =>
    obtain ⟨issue, next, result, reached, issued, source, transition, returned, raw, stored, _⟩ :=
      start.current.ready.acquiresViaOpenReferences opened.table start.uses opened.phaseEffects start.stored sequence
    have valid := start.current.ready.readPrefix.refines.1
    have exactPin := (EStateM.Result.ok.inj (returned.symm.trans (valid.acquireReturns acquired))).1
    subst result
    have state := transition.reached
    simp only [NativeSnapshotUpdateObservation.update, SnapshotUpdate.outcome, valid.phase, acquired] at state
    have directory : next.state.session.directory = opened.directory := by
      rw [state]
      exact start.directory
    let actualPin : NativeOpenedPin opened := ⟨issue pin, pin, issued pin⟩
    let nextPosition : NativeOpenedPosition opened :=
      ⟨⟨start.current.history, start.current.submissions, next⟩, reached, directory, stored, start.pins ++ [actualPin]⟩
    have common := NativeExecutionStep.snapshotControl start.current (.acquireAt sequence) next transition
    simp only [NativeSnapshotUpdateObservation.update, SnapshotUpdate.outcome, valid.phase, acquired] at common
    exact ⟨_, nextPosition, common, issue, actualPin, source, raw, rfl, rfl, rfl, rfl⟩
  | acquireAtUnavailable sequence unavailable =>
    obtain ⟨issue, next, result, reached, _, source, transition, returned, raw, stored, keepsHeap⟩ :=
      start.current.ready.acquiresViaOpenReferences opened.table start.uses opened.phaseEffects start.stored sequence
    have ready := start.current.ready.readPrefix.refines.1.phase
    have noneReturned : start.current.ready.state.session.runAcquireAt sequence = .ok none next.state.session := by
      simpa only [NativeSnapshotUpdateObservation.run, NativeSnapshotUpdateObservation.update, SnapshotUpdate.outcome,
        ready, unavailable] using transition.returned
    have sameResult := (EStateM.Result.ok.inj (returned.symm.trans noneReturned)).1
    subst result
    have state : next.state = start.current.ready.state := by
      simpa only [NativeSnapshotUpdateObservation.update, SnapshotUpdate.outcome, ready, unavailable] using transition.reached
    obtain ⟨step, directory⟩ := reachesSnapshotControl transition noneReturned
    let position : NativeOpenedPosition opened :=
      ⟨⟨start.current.history, start.current.submissions, next⟩, reached, directory.trans start.directory,
        stored, start.pins⟩
    exact ⟨_, position, step, issue, source, raw, rfl, keepsHeap rfl, state, rfl⟩
  | releaseAt _ pin _ compared =>
    obtain ⟨source, next, reached, transition, returned, raw, stored, _, setter⟩ :=
      start.current.ready.releasesViaOpenReferences opened.table start.uses pin.issued
        opened.phaseEffects start.stored opened.ptrEq start.current.ready.state.session.sessionRef true (by simp) compared
    obtain ⟨step, directory⟩ := reachesSnapshotControl transition returned
    let position : NativeOpenedPosition opened :=
      ⟨⟨start.current.history, start.current.submissions, next⟩, reached, directory.trans start.directory,
        stored, start.pins⟩
    exact ⟨_, position, step, source, raw, setter rfl, rfl, rfl⟩
  | advanceFloor floor =>
    obtain ⟨source, next, reached, accepted, transition, returned, raw, stored, refused, setter⟩ :=
      start.current.ready.advancesFloorViaOpenReferences opened.table start.uses opened.phaseEffects start.stored floor
    obtain ⟨step, directory⟩ := reachesSnapshotControl transition returned
    let position : NativeOpenedPosition opened :=
      ⟨⟨start.current.history, start.current.submissions, next⟩, reached, directory.trans start.directory,
        stored, start.pins⟩
    exact ⟨_, position, step, source, accepted, raw, refused, setter, rfl, rfl⟩
  | readAt _ request pin _ compared =>
    obtain ⟨source, response, recorded, next, observed, raw, _⟩ :=
      start.current.ready.readsOpenPin opened.table start.uses pin.issued
        (fun value => opened.phaseEffects.reads start.reached opened.phase value) start.stored opened.ptrEq compared request
    let nextPosition : NativeOpenedPosition opened :=
      ⟨⟨start.current.history, start.current.submissions, next⟩, start.reached,
        observed.state.symm ▸ start.directory, observed.state.symm ▸ start.stored, start.pins⟩
    have common := NativeExecutionStep.snapshotHandleRead start.current
      ⟨pin.localPin.handle, start.current.ready.state.session.sessionRef, true, by simp⟩ request response recorded next observed
    refine ⟨_, nextPosition, common, ?_, response, recorded, raw, rfl, rfl, rfl⟩
    cases request <;> exact source
  | readSupplied _ request owns tokenIdentity currentToken identifies compared =>
    obtain ⟨source, response, recorded, next, raw, denied, step, state, heap, pins, reads, _, _⟩ :=
      start.readsSuppliedPin owns tokenIdentity currentToken identifies compared request
    refine ⟨_, next, step, source, response, recorded, ?_, denied, rfl, state, heap, pins, reads⟩
    rw [heap]
    exact raw
  | @releaseSupplied _ issuer issued owns tokenIdentity currentToken identifies compared =>
    let before := start.current.ready.state
    let sameToken := tokenIdentity issuer = before.session.sessionRef
    have currentId : tokenIdentity opened.token = before.session.sessionRef := currentToken
    have same : sameToken ↔ issuer = opened.token := by
      simpa only [currentId] using identifies
    have comparison : opened.ptrEq issuer opened.token start.reached = .ok (decide sameToken) start.reached := by
      simpa only [sameToken, currentId] using compared
    obtain ⟨source, next, reached, transition, returned, raw, stored, keepsHeap, setter⟩ :=
      start.current.ready.releasesViaOpenReferences opened.table start.uses owns
        opened.phaseEffects start.stored opened.ptrEq (tokenIdentity issuer) (decide sameToken) rfl comparison
    obtain ⟨step, directory⟩ := reachesSnapshotControl transition returned
    let position : NativeOpenedPosition opened :=
      ⟨⟨start.current.history, start.current.submissions, next⟩, reached, directory.trans start.directory,
        stored, start.pins⟩
    have ready := start.current.ready.readPrefix.refines.1.phase
    refine ⟨_, position, step, source, raw, ?_, ?_, rfl, transition.files, transition.cache, transition.census,
      transition.owner, rfl, rfl, rfl, transition.reads⟩
    · intro foreign
      have distinct : tokenIdentity issuer ≠ start.current.ready.state.session.sessionRef :=
        fun equal => foreign (same.mp equal)
      refine ⟨keepsHeap (decide_eq_false distinct), ?_⟩
      simpa only [NativeSnapshotUpdateObservation.update, SnapshotUpdate.outcome, ready, distinct, ite_false]
        using transition.reached
    · intro localToken
      have localId : tokenIdentity issuer = start.current.ready.state.session.sessionRef := same.mpr localToken
      have updated : next.state = before.withTable (before.writer.installed.table.release issued.handle) := by
        simpa only [NativeSnapshotUpdateObservation.update, SnapshotUpdate.outcome, ready, localId, ite_true]
          using transition.reached
      refine ⟨updated, setter (decide_eq_true localId), ?_⟩
      change next.state.writer.installed.table.pins.find issued.handle = none ∧
        (∀ pin, pin ∈ next.state.writer.installed.table.pins.active ↔
          pin ∈ before.writer.installed.table.pins.active ∧ pin.handle ≠ issued.handle)
      rw [updated]
      exact ⟨before.writer.installed.table.pins.find_released issued.handle,
        before.writer.installed.table.pins.mem_release issued.handle⟩
  | acquire =>
    obtain ⟨issuer⟩ := opened.hasLatestIssuer
    obtain ⟨next, pin, _, _, atReturn⟩ := start.refinesAcquireLatest issuer rfl
    exact ⟨_, next, atReturn⟩
  | planWalCollection observed =>
    obtain ⟨source, raw, step, _, _, _, _, _⟩ := start.plansWalCollection observed
    exact ⟨_, start, step, source, raw, rfl, rfl⟩
  | collectObsoleteRuns held observed seen =>
    obtain ⟨next, returned, step⟩ := NativeOpenedPosition.collectsObsoleteRuns observed seen
    have actual := returned.returned
    unfold NativeObsoleteRunPass.collectorResult at actual
    rw [observed.completed] at actual
    exact ⟨_, next, step, returned, actual, rfl⟩
  | obsoleteRunBarrierError held failed seen =>
    obtain ⟨next, returned, diagnostic, step⟩ := NativeOpenedPosition.reachesObsoleteRunBarrierError failed seen
    exact ⟨_, next, step, returned, diagnostic, rfl⟩
  | collectCoveredWal observed completed =>
    obtain ⟨next, source, raw, state, pins, step⟩ := start.collectsCoveredWal observed completed
    exact ⟨_, next, step, source, raw, state, pins, rfl⟩
  | rejectsCoveredWalPlan observed _ rejected =>
    obtain ⟨source, raw, step⟩ := start.rejectsCoveredWalPlan observed rejected
    exact ⟨_, start, step, source, raw, rfl, rfl⟩

end NativeOpenedReport

/-- A finite prefix on one handle. The raw reports and the common
execution share every intermediate position. -/
inductive NativeOpenedTrace (start : NativeOpenedPosition opened) :
    List NativeOpenedInstruction → List NativeExecutionEvent → NativeOpenedPosition opened → Prop where
  | empty : NativeOpenedTrace start [] [] start
  | step (prior : NativeOpenedTrace start instructions events current)
      (report : NativeOpenedReport current instruction) (next : report.Reached event reached) :
      NativeOpenedTrace start (instructions ++ [instruction]) (events ++ [event]) reached

namespace NativeOpenedTrace

variable {start last : NativeOpenedPosition opened}

theorem common (trace : NativeOpenedTrace start instructions events last) :
    NativeExecutionTrace start.current events last.current := by
  induction trace with
  | empty => exact .empty
  | step _ _ next prior => exact .step prior next.common

/-- Supply a local report for the next prescribed instruction only at
positions reached by earlier returned operations on this handle. -/
def Reports (start : NativeOpenedPosition opened) (instructions : List NativeOpenedInstruction) : Prop :=
  ∀ issued events reached instruction remaining,
    instructions = issued ++ instruction :: remaining →
    NativeOpenedTrace start issued events reached → Nonempty (NativeOpenedReport reached instruction)

/-- A ready suffix can begin with previously tracked pins. Use
`NativeOpenedPosition.fromOpen` to start immediately after opening. -/
theorem executes (start : NativeOpenedPosition opened) (instructions : List NativeOpenedInstruction)
    (reports : Reports start instructions) :
    ∃ events last, NativeOpenedTrace start instructions events last ∧
      NativeExecutionTrace start.current events last.current ∧
      InstalledClientReplay last.current.submissions last.current.ready.reads last.current.history
        last.current.ready.state.writer.installed last.current.ready.state.session := by
  have finish (remaining : List NativeOpenedInstruction) : ∀ issued events current,
      instructions = issued ++ remaining → NativeOpenedTrace start issued events current →
      ∃ events last, NativeOpenedTrace start instructions events last := by
    induction remaining with
    | nil =>
      intro issued events current ordered trace
      exact ⟨events, current, by simpa [ordered] using trace⟩
    | cons instruction remaining earlier =>
      intro issued events current ordered trace
      obtain ⟨report⟩ := reports issued events current instruction remaining ordered trace
      obtain ⟨event, next, reached⟩ := report.reaches
      have follows : instructions = (issued ++ [instruction]) ++ remaining := by
        simpa [List.append_assoc] using ordered
      exact earlier (issued ++ [instruction]) (events ++ [event]) next follows (.step trace report reached)
  obtain ⟨events, last, trace⟩ := finish instructions [] [] start (by simp) .empty
  exact ⟨events, last, trace, trace.common, trace.common.keyValueRefinement.2.2.2⟩

end NativeOpenedTrace
end Alvoki.Storage.DiskSession
