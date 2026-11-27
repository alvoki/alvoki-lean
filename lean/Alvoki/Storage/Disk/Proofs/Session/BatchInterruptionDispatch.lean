import Alvoki.Storage.Disk.Proofs.Append.SegmentedBatchAppendPowerLoss
import Alvoki.Storage.Disk.Proofs.Recovery.SegmentedBatchPowerLoss
import Alvoki.Storage.Disk.Proofs.Write.ClientWriteTrace

namespace Alvoki.Storage.DiskSession

open System WalSegmentCommit WalSegmentRepair WAL.Boundary

private def observeBatchFileCall {stop image α : Type} (classify : IO.Error → DiskWriteError)
    (operation : ExceptT IO.Error (EStateM stop image) α) :
    ExceptT DiskWriteError (EStateM stop (Phase Installed × LockedFileState image)) α :=
  fun (phase, before) => match operation.run before.image with
    | .ok returned after => .ok (returned.mapError classify) (phase, { before with image := after })
    | .error stopped after => .error stopped (phase, { before with image := after })

/-- Interpret the production batch schedule with a separate channel for
interruption. An ordinary error is a returned `Except.error` value. A
stop exits the reported execution with no native return or error. -/
def runBatchWriteWithInterruption {stop image : Type} (directory : DiskDirectory)
    (rows : List (UInt64 × Option UInt64)) (lookup : FilePath → Except IO.Error IO.FS.Metadata)
    (publish : Installed → List WAL.Write → Nat → ExceptT IO.Error (EStateM stop image) Unit) :
    EStateM stop (Phase Installed × LockedFileState image) (Except DiskWriteError UInt64) :=
  (writeBatchSchedule rows
    (fun state => .ok ((state.1.installed : Except IO.Error Installed).mapError .rejected) state)
    DiskWriteError.rejected
    (fun prepared => match prepared with
      | some value => pure value
      | none => throw (.rejected (IO.userError "write sequence space exhausted")))
    (fun installed => observeBatchFileCall .rejected fun image =>
      .ok (checkActiveSegmentWith directory installed lookup) image)
    (fun phase => ExceptT.lift (modify fun state => (phase, state.2)))
    (fun installed events bytes => observeBatchFileCall .commitUnknown (publish installed events bytes))).run

/-- The native single-write schedule uses the same separation of returned
errors and stops. It prepares one event before checking the WAL extent. -/
def runSingleWriteWithInterruption {stop image : Type} (directory : DiskDirectory)
    (key : UInt64) (value : Option UInt64) (lookup : FilePath → Except IO.Error IO.FS.Metadata)
    (publish : Installed → List WAL.Write → Nat → ExceptT IO.Error (EStateM stop image) Unit) :
    EStateM stop (Phase Installed × LockedFileState image) (Except DiskWriteError UInt64) :=
  (withPreparedSingleWrite key value
    (fun state => .ok ((state.1.installed : Except IO.Error Installed).mapError .rejected) state)
    DiskWriteError.rejected
    (fun prepared => match prepared with
      | some value => pure value
      | none => throw (.rejected (IO.userError "write sequence space exhausted")))
    (fun installed => observeBatchFileCall .rejected fun image =>
      .ok (checkActiveSegmentWith directory installed lookup) image)
    (fun installed event table bytes =>
      publishPreparedWrite { installed with table, walBytes := bytes } event.sequence
        (fun phase => ExceptT.lift (modify fun state => (phase, state.2)))
        (observeBatchFileCall .commitUnknown (publish installed [event] bytes)))).run

/-- The caller's original write interface determines which preflight runs
before using the reported publication actions. -/
def WriteRequest.runWithInterruption {stop image : Type} (request : WriteRequest) (directory : DiskDirectory)
    (lookup : FilePath → Except IO.Error IO.FS.Metadata)
    (publish : Installed → List WAL.Write → Nat → ExceptT IO.Error (EStateM stop image) Unit) :
    EStateM stop (Phase Installed × LockedFileState image) (Except DiskWriteError UInt64) :=
  match request with
  | .single key value => runSingleWriteWithInterruption directory key value lookup publish
  | .batch rows => runBatchWriteWithInterruption directory rows lookup publish

/-- A reached singleton preparation produces the same event and sequence
under both production schedules. The same low-level publication can
therefore stop either schedule, carrying the identical reached state. -/
theorem runSingleWriteWithInterruption_eq_singleton {stop image : Type} {directory : DiskDirectory}
    {installed : Installed} {key : UInt64} {value : Option UInt64} {next : PackedTable}
    (written : installed.table.write key value = some next)
    (lookup : FilePath → Except IO.Error IO.FS.Metadata)
    (publish : Installed → List WAL.Write → Nat → ExceptT IO.Error (EStateM stop image) Unit)
    (before : LockedFileState image) :
    runSingleWriteWithInterruption directory key value lookup publish (.ready installed, before) =
      runBatchWriteWithInterruption directory [(key, value)] lookup publish (.ready installed, before) := by
  let event : WAL.Write := ⟨next.committed, key, value⟩
  have single : prepareWrite installed.table key value = some (event, next) := by
    simp [prepareWrite, written, event]
  have batch : prepareBatch installed.table [(key, value)] = some ([event], next) := by
    simp [prepareBatch_singleton, single]
  by_cases fits : installed.walBytes + WAL.frameSize < UInt64.size <;>
    simp [runSingleWriteWithInterruption, runBatchWriteWithInterruption, withPreparedSingleWrite, writeBatchSchedule,
      single, batch, event, fits, Phase.installed, Except.mapError, Except.pure, Bind.bind, ExceptT.bind,
      ExceptT.bindCont, ExceptT.mk, ExceptT.run, EStateM.bind, Pure.pure, ExceptT.pure,
      Functor.map, EStateM.pure, ExceptT.lift, publishPreparedWrite, publishPrepared,
      modify, modifyGet, MonadStateOf.modifyGet, throw, throwThe, MonadExceptOf.throw]

/-- The code reaches the interrupted publication only after the checked
prepared batch has put the same writer into the poisoned phase. A stop
prevents the ready-cell update and acknowledgement. -/
theorem runBatchWriteWithInterruption_stopped {stop image : Type} {directory : DiskDirectory}
    {rows : List (UInt64 × Option UInt64)} {installed : Installed} {events : List WAL.Write} {table : PackedTable}
    {lookup : FilePath → Except IO.Error IO.FS.Metadata}
    (nonempty : rows ≠ []) (prepared : prepareBatch installed.table rows = some (events, table))
    (fits : installed.walBytes + WAL.frameSize * rows.length < UInt64.size)
    (guard : checkActiveSegmentWith directory installed lookup = .ok ())
    (publish : Installed → List WAL.Write → Nat → ExceptT IO.Error (EStateM stop image) Unit)
    {before : LockedFileState image} {stopped : stop} {reached : image}
    (issued : (publish installed events (installed.walBytes + WAL.frameSize * rows.length)).run before.image =
      .error stopped reached) :
    runBatchWriteWithInterruption directory rows lookup publish (.ready installed, before) =
      .error stopped (.poisoned, { before with image := reached }) := by
  have nonempty' : rows.isEmpty = false := by
    cases rows with
    | nil => contradiction
    | cons => rfl
  change publish installed events (installed.walBytes + WAL.frameSize * rows.length) before.image = .error stopped reached at issued
  simp [runBatchWriteWithInterruption, writeBatchSchedule, nonempty', prepared, fits, guard,
    Phase.installed, Except.mapError, Except.pure, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.run,
    EStateM.bind, Pure.pure, ExceptT.pure, Functor.map, EStateM.map,
    EStateM.pure, ExceptT.lift, observeBatchFileCall, publishPreparedWrite, publishPrepared,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, issued]

private theorem checkObservedActiveSegment {directory : DiskDirectory} {installed : Installed}
    {lookup : FilePath → Except IO.Error IO.FS.Metadata}
    (seen : ∃ metadata, lookup (directory.file (.walSegment installed.activeFirst)) = .ok metadata ∧
      metadata.type = .file ∧ metadata.numLinks = 1 ∧
      metadata.byteSize.toNat = installed.walBytes - installed.activeFirst * WAL.frameSize) :
    checkActiveSegmentWith directory installed lookup = .ok () := by
  obtain ⟨metadata, found, regular, privateFile, extent⟩ := seen
  have kind : (IO.FS.FileType.file == .file) = true := rfl
  simp [checkActiveSegmentWith, checkPrivateRegularWith, found, regular, privateFile, extent, kind, Except.bind,
    Bind.bind, Except.pure, Pure.pure]

private theorem writtenFromSingleton {state : PackedTable} {key : UInt64} {value : Option UInt64}
    {batch : List WAL.Write} {next : PackedTable}
    (prepared : prepareBatch state [(key, value)] = some (batch, next)) :
    state.write key value = some next := by
  rw [prepareBatch_singleton, prepareWrite] at prepared
  cases written : state.write key value with
  | none => simp [written] at prepared
  | some table =>
    simp only [written, Option.map_some, Option.some.injEq, Prod.mk.injEq] at prepared
    rw [prepared.2]

/-- The active guard and nonempty preflight of either write dispatcher
reach the same interrupted publication with the exact reached files. -/
theorem WriteRequest.stopsPublication {stop image : Type} {directory : DiskDirectory} {installed : Installed}
    {rows : List (UInt64 × Option UInt64)} {events : List WAL.Write} {table : PackedTable}
    (request : WriteRequest) (submitted : request.rows = rows) (nonempty : rows ≠ [])
    (prepared : prepareBatch installed.table rows = some (events, table))
    (fits : installed.walBytes + WAL.frameSize * rows.length < UInt64.size)
    (guard : BatchActiveGuard directory installed)
    (publish : Installed → List WAL.Write → Nat → ExceptT IO.Error (EStateM stop image) Unit)
    {before : LockedFileState image} {stopped : stop} {reached : image}
    (issued : (publish installed events (installed.walBytes + WAL.frameSize * rows.length)).run before.image =
      .error stopped reached) :
    request.runWithInterruption directory guard.lookup publish (.ready installed, before) =
      .error stopped (.poisoned, { before with image := reached }) := by
  have checked := checkObservedActiveSegment (directory := directory) (installed := installed)
    ⟨guard.metadata, guard.reached, guard.regular, guard.privateFile, guard.extent⟩
  have batch := runBatchWriteWithInterruption_stopped nonempty prepared fits checked publish issued
  cases request with
  | batch group =>
    change group = rows at submitted
    simpa only [runWithInterruption, submitted] using batch
  | single key value =>
    have singleton : [(key, value)] = rows := submitted
    have wrote := writtenFromSingleton (singleton.symm ▸ prepared)
    simpa only [runWithInterruption, runSingleWriteWithInterruption_eq_singleton wrote, singleton] using batch

namespace BatchAppendInterruption

variable {directory : DiskDirectory} {before : SegmentedWriterState}
  {report : BatchAppendInterruption directory before}

/-- Run the submitted write interface through the reported first append.
The same callback records the issued path and bytes for either interface. -/
def runRequestUntilAppend (report : BatchAppendInterruption directory before) (request : WriteRequest)
    (stage : FilePath → ByteArray → ExceptT IO.Error (EStateM (FilePath × ByteArray) WriteFiles) Unit)
    (sync : Array FilePath → ExceptT IO.Error (EStateM (FilePath × ByteArray) WriteFiles) Unit)
    (rename : FilePath → FilePath → ExceptT IO.Error (EStateM (FilePath × ByteArray) WriteFiles) Unit) :
    EStateM.Result (FilePath × ByteArray) (Phase Installed × LockedFileState WriteFiles) (Except DiskWriteError UInt64) :=
  let scratch := before.files.directory.staged .walBoundary
  request.runWithInterruption directory report.activeMetadata
    (fun installed events bytes => commitBytesAt directory installed.activeFirst (WAL.encodeBatch events) bytes
      (fun path data _ => .error (path, data) (report.cut.writeFiles before.history scratch))
      stage sync rename)
    (.ready before.installed, ⟨WriteFiles.initial before.history scratch, before.owners⟩)

def runUntilAppend (report : BatchAppendInterruption directory before) :=
  report.runRequestUntilAppend (.batch report.rows)

/-- The outer batch call issues the first append with the old owner
retained and the poisoned phase already installed. The stop has no
ordinary return from the write API. -/
theorem Valid.stopsBatchSchedule (observed : report.Valid) (stage sync rename) :
    report.runUntilAppend stage sync rename =
      .error report.appendCall (.poisoned,
        ⟨report.cut.writeFiles before.history (before.files.directory.staged .walBoundary), before.owners⟩) := by
  unfold runUntilAppend runRequestUntilAppend WriteRequest.runWithInterruption
  dsimp only
  have guard := checkObservedActiveSegment observed.activeGuard
  apply runBatchWriteWithInterruption_stopped observed.nonempty observed.prepared observed.fits guard
  rw [observed.invoked]
  rfl

/-- The stop transition starts at the exact files and owner reached by
the no-return append schedule. The process or power-loss report applies
to this state, before any retry can change it. -/
theorem Valid.reachedFileState (observed : report.Valid)
    (outer : report.runUntilAppend stage sync rename = .error tag reached) :
    tag = report.appendCall ∧ reached.1 = .poisoned ∧
    (⟨FirstAppendCut.projectReached before reached.2.image, reached.2.owners⟩ : LockedFileState FileImage) =
      ⟨report.cut.physical before, before.owners⟩ := by
  obtain ⟨rfl, rfl⟩ := EStateM.Result.error.inj (outer.symm.trans (observed.stopsBatchSchedule stage sync rename))
  exact ⟨rfl, rfl, rfl⟩

theorem Valid.stopsSingleWriteSchedule (observed : report.Valid) {key : UInt64} {value : Option UInt64}
    (singleton : report.rows = [(key, value)]) (stage sync rename) :
    let scratch := before.files.directory.staged .walBoundary
    runSingleWriteWithInterruption directory key value report.activeMetadata
      (fun installed events bytes => commitBytesAt directory installed.activeFirst (WAL.encodeBatch events) bytes
        (fun path data _ => .error (path, data) (report.cut.writeFiles before.history scratch))
        stage sync rename)
      (.ready before.installed, ⟨WriteFiles.initial before.history scratch, before.owners⟩) =
    .error report.appendCall (.poisoned,
      ⟨report.cut.writeFiles before.history scratch, before.owners⟩) := by
  dsimp only
  rw [runSingleWriteWithInterruption_eq_singleton (writtenFromSingleton (singleton ▸ observed.prepared))]
  have stopped := observed.stopsBatchSchedule stage sync rename
  simpa only [runUntilAppend, runRequestUntilAppend, WriteRequest.runWithInterruption, singleton] using stopped

/-- Either submitted interface stops in the poisoned phase at the same
issued append, leaving the actual reached files and owner. -/
theorem Valid.stopsWriteRequest (observed : report.Valid) (request : WriteRequest)
    (rows : request.rows = report.rows) (stage sync rename) :
    report.runRequestUntilAppend request stage sync rename =
      .error report.appendCall (.poisoned,
        ⟨report.cut.writeFiles before.history (before.files.directory.staged .walBoundary), before.owners⟩) := by
  cases request with
  | single key value =>
    exact observed.stopsSingleWriteSchedule rows.symm stage sync rename
  | batch group =>
    change group = report.rows at rows
    subst group
    exact observed.stopsBatchSchedule stage sync rename

end BatchAppendInterruption

/-- Returned file errors flow through the ordinary API diagnostic. -/
private def returnedFile {stop image α : Type} (operation : EStateM IO.Error image α) :
    ExceptT IO.Error (EStateM stop image) α :=
  fun before => match operation before with
  | .ok value after => .ok (.ok value) after
  | .error cause reached => .ok (.error cause) reached

private def observeMarkerStep (cut : MarkerInterruption) (marker : ByteArray)
    (perform : Publication.Step → EStateM IO.Error WriteFiles Unit) (step : Publication.Step) :
    ExceptT IO.Error (EStateM Publication.Step WriteFiles) Unit :=
  if step = cut.action then
    fun reached => .error step (cut.interrupt marker reached)
  else returnedFile (perform step)

private theorem completedMarkerPrefix_stops {cut : MarkerInterruption} {marker : ByteArray}
    {perform : Publication.Step → EStateM IO.Error WriteFiles Unit}
    {completed rest : List Publication.Step} (beforeIssue : cut.action ∉ completed)
    {initial reached : WriteFiles} (ran : (completed.forM perform) initial = .ok () reached) :
    (((completed ++ cut.action :: rest).forM (observeMarkerStep cut marker perform)).run) initial =
      .error cut.action (cut.interrupt marker reached) := by
  induction completed generalizing initial with
  | nil =>
    have same : initial = reached := (EStateM.Result.ok.inj ran).2
    subst reached
    simp [List.forM_cons, observeMarkerStep, Bind.bind, ExceptT.bind, ExceptT.mk, ExceptT.run,
      EStateM.bind]
  | cons step earlier ih =>
    have notCurrent : step ≠ cut.action := fun same => beforeIssue (same ▸ List.mem_cons_self)
    have tail : cut.action ∉ earlier := fun member => beforeIssue (List.mem_cons_of_mem _ member)
    change (perform step >>= fun _ => earlier.forM perform) initial = _ at ran
    simp only [Bind.bind, EStateM.bind] at ran
    cases stepResult : perform step initial with
    | error cause failed => simp [stepResult] at ran
    | ok value after =>
      cases value
      rw [stepResult] at ran
      change ((observeMarkerStep cut marker perform step >>= fun _ =>
        (earlier ++ cut.action :: rest).forM (observeMarkerStep cut marker perform)).run) initial = _
      simp only [Bind.bind, observeMarkerStep, notCurrent, ↓reduceIte,
        ExceptT.bind, ExceptT.mk, ExceptT.run, EStateM.bind, returnedFile, stepResult, ExceptT.bindCont]
      exact ih tail ran

namespace SegmentedBatchMarkerPowerLossReport

variable {directory : DiskDirectory} {before : SegmentedWriterState} {writer : Nat}

/-- Execute the actual append and marker callback order, halting at the
reported issue. The current callback has no return, and the stop carries
its reported filesystem effect separately from ordinary IO errors. -/
def publishUntilIssue (report : SegmentedBatchMarkerPowerLossReport directory before writer)
    (installed : Installed) (batch : List WAL.Write) (bytes : Nat) :
    ExceptT IO.Error (EStateM Publication.Step WriteFiles) Unit :=
  commit (returnedFile (report.append (directory.file (.walSegment installed.activeFirst))
      (WAL.encodeBatch batch)))
    (Publication.run (observeMarkerStep report.cut (WAL.Boundary.encode bytes.toUInt64)
      (performMarkerAt directory installed.activeFirst bytes report.stage report.sync report.rename)))

/-- Lift the returned primitive prefix and observed marker issue into the
full batch schedule, without installing a ready phase or acknowledging it. -/
theorem Reached.stopsBatchSchedule {report : SegmentedBatchMarkerPowerLossReport directory before writer}
    (observed : report.Reached) :
    let scratch := before.wal.directory.staged .walBoundary
    runBatchWriteWithInterruption directory report.rows report.activeMetadata report.publishUntilIssue
      (.ready before.installed, ⟨WriteFiles.initial before.history scratch, before.owners⟩) =
      .error report.cut.action
        (.poisoned, ⟨report.cut.interrupt (WAL.Boundary.encode report.nextBytes.toUInt64) report.reached,
          before.owners⟩) := by
  intro scratch
  have guard := checkObservedActiveSegment observed.activeGuard
  apply runBatchWriteWithInterruption_stopped observed.nonempty observed.prepared observed.fits guard
  let initial := WriteFiles.initial before.history scratch
  let append := report.append (directory.file (.walSegment before.installed.activeFirst)) (WAL.encodeBatch report.batch)
  let perform := performMarkerAt directory before.installed.activeFirst report.nextBytes report.stage report.sync report.rename
  have completed := observed.reachedPrefix
  change (commit append ((Publication.steps.take report.cut.index).forM perform)) initial = .ok () report.reached at completed
  simp only [commit, Bind.bind, EStateM.bind] at completed
  cases appended : append initial with
  | error cause failed => simp [appended] at completed
  | ok value after =>
    cases value
    rw [appended] at completed
    have split : Publication.steps = Publication.steps.take report.cut.index ++
        report.cut.action :: Publication.steps.drop (report.cut.index + 1) := by
      cases report.cut <;> rfl
    have notReached : report.cut.action ∉ Publication.steps.take report.cut.index := by
      cases report.cut <;> simp [MarkerInterruption.action, MarkerInterruption.index, Publication.steps]
    have stopped := completedMarkerPrefix_stops
      (rest := Publication.steps.drop (report.cut.index + 1))
      (marker := WAL.Boundary.encode report.nextBytes.toUInt64) notReached completed
    rw [← split] at stopped
    change (commit (returnedFile append)
      (Publication.run (observeMarkerStep report.cut (WAL.Boundary.encode report.nextBytes.toUInt64) perform))).run initial = _
    simp only [commit, Bind.bind, ExceptT.bind, ExceptT.mk, ExceptT.run, EStateM.bind, returnedFile, appended,
      ExceptT.bindCont, Publication.run]
    exact stopped

theorem Reached.stopsSingleWriteSchedule {report : SegmentedBatchMarkerPowerLossReport directory before writer}
    (observed : report.Reached) {key : UInt64} {value : Option UInt64}
    (singleton : report.rows = [(key, value)]) :
    let scratch := before.wal.directory.staged .walBoundary
    runSingleWriteWithInterruption directory key value report.activeMetadata report.publishUntilIssue
      (.ready before.installed, ⟨WriteFiles.initial before.history scratch, before.owners⟩) =
      .error report.cut.action
        (.poisoned, ⟨report.cut.interrupt (WAL.Boundary.encode report.nextBytes.toUInt64) report.reached,
          before.owners⟩) := by
  dsimp only
  rw [runSingleWriteWithInterruption_eq_singleton (writtenFromSingleton (singleton ▸ observed.prepared))]
  simpa only [singleton] using observed.stopsBatchSchedule

/-- Both native write interfaces reach the same reported marker issue
for the request's prepared rows. -/
theorem Reached.stopsWriteRequest {report : SegmentedBatchMarkerPowerLossReport directory before writer}
    (observed : report.Reached) (request : WriteRequest) (rows : request.rows = report.rows) :
    let scratch := before.wal.directory.staged .walBoundary
    request.runWithInterruption directory report.activeMetadata report.publishUntilIssue
      (.ready before.installed, ⟨WriteFiles.initial before.history scratch, before.owners⟩) =
      .error report.cut.action
        (.poisoned, ⟨report.cut.interrupt (WAL.Boundary.encode report.nextBytes.toUInt64) report.reached,
          before.owners⟩) := by
  cases request with
  | single key value => exact observed.stopsSingleWriteSchedule rows.symm
  | batch submitted =>
    have exactRows : submitted = report.rows := rows
    simpa only [WriteRequest.runWithInterruption, exactRows] using observed.stopsBatchSchedule

end SegmentedBatchMarkerPowerLossReport
end Alvoki.Storage.DiskSession
