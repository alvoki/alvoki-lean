import Alvoki.Storage.Disk.NativeOpenWrite

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WAL.Boundary SyncHandleRouting

namespace WriteRequest.ReturnedReports

/-- A nonempty request with an actual successful return determines the
acknowledged report for the same fixed callbacks. The projected return
fixes the committed sequence and the reached cache and image. -/
theorem acknowledgesOfNonemptyReturn {directory : DiskDirectory} {writer : SegmentedWriterState} {descriptor : Nat}
    {handle : Type} {request : WriteRequest} {calls : WriteRequest.Calls handle}
    (classified : WriteRequest.ReturnedReports request directory writer handle calls)
    (ready : writer.RetainedReady directory descriptor) (nonempty : request.rows ≠ [])
    {sequence : UInt64} {phase : Phase Installed} {reached : Cache handle × WriteFiles}
    (returned : calls.run request directory writer = .ok sequence (phase, ⟨reached, writer.owners⟩)) :
    ∃ (report : SegmentedBatchAppendReport directory writer) (observed : ObservedBatchWrite report handle),
      calls = WriteRequest.Calls.ofSuccess observed ∧ request.rows = report.rows ∧
      sequence = report.table.committed ∧ phase = .ready report.nextInstalled ∧ reached.2 = report.written := by
  have dispatch (seen : WriteRequest.Calls handle) := request.runReported_eq_batch ready
    (WriteRequest.readyCall writer seen.cache).2 seen.lookup seen.append seen.stage seen.sync seen.rename
  cases classified with
  | empty rows => exact False.elim (nonempty rows)
  | rejected guard =>
    rw [WriteRequest.Calls.run, dispatch, guard.run] at returned
    contradiction
  | acknowledged report observed rows =>
    obtain ⟨cache, exactWrite⟩ := observed.acknowledges
    rw [WriteRequest.Calls.run, dispatch, rows] at returned
    have agrees := EStateM.Result.ok.inj (returned.symm.trans exactWrite)
    exact ⟨report, observed, rfl, rows, agrees.1, congrArg Prod.fst agrees.2,
      congrArg (fun state : WriteCallState handle => state.2.image.2) agrees.2⟩
  | unknown failure observed rows =>
    obtain ⟨cache, failed⟩ := observed.commitUnknown
    simp only [← ready.directoryFiles] at failed
    rw [WriteRequest.Calls.run, dispatch, rows] at returned
    have impossible := returned.symm.trans failed
    contradiction

end WriteRequest.ReturnedReports

def NativeReadyState.afterWrite (before : NativeReadyState) (writer : SegmentedWriterState)
    (cache : CensusDirectoryCache) (custody : NativePendingWriteCensus before cache) : NativeReadyState :=
  { before with
    session := { before.session with phase := .ready writer.installed }
    writer := writer
    census := custody.reached
    cache := cache }

def NativeReadyState.afterClassifiedAck (before : NativeReadyState)
    (report : SegmentedBatchAppendReport before.session.directory before.writer) (target : Target)
    (cache : CensusDirectoryCache) (custody : NativePendingWriteCensus before cache) : NativeReadyState :=
  before.afterWrite (report.next target) cache custody

/-- Keep the observed reads with the new replay when an acknowledged
batch extends the ready writer's history. -/
def NativeReadPosition.afterAcknowledgedWrite {history log}
    (current : NativeReadPosition history log) (state : NativeReadyState)
    (valid : state.Valid) {batch : List WAL.Write}
    (extended : state.writer.history = history ++ batch) :
    NativeReadPosition (history ++ batch) (log ++ [.acknowledgedBatch batch]) :=
  let replayed := current.readPrefix.refines.2.2.appendAcknowledged current.readPrefix.readsBounded
    (extended ▸ valid.retained.resumed.ordered)
  ⟨.ok state.session (state.census, state.files), state, state, current.reads,
    .installed rfl valid extended replayed.1 replayed.2⟩

/-- The restored ready position comes from one acknowledged return and
its reported descriptor census. The sequence, cache and write-file
image all belong to those original callbacks. -/
structure ClassifiedWriteAcknowledgement (current : NativeReadPosition history log)
    (request : WriteRequest) (calls : WriteRequest.Calls (DescriptorInventory × DescriptorSlot × Nat))
    (sequence : UInt64) (reached : OpenWriteFiles) (custody : NativePendingWriteCensus current.state reached.1) where
  report : SegmentedBatchAppendReport current.state.session.directory current.state.writer
  observed : ObservedBatchWrite report (DescriptorInventory × DescriptorSlot × Nat)
  sameCalls : calls = WriteRequest.Calls.ofSuccess observed
  rows : request.rows = report.rows
  committedSequence : sequence = report.table.committed
  written : reached.2 = report.written
  target : Target
  selected : report.Selects target
  next : NativeReadPosition (history ++ report.batch) (log ++ [.acknowledgedBatch report.batch])
  returned : calls.run request current.state.session.directory current.state.writer =
    .ok sequence (next.state.session.phase, ⟨reached, current.state.files.owners⟩)
  exactState : next.state = current.state.afterClassifiedAck report target reached.1 custody
  initial : next.initial = next.state
  installed : next.opened = .ok next.state.session (next.state.census, next.state.files)
  reads : next.reads = current.reads
  replay : InstalledClientReplay (log ++ [.acknowledgedBatch report.batch]) current.reads
    (history ++ report.batch) next.state.writer.installed next.state.session

/-- Build the ready position from a projected acknowledgement.
The source interpreter supplies this result and the exact reached
descriptor and cache facts, independently of replay. -/
theorem NativeReadPosition.acknowledgesProjectedReturn {history log}
    (current : NativeReadPosition history log) (request : WriteRequest) (nonempty : request.rows ≠ [])
    (calls : WriteRequest.Calls (DescriptorInventory × DescriptorSlot × Nat))
    (classified : WriteRequest.ReturnedReports request current.state.session.directory current.state.writer
      (DescriptorInventory × DescriptorSlot × Nat) calls)
    {sequence : UInt64} {returnedPhase : Phase Installed} {reached : OpenWriteFiles}
    (returned : calls.run request current.state.session.directory current.state.writer =
      .ok sequence (returnedPhase, ⟨reached, current.state.writer.owners⟩))
    (custody : NativePendingWriteCensus current.state reached.1) :
    ∃ next : ClassifiedWriteAcknowledgement current request calls sequence reached custody,
      returnedPhase = next.next.state.session.phase := by
  obtain ⟨valid, beforeHistory, _⟩ := current.readPrefix.refines
  obtain ⟨report, observed, actualCalls, rows, sequenceEq, phaseEq, written⟩ :=
    classified.acknowledgesOfNonemptyReturn valid.retained nonempty returned
  obtain ⟨target, selected, retained⟩ := report.preservesRetained valid.retained
  let state := current.state.afterClassifiedAck report target reached.1 custody
  have stateReady : state.Valid := ⟨rfl, valid.owner, custody.ownerLive, custody.directoryLive,
    ⟨custody.cachedAt, custody.cachedDirectory⟩, retained⟩
  have extended : state.writer.history = history ++ report.batch :=
    congrArg (· ++ report.batch) beforeHistory
  let next := current.afterAcknowledgedWrite state stateReady extended
  have exactReturn := returned.trans (congrArg (fun value =>
    EStateM.Result.ok sequence (value, (⟨reached, current.state.writer.owners⟩ : LockedFileState OpenWriteFiles))) phaseEq)
  exact ⟨⟨report, observed, actualCalls, rows, sequenceEq, written, target, selected, next, exactReturn,
    rfl, rfl, rfl, rfl, next.readPrefix.guardedReplay⟩, phaseEq⟩

/-- Starting from the live opened cell, classify the actual successful
nonempty return, derive its retained-ready writer and preserve the
previous read ledger. The raw returned cache fixes the descriptor
report at this boundary, including the held lock and cached directory. -/
theorem NativeReadPosition.acknowledgesClassifiedWrite {heap : Type} {history log}
    (current : NativeReadPosition history log) (db : DiskTable)
    {lock : IO.FS.Handle} {files : DiskTable.OpenSyncFiles} {phase : IO.Ref (Phase Installed)} {token : IO.Ref Unit}
    (uses : db.UsesOpenReferences current.state.session.directory lock files phase token)
    {contents : heap → IO.Ref (Phase Installed) → Option (Phase Installed)}
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (effects : OpenPhaseCellEffects contents get set) {entry : heap}
    (stored : contents entry phase = some current.state.session.phase)
    (request : WriteRequest) (nonempty : request.rows ≠ [])
    (calls : WriteRequest.Calls (DescriptorInventory × DescriptorSlot × Nat))
    (cache : calls.cache = current.state.cache)
    (observe : ∀ checked : CheckedWriteRequest request current.state.session.directory current.state.writer.installed calls.lookup,
      Nonempty (WriteCallPublication calls checked))
    {sequence : UInt64} {returnedHeap : heap} {reached : OpenWriteFiles}
    (actual : request.runOnOpenPhase current.state.session.directory calls phase get set
      (entry, current.state.cache,
        WriteFiles.initial current.state.writer.history (current.state.files.image.directory.staged .walBoundary)) =
      .ok sequence (returnedHeap, reached))
    (custody : NativePendingWriteCensus current.state reached.1) :
    ∃ next : ClassifiedWriteAcknowledgement current request calls sequence reached custody,
      contents returnedHeap phase = some next.next.state.session.phase ∧
      db.UsesOpenReferences next.next.state.session.directory lock files phase token := by
  obtain ⟨_, projects⟩ := current.classifiesWriteOnOpenPhase db uses effects stored request calls cache
  rw [actual] at projects
  cases reachedPhase : contents returnedHeap phase with
  | none => simp [projectOpenWriteResult, reachedPhase] at projects
  | some returnedPhase =>
    have returned : calls.run request current.state.session.directory current.state.writer =
        .ok sequence (returnedPhase, ⟨reached, current.state.writer.owners⟩) := by
      exact Option.some.inj (by simpa only [projectOpenWriteResult, reachedPhase, Option.map_some] using projects.symm)
    have classified := calls.classifiesReturnedReports current.readPrefix.refines.1.retained request observe
    obtain ⟨next, exactPhase⟩ := current.acknowledgesProjectedReturn request nonempty calls classified returned custody
    have sameReferences : db.UsesOpenReferences next.next.state.session.directory lock files phase token := by
      rw [next.exactState]
      exact uses
    exact ⟨next, congrArg some exactPhase, sameReferences⟩

end Alvoki.Storage.DiskSession
