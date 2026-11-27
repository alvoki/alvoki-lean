import Alvoki.Storage.Disk.Proofs.Write.NativeOpenWrite

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair WAL.Boundary SyncHandleRouting

/-- An exact uncertain return selects the failure report of the same
fixed callbacks. Invert the existing indexed return contract at this
writer; the actual prior read ledger is carried by the pending state. -/
theorem WriteRequest.ReturnedReports.uncertainOfReturn {directory : DiskDirectory}
    {writer : SegmentedWriterState} {descriptor : Nat} {handle : Type}
    {request : WriteRequest} {calls : WriteRequest.Calls handle}
    (classified : WriteRequest.ReturnedReports request directory writer handle calls)
    (ready : writer.RetainedReady directory descriptor)
    {cause : IO.Error} {phase : Phase Installed} {reached : Cache handle × WriteFiles}
    (returned : calls.run request directory writer = .error (.commitUnknown cause) (phase, ⟨reached, writer.owners⟩)) :
    ∃ (failure : SegmentedBatchFailure directory writer) (observed : ObservedBatchFailure failure handle),
      calls = WriteRequest.Calls.ofFailure observed ∧ request.rows = failure.rows ∧
      cause = failure.cause ∧ phase = .poisoned ∧ reached.2 = failure.failed := by
  let here : SegmentedClientReadTrace directory descriptor writer false [] [] descriptor writer := .start
  have exactReturn := classified.refinesClient here ready
  rw [returned] at exactReturn
  cases exactReturn with
  | unknown failure observed sameCalls rows _ => exact ⟨failure, observed, sameCalls, rows, rfl, rfl, rfl⟩

/-- The uncertain write packet consumes the original raw return's cache,
file projection and descriptor observation. It retains the exact request
and diagnostic and the same issued callbacks. -/
structure ClassifiedUncertainWrite (current : NativeReadPosition history log)
    (request : WriteRequest) (calls : WriteRequest.Calls (DescriptorInventory × DescriptorSlot × Nat))
    (cause : IO.Error) (reached : OpenWriteFiles) (custody : NativePendingWriteCensus current.state reached.1) where
  write : NativeReadyWriteFailure current.state
  sameRequest : write.request = request
  sameCalls : calls = WriteRequest.Calls.ofFailure write.observed
  diagnostic : write.failure.cause = cause
  files : write.failure.failed = reached.2
  returned : write.returnedAt reached.1

def ClassifiedUncertainWrite.pending
    (seen : ClassifiedUncertainWrite current request calls cause reached custody) : NativePendingWrite current :=
  ⟨seen.write, reached.1, seen.returned, custody⟩

/-- Classify the actual raw write error from the same live opened cell.
The original returned cause, file/cache projection and reported census
supply one pending write. Its marker selection accounts for the earlier
read ledger and one uncertain batch, without requiring a successful open. -/
theorem NativeReadPosition.stopsAtClassifiedUncertainWrite {heap : Type} {history log}
    (current : NativeReadPosition history log) (db : DiskTable)
    {lock : IO.FS.Handle} {files : DiskTable.OpenSyncFiles} {phase : IO.Ref (Phase Installed)} {token : IO.Ref Unit}
    (uses : db.UsesOpenReferences current.state.session.directory lock files phase token)
    {contents : heap → IO.Ref (Phase Installed) → Option (Phase Installed)}
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (effects : OpenPhaseCellEffects contents get set) {entry : heap}
    (stored : contents entry phase = some current.state.session.phase)
    (request : WriteRequest) (calls : WriteRequest.Calls (DescriptorInventory × DescriptorSlot × Nat))
    (cache : calls.cache = current.state.cache)
    (observe : ∀ checked : CheckedWriteRequest request current.state.session.directory current.state.writer.installed calls.lookup,
      Nonempty (WriteCallPublication calls checked))
    {cause : IO.Error} {after : heap} {reached : OpenWriteFiles}
    (actual : request.runOnOpenPhase current.state.session.directory calls phase get set
      (entry, (WriteRequest.readyCall current.state.writer current.state.cache).2.image) =
        .error (.commitUnknown cause) (after, reached))
    (custody : NativePendingWriteCensus current.state reached.1) :
    db.UsesOpenWriteSchedules current.state.session.directory files phase ∧
    ∃ seen : ClassifiedUncertainWrite current request calls cause reached custody,
      contents after phase = some seen.pending.session.phase ∧
      db.UsesOpenReferences seen.pending.session.directory lock files phase token ∧
      seen.pending.poisoned.files = ⟨reached, current.state.files.owners⟩ ∧
      seen.pending.poisoned.descriptors = custody.reached ∧
      calls.run request current.state.session.directory current.state.writer =
        .error (.commitUnknown cause) (seen.pending.session.phase, ⟨reached, current.state.files.owners⟩) ∧
      ∃ chosen,
        (chosen = history ∨ chosen = history ++ seen.write.failure.batch) ∧
        seen.pending.files.image.directory.active.walBoundary =
          some (WAL.Boundary.encode (WAL.encode chosen).size.toUInt64) ∧
        PendingClientReplay seen.pending.submissions current.reads chosen ∧
        ∀ read ∈ current.reads, read.BoundedBy chosen.length := by
  let state := current.state
  have valid := current.readPrefix.refines.1
  obtain ⟨source, projects⟩ := current.classifiesWriteOnOpenPhase db uses effects stored request calls cache
  change projectOpenWriteResult contents phase state.writer.owners
    (request.runOnOpenPhase state.session.directory calls phase get set
      (entry, (WriteRequest.readyCall state.writer state.cache).2.image)) =
        some (calls.run request state.session.directory state.writer) at projects
  rw [actual] at projects
  cases phaseAtReturn : contents after phase with
  | none => simp [projectOpenWriteResult, phaseAtReturn] at projects
  | some returnedPhase =>
    have returned : calls.run request state.session.directory state.writer =
        .error (.commitUnknown cause) (returnedPhase, ⟨reached, state.writer.owners⟩) := by
      exact Option.some.inj (by simpa only [projectOpenWriteResult, phaseAtReturn, Option.map_some] using projects.symm)
    have classified := calls.classifiesReturnedReports valid.retained request observe
    obtain ⟨failure, observed, sameCalls, rows, error, poisoned, cut⟩ :=
      classified.uncertainOfReturn valid.retained returned
    have seenCache : observed.cache = state.cache := (congrArg WriteRequest.Calls.cache sameCalls).symm.trans cache
    let write : NativeReadyWriteFailure state := ⟨request, failure, observed, rows, seenCache⟩
    have fixed : ({ WriteRequest.Calls.ofFailure observed with cache := state.cache } :
        WriteRequest.Calls (DescriptorInventory × DescriptorSlot × Nat)) = calls := by
      rw [← sameCalls, ← cache]
    have returnedAtCache : write.returnedAt reached.1 := by
      unfold NativeReadyWriteFailure.returnedAt
      change ({ WriteRequest.Calls.ofFailure observed with cache := state.cache }).run request state.session.directory state.writer = _
      rw [fixed, returned, error, poisoned]
      let result (bytes : WriteFiles) :
          EStateM.Result DiskWriteError (Phase Installed × LockedFileState OpenWriteFiles) UInt64 :=
        .error (.commitUnknown failure.cause) (.poisoned, ⟨(reached.1, bytes), state.writer.owners⟩)
      exact congrArg result cut
    let seen : ClassifiedUncertainWrite current request calls cause reached custody :=
      ⟨write, rfl, sameCalls, error.symm, cut.symm, returnedAtCache⟩
    refine ⟨source, seen, congrArg some poisoned, uses, ?_, rfl, ?_, seen.pending.selectsAtReturn⟩
    · change (⟨(reached.1, failure.failed), state.writer.owners⟩ : LockedFileState OpenWriteFiles) = _
      rw [← cut]
      rfl
    · rw [returned, poisoned]
      rfl

end Alvoki.Storage.DiskSession
