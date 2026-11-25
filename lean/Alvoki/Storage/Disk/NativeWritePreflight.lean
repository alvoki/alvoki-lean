import Alvoki.Storage.Disk.NativeReadRecoveryTrace

namespace Alvoki.Storage.DiskSession

open System

/-- The first failing write preflight, or the successful empty batch.
The reported active-file check is the native no-follow lookup. -/
inductive NativeWritePreflightResult (state : NativeReadyState) (request : WriteRequest)
    (lookup : FilePath → Except IO.Error IO.FS.Metadata) : Except IO.Error UInt64 → Prop where
  | rejected {cause : IO.Error}
      (checked : BatchPreflightRejection state.session.directory state.writer.installed request.rows lookup cause) :
      NativeWritePreflightResult state request lookup (.error cause)
  | empty (rows : request.rows = []) :
      NativeWritePreflightResult state request lookup (.ok state.writer.installed.table.committed)

/-- Report the preflight at the reached session. No append, marker or
barrier callback is required to account for its response. -/
structure NativeWritePreflightObservation (state : NativeReadyState) (request : WriteRequest) where
  lookup : FilePath → Except IO.Error IO.FS.Metadata
  response : Except IO.Error UInt64
  checked : NativeWritePreflightResult state request lookup response

namespace NativeWritePreflightObservation

variable {state : NativeReadyState} {request : WriteRequest}

def resultAt (seen : NativeWritePreflightObservation state request) (before : σ) :
    EStateM.Result DiskWriteError σ UInt64 :=
  match seen.response with
  | .error cause => .error (.rejected cause) before
  | .ok sequence => .ok sequence before

/-- The production single or batch schedule returns at its original
phase and file state, for any interpretations of the unreached write
callbacks. The generic state can carry the full descriptor census. -/
theorem returns {image : Type} (seen : NativeWritePreflightObservation state request) (valid : state.Valid)
    (before : LockedFileState image) (append stage : FilePath → ByteArray → EStateM IO.Error image Unit)
    (sync : Array FilePath → EStateM IO.Error image Unit) (rename : FilePath → FilePath → EStateM IO.Error image Unit) :
    request.runReported state.session.directory seen.lookup append stage sync rename (state.session.phase, before) =
      seen.resultAt (state.session.phase, before) := by
  rw [valid.phase, request.runReported_eq_batch valid.retained before seen.lookup append stage sync rename]
  obtain ⟨lookup, response, checked⟩ := seen
  cases checked with
  | rejected checked => exact checked.run before append stage sync rename
  | empty rows =>
    rw [rows]
    exact runBatchWrite_empty _ _ _ _ _ _ _ _

/-- The classified and plain write APIs preserve the same projected
owner, files, cache and phase at return. -/
theorem returnsWithCache (seen : NativeWritePreflightObservation state request) (valid : state.Valid)
    (calls : WriteRequest.Calls (DescriptorInventory × DescriptorSlot × Nat))
    (cache : calls.cache = state.cache) (lookup : calls.lookup = seen.lookup) :
    let before := WriteRequest.readyCall state.writer state.cache
    calls.run request state.session.directory state.writer = seen.resultAt before ∧
      calls.runPlain request state.session.directory state.writer = WriteRequest.plainResult (seen.resultAt before) := by
  have returned := seen.returns valid (WriteRequest.readyCall state.writer state.cache).2
    calls.append calls.stage calls.sync calls.rename
  rw [valid.phase] at returned
  have classified : calls.run request state.session.directory state.writer =
      seen.resultAt (WriteRequest.readyCall state.writer state.cache) := by
    unfold WriteRequest.Calls.run
    rw [cache, lookup]
    exact returned
  exact ⟨classified, congrArg WriteRequest.plainResult classified⟩

end NativeWritePreflightObservation

/-- The unchanged continuation leaves the same session, writer, pins,
files, cache, live descriptors and client ledger available to the next
instruction. Retain the exact response alongside that continuation. -/
structure NativeWritePreflightStep (current : NativeReadPosition history log) {request : WriteRequest}
    (seen : NativeWritePreflightObservation current.state request) (next : NativeReadPosition history log) : Prop where
  unchanged : next = current
  returned : ∀ {image : Type} (before : LockedFileState image)
      (append stage : FilePath → ByteArray → EStateM IO.Error image Unit)
      (sync : Array FilePath → EStateM IO.Error image Unit) (rename : FilePath → FilePath → EStateM IO.Error image Unit),
    request.runReported current.state.session.directory seen.lookup append stage sync rename
      (current.state.session.phase, before) = seen.resultAt (current.state.session.phase, before)

theorem NativeReadPosition.preflightsWrite (current : NativeReadPosition history log) {request : WriteRequest}
    (seen : NativeWritePreflightObservation current.state request) : NativeWritePreflightStep current seen current :=
  ⟨rfl, seen.returns current.readPrefix.refines.1⟩

end Alvoki.Storage.DiskSession
