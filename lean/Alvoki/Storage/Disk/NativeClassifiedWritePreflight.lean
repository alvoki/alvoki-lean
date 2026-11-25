import Alvoki.Storage.Disk.NativeOpenWrite

namespace Alvoki.Storage.DiskSession

open System WAL.Boundary

/-- Discriminate a preflight using only the fixed call's returned phase
and diagnostic tag. A successful write that installed a new writer is
excluded even if a caller disregards its committed sequence. -/
def WriteRequest.Calls.ReturnsPreflight {handle : Type} (calls : Calls handle)
    (request : WriteRequest) (state : NativeReadyState) : Prop :=
  match calls.run request state.session.directory state.writer with
  | .ok _ reached => reached.1 = .ready state.writer.installed
  | .error (.rejected _) _ => True
  | .error (.commitUnknown _) _ => False

/-- Recover the precise empty or rejected observation from the total
classification of the actual call. No checked preflight is supplied. -/
theorem WriteRequest.Calls.observesPreflight {handle : Type} (calls : Calls handle)
    (request : WriteRequest) {state : NativeReadyState} (valid : state.Valid)
    (preflight : calls.ReturnsPreflight request state) :
    ∃ seen : NativeWritePreflightObservation state request,
      seen.lookup = calls.lookup ∧
      calls.run request state.session.directory state.writer =
        seen.resultAt (readyCall state.writer calls.cache) := by
  have classified := request.classifiesReadyReturn valid.retained (readyCall state.writer calls.cache).2
    calls.lookup calls.append calls.stage calls.sync calls.rename
  change ReadyWriteReturn request state.session.directory state.writer.installed calls.lookup calls.append calls.stage
    calls.sync calls.rename (readyCall state.writer calls.cache).2
      (calls.run request state.session.directory state.writer) at classified
  unfold ReturnsPreflight at preflight
  generalize calls.run request state.session.directory state.writer = result at classified preflight ⊢
  cases classified with
  | empty rows =>
    exact ⟨⟨calls.lookup, .ok state.writer.installed.table.committed, .empty rows⟩, rfl, rfl⟩
  | @rejected reason guard =>
    exact ⟨⟨calls.lookup, .error reason, .rejected guard⟩, rfl, rfl⟩
  | acknowledged checked committed =>
    have installed : checked.next = state.writer.installed := Phase.ready.inj preflight
    have sameExtent : state.writer.installed.walBytes + WAL.frameSize * request.rows.length =
        state.writer.installed.walBytes := congrArg Installed.walBytes installed
    have nonempty : 0 < request.rows.length := by
      cases rows : request.rows with
      | nil => exact False.elim (checked.nonempty rows)
      | cons => simp
    have extended : 0 < WAL.frameSize * request.rows.length :=
      Nat.mul_pos (by decide) nonempty
    omega
  | uncertain => exact False.elim preflight

variable {heap : Type}

/-- Interpret that derived preflight on the same opened phase cell.
The exact reported return preserves the original heap, file/cache
projection and normalized ready position. -/
theorem NativeReadPosition.preflightsClassifiedWriteOnOpenPhase {history log}
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
    (preflight : calls.ReturnsPreflight request current.state) :
    let state := current.state
    let before := WriteRequest.readyCall state.writer state.cache
    db.UsesOpenWriteSchedules state.session.directory files phase ∧
    ∃ seen : NativeWritePreflightObservation state request,
      seen.lookup = calls.lookup ∧
      calls.run request state.session.directory state.writer = seen.resultAt before ∧
      request.runOnOpenPhase state.session.directory calls phase get set (entry, before.2.image) =
        seen.resultAt (entry, before.2.image) ∧
      NativeWritePreflightStep current seen current := by
  intro state before
  obtain ⟨seen, sameLookup, normalized⟩ :=
    calls.observesPreflight request current.readPrefix.refines.1 preflight
  refine ⟨uses.writeSchedules, seen, sameLookup, ?_, ?_, current.preflightsWrite seen⟩
  · simpa only [cache] using normalized
  · exact current.interpretsOpenWritePreflight db uses
      (effects.reads entry phase state.session.phase stored) set seen calls sameLookup before.2.image

end Alvoki.Storage.DiskSession
