import Alvoki.Storage.Disk.NativeAlignedCloseTableOpen
import Alvoki.Storage.Disk.Proofs.Read.NativeOpenExternalPinRead

namespace Alvoki.Storage.DiskSession

open System

variable {heap : Type} {oldHandle newHandle : NativeOpenedHandle heap}
  {old : NativeOpenedPosition oldHandle} {reopened : NativeOpenedPosition newHandle}
  {input : FilePath} {observation : NativeCloseReopenObservation old.current.ready.state input}
  {next : NativeReadPosition old.current.history old.current.submissions}

/-- The new table rejects a point or range read with a pin issued on the
previous table. Its raw token differs by the returning session's proved
fresh identity. The same pointer guard used by public reads supplies
the denied response, without a heap update or a table read. -/
theorem NativeOpenedPosition.rejectsOldPinAfterReopen
    (close : NativeCloseReopenStep old.current.ready observation next)
    (sameCurrent : reopened.current = ⟨old.current.history, old.current.submissions, next⟩)
    (tokenIdentity : IO.Ref Unit → Nat)
    (oldToken : tokenIdentity oldHandle.token = old.current.ready.state.session.sessionRef)
    (newToken : tokenIdentity newHandle.token = reopened.current.ready.state.session.sessionRef)
    (index : Nat) (pin : NativeOpenedPin oldHandle) (issued : old.pins[index]? = some pin)
    (comparesDistinct : oldHandle.token ≠ newHandle.token →
      newHandle.ptrEq oldHandle.token newHandle.token reopened.reached = .ok false reopened.reached)
    (request : SnapshotReadRequest α) :
    let issuer := old.current.ready.state.session.sessionRef
    let current := reopened.current.ready.state.session.sessionRef
    let seen : NativeSnapshotHandleObservation reopened.current.ready.state.session :=
      ⟨pin.localPin.handle, issuer, false, by
        have same : current = next.state.session.sessionRef := by
          dsimp only [current]
          rw [sameCurrent]
        have distinct : issuer ≠ current := fun equal => close.sessionFresh (same.symm.trans equal.symm)
        exact (decide_eq_false distinct).symm⟩
    oldHandle.token ≠ newHandle.token ∧ old.pins[index]? = some pin ∧
    (match request with
      | .lookup key => newHandle.table.lookup pin.raw.handle key =
          readSnapshotWith (m := IO) (do (← newHandle.phase.get).installed)
            (oldHandle.token.ptrEq newHandle.token) (fun table => table.lookup pin.localPin.handle key)
      | .range lo hi => newHandle.table.range pin.raw.handle lo hi =
          readSnapshotWith (m := IO) (do (← newHandle.phase.get).installed)
            (oldHandle.token.ptrEq newHandle.token) (fun table => table.range pin.localPin.handle lo hi)) ∧
    readSnapshotWith (m := EStateM IO.Error heap) (do (← newHandle.get newHandle.phase).installed)
      (newHandle.ptrEq oldHandle.token newHandle.token) (request.read pin.localPin.handle) reopened.reached =
        .ok none reopened.reached ∧
    ∃ (recorded : RecordedSnapshotRead) (reached : NativeOpenedPosition newHandle),
      NativeExecutionStep reopened.current (.snapshotHandleRead issuer pin.localPin.handle request none recorded)
        reached.current ∧
      recorded = request.denied ((seen.reader reopened.current.ready.readPrefix.refines.1).guard pin.localPin.handle) ∧
      reached.current.ready.state = reopened.current.ready.state ∧ reached.reached = reopened.reached ∧
      reached.pins = reopened.pins := by
  intro issuer current seen
  have session : current = next.state.session.sessionRef := by
    dsimp only [current]
    rw [sameCurrent]
  have foreign : issuer ≠ current := by
    rw [session]
    exact close.sessionFresh.symm
  have distinctId : tokenIdentity oldHandle.token ≠ tokenIdentity newHandle.token :=
    fun equal => foreign (oldToken.symm.trans (equal.trans newToken))
  have different : oldHandle.token ≠ newHandle.token :=
    fun equal => distinctId (congrArg tokenIdentity equal)
  have identifies : tokenIdentity oldHandle.token = tokenIdentity newHandle.token ↔
      oldHandle.token = newHandle.token :=
    ⟨fun equal => False.elim (distinctId equal), congrArg tokenIdentity⟩
  have compared : newHandle.ptrEq oldHandle.token newHandle.token reopened.reached =
      .ok (decide (tokenIdentity oldHandle.token = tokenIdentity newHandle.token)) reopened.reached := by
    simpa only [decide_eq_false distinctId] using comparesDistinct different
  obtain ⟨source, response, recorded, reached, raw, denied, step, state, heap, pins, _, records, _⟩ :=
    reopened.readsSuppliedPin pin.issued tokenIdentity newToken identifies compared request
  have absent := denied.2 (Or.inl different)
  subst response
  refine ⟨different, issued, source, raw, recorded, reached, ?_, ?_, state, heap, pins⟩
  · simpa only [oldToken] using step
  · simpa only [oldToken, seen, issuer, current, NativeSnapshotHandleObservation.reader, ObservedSnapshotReader.guard]
      using records

end Alvoki.Storage.DiskSession
