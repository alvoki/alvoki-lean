import Alvoki.Storage.Disk.NativeAlignedCloseTableOpen

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
  have different : oldHandle.token ≠ newHandle.token := fun equal =>
    foreign (oldToken.symm.trans ((congrArg tokenIdentity equal).trans newToken))
  have ready := reopened.current.ready.readPrefix.refines.1.phase
  have loaded := newHandle.phaseEffects.reads reopened.reached newHandle.phase
    reopened.current.ready.state.session.phase reopened.stored
  refine ⟨different, issued, ?_, ?_, ?_⟩
  · cases request with
    | lookup key => exact reopened.uses.lookupIssuedPin pin.issued key
    | range lo hi => exact reopened.uses.rangeIssuedPin pin.issued lo hi
  · simp only [readSnapshotWith, withLocalHandle, Bind.bind, EStateM.bind, loaded, ready, Phase.installed,
      comparesDistinct different, Bool.false_eq_true, ↓reduceIte, Pure.pure, EStateM.pure]
  · obtain ⟨response, recorded, nextPosition, read⟩ := reopened.current.ready.readsHandle seen request
    have rejected := (request.handleDenied_iff (seen.reader reopened.current.ready.readPrefix.refines.1)
      pin.localPin.handle).2 (Or.inl foreign)
    have absent := (EStateM.Result.ok.inj (read.result.returned.symm.trans rejected)).1
    subst response
    let reached : NativeOpenedPosition newHandle :=
      ⟨⟨reopened.current.history, reopened.current.submissions, nextPosition⟩, reopened.reached,
        by rw [read.state]; exact reopened.directory, by rw [read.state]; exact reopened.stored, reopened.pins⟩
    exact ⟨recorded, reached, .snapshotHandleRead reopened.current seen request none recorded nextPosition read,
      read.result.records, read.state, rfl, rfl⟩

end Alvoki.Storage.DiskSession
