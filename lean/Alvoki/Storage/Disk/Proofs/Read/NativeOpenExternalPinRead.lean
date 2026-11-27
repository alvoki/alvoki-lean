import Alvoki.Storage.Disk.Proofs.Native.Open.NativeOpenedPosition

namespace Alvoki.Storage.DiskSession

open Sequential (SnapshotPin)

variable {heap : Type} {opened : NativeOpenedHandle heap}

/-- A ready table's public point or range read accepts the supplied issued
pin as its operand. Its issuer need not be the current table. The local
pointer-comparison report identifies the two live tokens in this heap.
For an equal token the reached registry alone determines whether the
handle is active. Neither branch changes the heap or the tracked pins. -/
theorem NativeOpenedPosition.readsSuppliedPin (start : NativeOpenedPosition opened)
    {pin : DiskSnapshotPin} {issuer : IO.Ref Unit} {issued : SnapshotPin}
    (owns : pin.UsesOpenToken issuer issued)
    (tokenIdentity : IO.Ref Unit → Nat)
    (currentToken : tokenIdentity opened.token = start.current.ready.state.session.sessionRef)
    (identifies : tokenIdentity issuer = tokenIdentity opened.token ↔ issuer = opened.token)
    (compared : opened.ptrEq issuer opened.token start.reached =
      .ok (decide (tokenIdentity issuer = tokenIdentity opened.token)) start.reached)
    (request : SnapshotReadRequest α) :
    (match request with
      | .lookup key => opened.table.lookup pin.handle key = readSnapshotWith (m := IO)
          (do (← opened.phase.get).installed) (issuer.ptrEq opened.token) (fun table => table.lookup issued.handle key)
      | .range lo hi => opened.table.range pin.handle lo hi = readSnapshotWith (m := IO)
          (do (← opened.phase.get).installed) (issuer.ptrEq opened.token) (fun table => table.range issued.handle lo hi)) ∧
    ∃ (response : Option α) (recorded : RecordedSnapshotRead) (next : NativeOpenedPosition opened),
      readSnapshotWith (m := EStateM IO.Error heap) (do (← opened.get opened.phase).installed)
        (opened.ptrEq issuer opened.token) (request.read issued.handle) start.reached =
          .ok response start.reached ∧
      (response = none ↔ issuer ≠ opened.token ∨
        (issuer = opened.token ∧ start.current.ready.state.writer.installed.table.pins.find issued.handle = none)) ∧
      NativeExecutionStep start.current (.snapshotHandleRead (tokenIdentity issuer) issued.handle request response recorded)
        next.current ∧
      next.current.ready.state = start.current.ready.state ∧ next.reached = start.reached ∧ next.pins = start.pins ∧
      next.current.ready.reads = start.current.ready.reads ++ [recorded] ∧
      (match response with
        | none => recorded = request.denied ⟨tokenIdentity issuer, start.current.ready.state.session.sessionRef,
            issued.handle, start.current.ready.state.writer.installed.table.pins.find issued.handle⟩
        | some value => ∃ active, start.current.ready.state.writer.installed.table.pins.find issued.handle = some active ∧
            recorded = request.record active.sequence value) ∧
      InstalledClientReplay start.current.submissions next.current.ready.reads start.current.history
        next.current.ready.state.writer.installed next.current.ready.state.session := by
  constructor
  · cases request with
    | lookup key => exact start.uses.lookupIssuedPin owns key
    | range lo hi => exact start.uses.rangeIssuedPin owns lo hi
  let state := start.current.ready.state
  have stateToken : tokenIdentity opened.token = state.session.sessionRef := currentToken
  let seen : NativeSnapshotHandleObservation state.session :=
    ⟨issued.handle, tokenIdentity issuer, decide (tokenIdentity issuer = state.session.sessionRef), rfl⟩
  obtain ⟨response, recorded, position, read⟩ := start.current.ready.readsHandle seen request
  let reader := seen.reader start.current.ready.readPrefix.refines.1
  have expected := reader.readResult (request.read issued.handle)
  have value := (EStateM.Result.ok.inj (expected.symm.trans read.result.returned)).1
  change (if tokenIdentity issuer = state.session.sessionRef then request.read issued.handle state.writer.installed.table
    else none) = response at value
  have denied := request.handleDenied_iff reader issued.handle
  rw [read.result.returned] at denied
  change (.ok response state.session = EStateM.Result.ok none state.session) ↔
    tokenIdentity issuer ≠ state.session.sessionRef ∨
      (tokenIdentity issuer = state.session.sessionRef ∧ state.writer.installed.table.pins.find issued.handle = none)
    at denied
  have none_iff : response = none ↔ issuer ≠ opened.token ∨
      (issuer = opened.token ∧ state.writer.installed.table.pins.find issued.handle = none) := by
    simpa only [EStateM.Result.ok.injEq, and_true, ← stateToken, ne_eq, identifies] using denied
  have ready : state.session.phase = .ready state.writer.installed := start.current.ready.readPrefix.refines.1.phase
  have loaded := opened.phaseEffects.reads start.reached opened.phase state.session.phase start.stored
  have comparison : opened.ptrEq issuer opened.token start.reached =
      .ok (decide (tokenIdentity issuer = state.session.sessionRef)) start.reached := by
    simpa only [stateToken] using compared
  have raw : readSnapshotWith (m := EStateM IO.Error heap) (do (← opened.get opened.phase).installed)
      (opened.ptrEq issuer opened.token) (request.read issued.handle) start.reached = .ok response start.reached := by
    simp only [readSnapshotWith, withLocalHandle, Bind.bind, EStateM.bind, loaded, ready, Phase.installed,
      Pure.pure, EStateM.pure, comparison]
    by_cases localToken : tokenIdentity issuer = state.session.sessionRef <;>
      simp [localToken, EStateM.pure] at value ⊢ <;> exact value
  let next : NativeOpenedPosition opened :=
    ⟨⟨start.current.history, start.current.submissions, position⟩, start.reached,
      read.state.symm ▸ start.directory, read.state.symm ▸ start.stored, start.pins⟩
  refine ⟨response, recorded, next, raw, none_iff,
    .snapshotHandleRead start.current seen request response recorded position read,
    read.state, rfl, rfl, read.reads, ?_, position.readPrefix.guardedReplay⟩
  cases response <;> exact read.result.records

end Alvoki.Storage.DiskSession
