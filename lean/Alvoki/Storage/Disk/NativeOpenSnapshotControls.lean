import Alvoki.Storage.Disk.NativeOpenAcquire

namespace Alvoki.Storage.DiskSession

open System
open Sequential (SnapshotPin)

/-- Both public acquisition schedules read the same phase reference
and build the pin with the opened table's original token. -/
theorem _root_.Alvoki.Storage.DiskTable.UsesOpenReferences.snapshotAcquisitions
    {db : DiskTable} {directory lock files phase token}
    (uses : db.UsesOpenReferences directory lock files phase token) :
    ∃ issue : SnapshotPin → DiskSnapshotPin,
      (∀ pin, (issue pin).UsesOpenToken token pin) ∧
      (∀ sequence, db.acquireAt sequence = acquireSnapshotWith (m := IO) (do (← phase.get).installed)
        phase.set issue sequence) ∧
      db.acquire = acquireLatestWith (m := IO) (do (← phase.get).installed)
        (acquireSnapshotWith (do (← phase.get).installed) phase.set issue) := by
  obtain ⟨_, _, _, rfl, rfl⟩ := uses
  exact ⟨_, fun _ => ⟨rfl, rfl, rfl⟩, db.acquireAt_schedule, db.acquire_schedule⟩

variable {heap : Type}

/-- A foreign pin skips the setter. A local token always reaches the
setter, even if the local handle is no longer registered. The raw
token comparison is reported in the same heap as the phase read. -/
theorem NativeReadPosition.releasesViaOpenReferences {history log}
    (current : NativeReadPosition history log) (db : DiskTable)
    {lock : IO.FS.Handle} {files : DiskTable.OpenSyncFiles} {phase : IO.Ref (Phase Installed)} {token : IO.Ref Unit}
    (uses : db.UsesOpenReferences current.state.session.directory lock files phase token)
    {pin : DiskSnapshotPin} {issuerToken : IO.Ref Unit} {issued : SnapshotPin}
    (owns : pin.UsesOpenToken issuerToken issued)
    {contents : heap → IO.Ref (Phase Installed) → Option (Phase Installed)}
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (effects : OpenPhaseCellEffects contents get set) {before : heap}
    (stored : contents before phase = some current.state.session.phase)
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool)
    (issuer : Nat) (sameSession : Bool) (same : sameSession = decide (issuer = current.state.session.sessionRef))
    (compared : ptrEq issuerToken token before = .ok sameSession before) :
    let observed : NativeSnapshotUpdateObservation current.state Unit := .release issuer issued.handle sameSession same
    db.release pin.handle = releaseSnapshotWith (m := IO) (do (← phase.get).installed)
      (issuerToken.ptrEq token) phase.set issued.handle ∧
    ∃ (next : NativeReadPosition history log) (after : heap),
      NativeSnapshotUpdateContinuation current observed next ∧ observed.run = .ok () next.state.session ∧
      releaseSnapshotWith (m := EStateM IO.Error heap) (do (← get phase).installed) (ptrEq issuerToken token)
        (set phase) issued.handle before = .ok () after ∧
      contents after phase = some next.state.session.phase ∧
      (sameSession = false → after = before) ∧
      (sameSession = true → set phase next.state.session.phase before = .ok () after) := by
  intro observed
  refine ⟨uses.releasePin owns, ?_⟩
  obtain ⟨next, transition⟩ := current.updatesSnapshot observed
  have ready := current.readPrefix.refines.1.phase
  have loaded := effects.reads before phase current.state.session.phase stored
  have returned := transition.returned
  have reached := transition.reached
  cases sameSession with
  | false =>
    have foreign : issuer ≠ current.state.session.sessionRef := of_decide_eq_false same.symm
    simp only [observed, NativeSnapshotUpdateObservation.update, SnapshotUpdate.outcome, ready, foreign, ite_false]
      at returned reached
    refine ⟨next, before, transition, returned, ?_, ?_, fun _ => rfl, by simp⟩
    · simp only [releaseSnapshotWith, withLocalHandle, Bind.bind, EStateM.bind, loaded, ready, Phase.installed,
        Pure.pure, EStateM.pure, compared, Bool.false_eq_true, ↓reduceIte]
    · rw [reached]
      exact stored
  | true =>
    have localToken : issuer = current.state.session.sessionRef := of_decide_eq_true same.symm
    simp only [observed, NativeSnapshotUpdateObservation.update, SnapshotUpdate.outcome, ready, localToken, ite_true]
      at returned reached
    let updated := Phase.ready { current.state.writer.installed with
      table := current.state.writer.installed.table.release issued.handle }
    obtain ⟨after, wrote, kept⟩ := effects.writes before phase current.state.session.phase updated stored
    refine ⟨next, after, transition, returned, ?_, ?_, by simp, ?_⟩
    · simp only [releaseSnapshotWith, withLocalHandle, Bind.bind, EStateM.bind, loaded, ready, Phase.installed,
        Pure.pure, EStateM.pure, compared, ↓reduceIte, wrote, updated]
    · rw [reached]
      exact kept
    · intro _
      rw [reached]
      exact wrote

/-- The actual floor guard runs on the same ready phase. A refused
change has no setter effect. An accepted change updates that cell and
continues the same ready history and prior response ledger. -/
theorem NativeReadPosition.advancesFloorViaOpenReferences {history log}
    (current : NativeReadPosition history log) (db : DiskTable)
    {lock : IO.FS.Handle} {files : DiskTable.OpenSyncFiles} {phase : IO.Ref (Phase Installed)} {token : IO.Ref Unit}
    (uses : db.UsesOpenReferences current.state.session.directory lock files phase token)
    {contents : heap → IO.Ref (Phase Installed) → Option (Phase Installed)}
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (effects : OpenPhaseCellEffects contents get set) {before : heap}
    (stored : contents before phase = some current.state.session.phase) (floor : UInt64) :
    let observed : NativeSnapshotUpdateObservation current.state Bool := .advanceFloor floor
    db.advanceFloor floor = advanceFloorWith (m := IO) (do (← phase.get).installed) phase.set floor ∧
    ∃ (next : NativeReadPosition history log) (after : heap) (accepted : Bool),
      NativeSnapshotUpdateContinuation current observed next ∧ observed.run = .ok accepted next.state.session ∧
      advanceFloorWith (m := EStateM IO.Error heap) (do (← get phase).installed)
        (set phase) floor before = .ok accepted after ∧
      contents after phase = some next.state.session.phase ∧
      (accepted = false → after = before) ∧
      (accepted = true → set phase next.state.session.phase before = .ok () after) := by
  intro observed
  refine ⟨uses.advanceFloor floor, ?_⟩
  obtain ⟨next, transition⟩ := current.updatesSnapshot observed
  have ready := current.readPrefix.refines.1.phase
  have loaded := effects.reads before phase current.state.session.phase stored
  have returned := transition.returned
  have reached := transition.reached
  cases advanced : current.state.writer.installed.table.advanceFloor floor with
  | none =>
    simp only [observed, NativeSnapshotUpdateObservation.update, SnapshotUpdate.outcome, ready, advanced] at returned reached
    refine ⟨next, before, false, transition, returned, ?_, ?_, fun _ => rfl, by simp⟩
    · simp only [advanceFloorWith, Bind.bind, EStateM.bind, loaded, ready, Phase.installed, Pure.pure,
        EStateM.pure, advanced]
    · rw [reached]
      exact stored
  | some table =>
    simp only [observed, NativeSnapshotUpdateObservation.update, SnapshotUpdate.outcome, ready, advanced] at returned reached
    let updated := Phase.ready { current.state.writer.installed with table }
    obtain ⟨after, wrote, kept⟩ := effects.writes before phase current.state.session.phase updated stored
    refine ⟨next, after, true, transition, returned, ?_, ?_, by simp, ?_⟩
    · simp only [advanceFloorWith, Bind.bind, EStateM.bind, loaded, ready, Phase.installed, Pure.pure,
        EStateM.pure, advanced, wrote, updated]
    · rw [reached]
      exact kept
    · intro _
      rw [reached]
      exact wrote

end Alvoki.Storage.DiskSession
