import Alvoki.Storage.Disk.Proofs.Native.Open.NativeOpenAcquire

namespace Alvoki.Storage.DiskSession

open System
open Sequential (SnapshotPin SnapshotTable)

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

/-- Both public schedules act on the returned phase and token, with the
lookup consuming the pin at the heap reached by acquisition. -/
def _root_.Alvoki.Storage.DiskTable.ReadsLatest
    (db : DiskTable) (phase : IO.Ref (Phase Installed)) (token : IO.Ref Unit)
    (get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed))
    (set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit)
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool)
    (entry : heap) (key sequence : UInt64) (value : Option UInt64) : Prop :=
  ∃ (issue : SnapshotPin → DiskSnapshotPin) (pin : SnapshotPin) (after : heap),
    (issue pin).UsesOpenToken token pin ∧ (issue pin).sequence = sequence ∧
    db.acquire = acquireLatestWith (m := IO) (do (← phase.get).installed)
      (acquireSnapshotWith (do (← phase.get).installed) phase.set issue) ∧
    acquireLatestWith (m := EStateM IO.Error heap) (do (← get phase).installed)
      (acquireSnapshotWith (do (← get phase).installed) (set phase) issue) entry = .ok (issue pin) after ∧
    db.lookup (issue pin).handle key = readSnapshotWith (m := IO) (do (← phase.get).installed)
      (token.ptrEq token) (fun table => table.lookup pin.handle key) ∧
    readSnapshotWith (m := EStateM IO.Error heap) (do (← get phase).installed) (ptrEq token token)
      (fun table => table.lookup pin.handle key) after = .ok (some value) after

/-- One replay supplies the sequence and value of the observed latest read. -/
def _root_.Alvoki.Storage.DiskTable.LatestWalLookup
    (db : DiskTable) (phase : IO.Ref (Phase Installed)) (token : IO.Ref Unit)
    (get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed))
    (set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit)
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool)
    (entry : heap) (history : List WAL.Write) (key : UInt64) : Prop :=
  ∃ reference : SnapshotTable UInt64, SnapshotWalReplay .empty history reference ∧
    reference.committed.toNat = history.length ∧
    db.ReadsLatest phase token get set ptrEq entry key reference.committed
      (reference.table.lookup key reference.committed)

/-- Record the actual response alongside all earlier reads explained by
the same retained history. Deterministic replay identifies both models. -/
theorem _root_.Alvoki.Storage.DiskTable.LatestWalLookup.recordsRead
    {db : DiskTable} {phase token get set ptrEq} {entry : heap} {history key log reads}
    (lookup : db.LatestWalLookup phase token get set ptrEq entry history key)
    (pending : PendingClientReplay log reads history) :
    ∃ sequence value, db.ReadsLatest phase token get set ptrEq entry key sequence value ∧
      sequence.toNat = history.length ∧
      PendingClientReplay log (reads ++ [.lookup sequence key value]) history := by
  obtain ⟨model, played, count, observed⟩ := lookup
  obtain ⟨prior, earlier, retained, acknowledged, submitted, agrees⟩ := pending
  have same := earlier.deterministic played
  subst prior
  refine ⟨_, _, observed, count, model, played, retained, acknowledged, submitted, ?_⟩
  intro read member
  rcases List.mem_append.mp member with old | latest
  · exact agrees read old
  · obtain rfl := List.mem_singleton.mp latest
    rfl

/-- Acquire the latest pin and observe its lookup using the returned
phase and token. The installed table may have been restored from a
checkpoint as long as its latest entries agree with replay. -/
theorem _root_.Alvoki.Storage.DiskTable.UsesOpenReferences.lookupLatestAfterRepresentedHistory
    {db : DiskTable} {directory lock files phase token}
    (uses : db.UsesOpenReferences directory lock files phase token)
    {contents : heap → IO.Ref (Phase Installed) → Option (Phase Installed)}
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (effects : OpenPhaseCellEffects contents get set) {entry : heap} {installed : Installed}
    (stored : contents entry phase = some (.ready installed)) {history : List WAL.Write}
    {model : SnapshotTable UInt64} (refined : installed.table.Refines model)
    (represented : RepresentsWalHistory history model)
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool)
    (compares : ∀ {pinned : PackedTable} {after},
      set phase (.ready { installed with table := pinned }) entry = .ok () after →
      ptrEq token token after = .ok true after) (key : UInt64) :
    db.LatestWalLookup phase token get set ptrEq entry history key := by
  obtain ⟨reference, replayed, clock, _, _, _⟩ := id represented
  have available : installed.table.pins.floor ≤ installed.table.committed := by
    rw [refined.pins, refined.committed]
    exact model.floor_committed
  have sameTable : installed.table.SameData installed.table := ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨pin, pinned, acquired, lookups, _⟩ := sameTable.acquireAt_reads available (UInt64.le_refl _)
  have answer : pinned.lookup pin.handle key = some (reference.table.lookup key reference.committed) := by
    simp only [refined.table, refined.committed] at lookups
    have agree := (represented.reads replayed model.floor_committed).1 key
    exact (lookups key).trans (congrArg some (agree.trans (congrArg (reference.table.lookup key) clock)))
  obtain ⟨issue, owns, _, acquireSource⟩ := uses.snapshotAcquisitions
  obtain ⟨after, wrote, pinnedAt⟩ := effects.writes entry phase (.ready installed)
    (.ready { installed with table := pinned }) stored
  have loaded := effects.reads entry phase (.ready installed) stored
  have loadedPin := effects.reads after phase (.ready { installed with table := pinned }) pinnedAt
  have localToken := compares wrote
  have sequence := (owns pin).2.2.trans (PackedTable.acquireAt_spec acquired).sequence
  have count : reference.committed.toNat = history.length := by
    simpa only [show (SnapshotTable.empty : SnapshotTable UInt64).committed.toNat = 0 from rfl, Nat.zero_add]
      using replayed.committed_count
  refine ⟨reference, replayed, count, issue, pin, after, owns pin,
    sequence.trans (refined.committed.trans clock),
    acquireSource, ?_, uses.lookupPin (owns pin) key, ?_⟩
  · simp only [acquireLatestWith, acquireSnapshotWith, Bind.bind, EStateM.bind, loaded, Phase.installed,
      Pure.pure, EStateM.pure, acquired, wrote]
  · simp only [readSnapshotWith, withLocalHandle, Bind.bind, EStateM.bind, loadedPin, Phase.installed,
      Pure.pure, EStateM.pure, localToken, ↓reduceIte, answer]

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
