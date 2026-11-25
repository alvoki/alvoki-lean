import Alvoki.Storage.Disk.ClientReadTrace
import Alvoki.Storage.Disk.SessionRetentionFloor

namespace Alvoki.Storage.DiskSession

open Sequential (SnapshotHandle SnapshotPin SnapshotTable)

variable {session next : SegmentedSession} {installed : Installed} {before : SegmentedWriterState}

/-- Client operations that can update the in-memory snapshot registry or
retention floor. A release carries the issuing session's token and local pin. -/
inductive SnapshotUpdate : Type → Type where
  | acquireAt (snapshot : UInt64) : SnapshotUpdate (Option (Nat × SnapshotPin))
  | acquire : SnapshotUpdate (Nat × SnapshotPin)
  | release (issuer : Nat) (handle : SnapshotHandle) : SnapshotUpdate Unit
  | advanceFloor (floor : UInt64) : SnapshotUpdate Bool

def SnapshotUpdate.run : SnapshotUpdate α → EStateM IO.Error SegmentedSession α
  | .acquireAt snapshot => SegmentedSession.runAcquireAt snapshot
  | .acquire => SegmentedSession.runAcquire
  | .release issuer handle => fun session =>
    session.runRelease (decide (issuer = session.sessionRef)) handle
  | .advanceFloor floor => SegmentedSession.runAdvanceFloor floor

private theorem runAcquireAt_result (phase : session.phase = .ready installed) (snapshot : UInt64) :
    session.runAcquireAt snapshot =
      match installed.table.acquireAt snapshot with
      | none => .ok none session
      | some (pin, table) => .ok (some (session.sessionRef, pin)) { session with phase := .ready { installed with table } } := by
  cases acquired : installed.table.acquireAt snapshot with
  | none => simp [SegmentedSession.runAcquireAt, acquireSnapshotWith, phase, Phase.installed,
      Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, acquired]
  | some found =>
    obtain ⟨pin, table⟩ := found
    exact SegmentedSession.runAcquireAt_ready phase acquired

private theorem runAcquire_result (phase : session.phase = .ready installed) :
    session.runAcquire =
      match installed.table.acquireAt installed.table.committed with
      | none => .error (IO.userError "cannot acquire the latest snapshot") session
      | some (pin, table) => .ok (session.sessionRef, pin) { session with phase := .ready { installed with table } } := by
  cases acquired : installed.table.acquireAt installed.table.committed with
  | none =>
    have explicit := runAcquireAt_result phase installed.table.committed
    rw [acquired] at explicit
    simp only [SegmentedSession.runAcquire, acquireLatestWith, phase, Phase.installed, explicit,
      Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
    rfl
  | some found =>
    obtain ⟨pin, table⟩ := found
    exact SegmentedSession.runAcquire_of_acquireAt phase (SegmentedSession.runAcquireAt_ready phase acquired)

/-- Use the actual pointer comparison that the release schedule reached. -/
theorem SnapshotUpdate.run_release (handle : SnapshotHandle)
    (compared : sameSession = decide (issuer = session.sessionRef)) :
    (SnapshotUpdate.release issuer handle).run session = session.runRelease sameSession handle := by
  rw [compared]
  rfl

/-- On an available session, the actual schedule's successful outcome
supplies the exact next ready cell. The same table step supplies the next
mixed writer with no new WAL submissions. -/
theorem SnapshotUpdate.readyTransition (update : SnapshotUpdate α)
    (phase : session.phase = .ready before.installed) (returned : update.run session = .ok result next) :
    ∃ after, next = { session with phase := .ready after.installed } ∧
      SegmentedBatchDatabaseTrace session.directory session.descriptor before allowCollection [] session.descriptor after := by
  have unchanged (same : next = session) :
      ∃ after, next = { session with phase := .ready after.installed } ∧
        SegmentedBatchDatabaseTrace session.directory session.descriptor before allowCollection [] session.descriptor after := by
    refine ⟨before, ?_, .start⟩
    cases session
    simp_all
  cases update with
  | acquireAt snapshot =>
    rw [SnapshotUpdate.run, runAcquireAt_result phase snapshot] at returned
    cases acquired : before.installed.table.acquireAt snapshot with
    | none => exact unchanged (EStateM.Result.ok.inj (by simpa only [acquired] using returned)).2.symm
    | some found =>
      obtain ⟨pin, table⟩ := found
      rw [acquired] at returned
      exact ⟨before.withTable table, (EStateM.Result.ok.inj returned).2.symm, .table .start (.acquireAt acquired)⟩
  | acquire =>
    rw [SnapshotUpdate.run, runAcquire_result phase] at returned
    cases acquired : before.installed.table.acquireAt before.installed.table.committed with
    | none => simp [acquired] at returned
    | some found =>
      obtain ⟨pin, table⟩ := found
      rw [acquired] at returned
      exact ⟨before.withTable table, (EStateM.Result.ok.inj returned).2.symm, .table .start (.acquireAt acquired)⟩
  | release issuer handle =>
    change session.runRelease (decide (issuer = session.sessionRef)) handle = .ok result next at returned
    rw [SegmentedSession.runRelease_ready phase handle (issuer := issuer) rfl] at returned
    by_cases localToken : issuer = session.sessionRef
    · rw [ite_eq_left localToken] at returned
      exact ⟨before.withTable (before.installed.table.release handle), (EStateM.Result.ok.inj returned).2.symm,
        .table .start (.release handle true)⟩
    · rw [ite_eq_right localToken] at returned
      exact unchanged (EStateM.Result.ok.inj returned).2.symm
  | advanceFloor floor =>
    rw [SnapshotUpdate.run, SegmentedSession.runAdvanceFloor_ready phase] at returned
    cases advanced : before.installed.table.advanceFloor floor with
    | none => exact unchanged (EStateM.Result.ok.inj (by simpa only [advanced] using returned)).2.symm
    | some table =>
      rw [advanced] at returned
      exact ⟨before.withTable table, (EStateM.Result.ok.inj returned).2.symm, .table .start (.advanceFloor advanced)⟩

private theorem SnapshotUpdate.phaseError (update : SnapshotUpdate α)
    (rejected : session.phase.installed (m := EStateM IO.Error SegmentedSession) session =
      .error error session) : update.run session = .error error session := by
  cases update <;>
    simp only [SnapshotUpdate.run, SegmentedSession.runAcquireAt, SegmentedSession.runAcquire,
      SegmentedSession.runRelease, SegmentedSession.runAdvanceFloor, acquireSnapshotWith, acquireLatestWith,
      releaseSnapshotWith, withLocalHandle, advanceFloorWith, Bind.bind, EStateM.bind, rejected]

theorem SnapshotUpdate.closed (update : SnapshotUpdate α) (phase : session.phase = .closed) :
    update.run session = .error (IO.userError "database is closed") session := by
  apply update.phaseError
  rw [phase]
  rfl

theorem SnapshotUpdate.poisoned (update : SnapshotUpdate α) (phase : session.phase = .poisoned) :
    update.run session = .error (IO.userError "publication failed; reopen the database") session := by
  apply update.phaseError
  rw [phase]
  rfl

/-- The response together with the phase update, if the call made one. -/
inductive SnapshotUpdate.Outcome (α : Type) where
  | unchanged (value : α)
  | updated (value : α) (installed : Installed)
  | failed (cause : IO.Error)

def SnapshotUpdate.Outcome.reached (outcome : SnapshotUpdate.Outcome α)
    (session : SegmentedSession) : EStateM.Result IO.Error SegmentedSession α :=
  match outcome with
  | .unchanged value => .ok value session
  | .updated value installed => .ok value { session with phase := .ready installed }
  | .failed cause => .error cause session

/-- Read the response and phase update from the installed table and the
reported identity of the release handle. The token and pin of a successful
acquisition are those issued by this session. -/
def SnapshotUpdate.outcome (update : SnapshotUpdate α) (session : SegmentedSession) :
    SnapshotUpdate.Outcome α :=
  match session.phase with
  | .closed => .failed (IO.userError "database is closed")
  | .poisoned => .failed (IO.userError "publication failed; reopen the database")
  | .ready installed =>
    match update with
    | .acquireAt snapshot =>
      match installed.table.acquireAt snapshot with
      | none => .unchanged none
      | some (pin, table) => .updated (some (session.sessionRef, pin)) { installed with table }
    | .acquire =>
      match installed.table.acquireAt installed.table.committed with
      | none => .failed (IO.userError "cannot acquire the latest snapshot")
      | some (pin, table) => .updated (session.sessionRef, pin) { installed with table }
    | .release issuer handle =>
      if issuer = session.sessionRef then
        .updated () { installed with table := installed.table.release handle }
      else .unchanged ()
    | .advanceFloor floor =>
      match installed.table.advanceFloor floor with
      | none => .unchanged false
      | some table => .updated true { installed with table }

/-- Interpret the shared schedules for `DiskTable.acquireAt`, `acquire`,
`release` and `advanceFloor` on the same sequential phase cell. For
release, `run_release` substitutes the reported native pointer comparison. -/
theorem SnapshotUpdate.run_outcome (update : SnapshotUpdate α) (session : SegmentedSession) :
    update.run session = (update.outcome session).reached session := by
  cases phase : session.phase with
  | closed => simpa [outcome, phase, Outcome.reached] using update.closed phase
  | poisoned => simpa [outcome, phase, Outcome.reached] using update.poisoned phase
  | ready installed =>
    cases update with
    | acquireAt snapshot =>
      rw [run, runAcquireAt_result phase snapshot]
      cases acquired : installed.table.acquireAt snapshot with
      | none => simp [outcome, phase, acquired, Outcome.reached]
      | some found =>
        obtain ⟨pin, table⟩ := found
        simp [outcome, phase, acquired, Outcome.reached]
    | acquire =>
      rw [run, runAcquire_result phase]
      cases acquired : installed.table.acquireAt installed.table.committed with
      | none => simp [outcome, phase, acquired, Outcome.reached]
      | some found =>
        obtain ⟨pin, table⟩ := found
        simp [outcome, phase, acquired, Outcome.reached]
    | release issuer handle =>
      change session.runRelease (decide (issuer = session.sessionRef)) handle = _
      rw [SegmentedSession.runRelease_ready phase handle (issuer := issuer) rfl]
      by_cases localToken : issuer = session.sessionRef <;>
        simp [outcome, phase, localToken, Outcome.reached]
    | advanceFloor floor =>
      rw [run, SegmentedSession.runAdvanceFloor_ready phase]
      cases advanced : installed.table.advanceFloor floor <;>
        simp [outcome, phase, advanced, Outcome.reached]

/-- Extend the client ledger from the actual result, keeping the precise
returned phase and the same submissions and recorded reads on every branch. -/
theorem SegmentedClientReadTrace.snapshotUpdateOutcome
    (trace : SegmentedClientReadTrace session.directory initialDescriptor initial allowCollection log reads
      session.descriptor before)
    (update : SnapshotUpdate α)
    (ready : ∀ installed, session.phase = .ready installed → installed = before.installed) :
    ∃ after, (match update.run session with
        | .ok _ reached => reached = { session with phase := .ready after.installed }
        | .error _ reached => reached = session ∧ after = before) ∧
      SegmentedClientReadTrace session.directory initialDescriptor initial allowCollection log reads session.descriptor after := by
  cases returned : update.run session with
  | ok result next =>
    have phase : session.phase = .ready before.installed := by
      cases reachedPhase : session.phase with
      | closed =>
        rw [update.closed reachedPhase] at returned
        contradiction
      | poisoned =>
        rw [update.poisoned reachedPhase] at returned
        contradiction
      | ready installed => exact congrArg Phase.ready (ready installed reachedPhase)
    obtain ⟨after, reached, step⟩ := update.readyTransition (allowCollection := allowCollection) phase returned
    exact ⟨after, reached, by simpa only [List.append_nil] using trace.advance step⟩
  | error cause next =>
    rw [update.run_outcome] at returned
    cases seen : update.outcome session <;> simp [seen, SnapshotUpdate.Outcome.reached] at returned
    exact ⟨before, ⟨returned.2.symm, rfl⟩, trace⟩

/-- Extend the chronological trace while keeping the actual returned
session and the existing submissions and recorded reads. -/
theorem SegmentedClientReadTrace.observeSnapshotUpdate
    (trace : SegmentedClientReadTrace session.directory initialDescriptor initial allowCollection log reads
      session.descriptor before)
    (update : SnapshotUpdate α) (phase : session.phase = .ready before.installed)
    (returned : update.run session = .ok result next) :
    ∃ after, next = { session with phase := .ready after.installed } ∧
      SegmentedClientReadTrace session.directory initialDescriptor initial allowCollection log reads session.descriptor after := by
  simpa only [returned] using trace.snapshotUpdateOutcome update
    (fun _ supplied => Phase.ready.inj (supplied.symm.trans phase))

inductive SnapshotReadRequest : Type → Type where
  | lookup (key : UInt64) : SnapshotReadRequest (Option UInt64)
  | range (lo hi : UInt64) : SnapshotReadRequest (List (Compaction.Model.Entry (Option UInt64)))

def SnapshotReadRequest.read (handle : SnapshotHandle) : SnapshotReadRequest α → PackedTable → Option α
  | .lookup key => fun table => table.lookup handle key
  | .range lo hi => fun table => table.range handle lo hi

def SnapshotReadRequest.replay (reference : SnapshotTable UInt64) (sequence : UInt64) : SnapshotReadRequest α → α
  | .lookup key => reference.table.lookup key sequence
  | .range lo hi => reference.table.range lo hi sequence

def SnapshotReadRequest.record (sequence : UInt64) : SnapshotReadRequest α → α → RecordedSnapshotRead
  | .lookup key => .lookup sequence key
  | .range lo hi => .range sequence lo hi

def SnapshotReadRequest.denied (guard : SnapshotReadGuard) : SnapshotReadRequest α → RecordedSnapshotRead
  | .lookup key => .lookupDenied key guard
  | .range lo hi => .rangeDenied lo hi guard

/-- The native return and the ledger entry use the same request and
supplied handle. A successful response uses the registry's pin sequence. -/
structure SnapshotReadRequest.HandleReturn (request : SnapshotReadRequest α)
    (reader : ObservedSnapshotReader directory descriptor writer) (handle : SnapshotHandle)
    (response : Option α) (recorded : RecordedSnapshotRead) : Prop where
  returned : reader.session.runSnapshotRead reader.sameSession (request.read handle) = .ok response reader.session
  records : match response with
    | none => recorded = request.denied (reader.guard handle)
    | some value => ∃ pin, writer.installed.table.pins.find handle = some pin ∧
        recorded = request.record pin.sequence value
  observed : RecordedSnapshotRead.Observed directory descriptor writer recorded

/-- A ready read has outer absence exactly for a foreign token or an
inactive local handle. A missing key remains a successful point read. -/
theorem SnapshotReadRequest.handleDenied_iff (request : SnapshotReadRequest α)
    (reader : ObservedSnapshotReader directory descriptor writer) (handle : SnapshotHandle) :
    reader.session.runSnapshotRead reader.sameSession (request.read handle) = .ok none reader.session ↔
      (reader.guard handle).rejects := by
  cases request with
  | lookup key => exact reader.lookupDenied_iff handle key
  | range lo hi => exact reader.rangeDenied_iff handle lo hi

theorem SnapshotReadRequest.returnsForHandle (request : SnapshotReadRequest α)
    (reader : ObservedSnapshotReader directory descriptor writer) (handle : SnapshotHandle) :
    ∃ response recorded, request.HandleReturn reader handle response recorded := by
  have returned := reader.readResult (request.read handle)
  generalize (if reader.issuer = reader.session.sessionRef then request.read handle writer.installed.table else none) =
    response at returned
  refine ⟨response, ?_⟩
  cases request with
  | lookup key =>
    have observed := reader.recordLookup handle key response returned
    cases response with
    | none => exact ⟨_, returned, rfl, observed⟩
    | some value =>
      obtain ⟨pin, found, observed⟩ := observed
      exact ⟨_, returned, ⟨pin, found, rfl⟩, observed⟩
  | range lo hi =>
    have observed := reader.recordRange handle lo hi response returned
    cases response with
    | none => exact ⟨_, returned, rfl, observed⟩
    | some entries =>
      obtain ⟨pin, found, observed⟩ := observed
      exact ⟨_, returned, ⟨pin, found, rfl⟩, observed⟩

private theorem runSnapshotRead_of_guarded (phase : session.phase = .ready installed)
    (read : PackedTable → Option α)
    (guarded : withLocalHandle (m := Except IO.Error) session.phase.installed (.ok sameSession) none
      (fun state => pure (read state.table)) = .ok value) :
    session.runSnapshotRead sameSession read = .ok value session := by
  rw [SegmentedSession.runSnapshotRead, phase]
  rw [phase] at guarded
  cases sameSession
  · change Except.ok none = .ok value at guarded
    exact congrArg (fun result => EStateM.Result.ok result session) (Except.ok.inj guarded)
  · change Except.ok (read installed.table) = .ok value at guarded
    exact congrArg (fun result => EStateM.Result.ok result session) (Except.ok.inj guarded)

/-- A supported acquisition uses the exact recovered session and issues the
pin that serves the next read. The native read and the appended response both
use the same abstract replay that explains the preceding client responses. -/
theorem GuardedClientReplay.acquireAndRead
    (replay : GuardedClientReplay log reads before session)
    (trace : SegmentedClientReadTrace session.directory initialDescriptor initial allowCollection log reads
      session.descriptor before)
    (phase : session.phase = .ready before.installed) (snapshot : UInt64)
    (floor : before.installed.table.pins.floor ≤ snapshot) (committed : snapshot ≤ before.installed.table.committed) :
    ∃ (reference : SnapshotTable UInt64) (issued : Nat × SnapshotPin) (acquired : SegmentedSession)
      (after : SegmentedWriterState),
      SnapshotWalReplay .empty before.history reference ∧
      (∀ earlier ∈ reads, earlier.agrees reference) ∧
      session.runAcquireAt snapshot = .ok (some issued) acquired ∧
      issued.1 = acquired.sessionRef ∧ issued.2.sequence = snapshot ∧
      acquired = { session with phase := .ready after.installed } ∧
      ∀ (sameSession : Bool), sameSession = decide (issued.1 = acquired.sessionRef) →
        ∀ {α : Type} (request : SnapshotReadRequest α),
          acquired.runSnapshotRead sameSession (request.read issued.2.handle) =
            .ok (some (request.replay reference snapshot)) acquired ∧
          SegmentedClientReadTrace session.directory initialDescriptor initial allowCollection log
            (reads ++ [request.record snapshot (request.replay reference snapshot)]) session.descriptor after := by
  obtain ⟨reference, replayed, _, _, _, preceding, supported⟩ := replay
  obtain ⟨issued, pinned, acquired, returned, pinnedPhase, localToken, sequence, active, guarded⟩ :=
    supported snapshot floor committed
  obtain ⟨after, exactSession, continued⟩ :=
    trace.observeSnapshotUpdate (.acquireAt snapshot) phase returned
  have readyAfter : acquired.phase = .ready after.installed := congrArg SegmentedSession.phase exactSession
  have sameTable : after.installed.table = pinned :=
    congrArg Installed.table (Phase.ready.inj (readyAfter.symm.trans pinnedPhase))
  have sameDirectory : acquired.directory = session.directory := by rw [exactSession]
  have sameDescriptor : acquired.descriptor = session.descriptor := by rw [exactSession]
  refine ⟨reference, issued, acquired, after, replayed, preceding, returned, localToken, sequence, exactSession, ?_⟩
  intro sameSession compared α request
  let pin : ObservedLocalPin session.directory session.descriptor after :=
    ⟨⟨acquired, sameDirectory, sameDescriptor, readyAfter, issued.1, sameSession, compared⟩,
      issued.2, sameTable.symm ▸ active, localToken⟩
  obtain ⟨lookup, range⟩ := guarded sameSession compared
  cases request with
  | lookup key =>
    have actual := runSnapshotRead_of_guarded pinnedPhase (fun table => table.lookup issued.2.handle key) (lookup key)
    have observed : RecordedSnapshotRead.Observed session.directory session.descriptor after
        (.lookup issued.2.sequence key (reference.table.lookup key snapshot)) := .lookup pin actual
    refine ⟨actual, ?_⟩
    simpa only [SnapshotReadRequest.record, SnapshotReadRequest.replay, sequence] using continued.read observed
  | range lo hi =>
    have actual := runSnapshotRead_of_guarded pinnedPhase (fun table => table.range issued.2.handle lo hi) (range lo hi)
    have observed : RecordedSnapshotRead.Observed session.directory session.descriptor after
        (.range issued.2.sequence lo hi (reference.table.range lo hi snapshot)) := .range pin actual
    refine ⟨actual, ?_⟩
    simpa only [SnapshotReadRequest.record, SnapshotReadRequest.replay, sequence] using continued.read observed

end Alvoki.Storage.DiskSession
