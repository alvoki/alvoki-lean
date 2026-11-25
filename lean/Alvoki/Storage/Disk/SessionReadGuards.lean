import Alvoki.Storage.Disk.MarkedDatabaseTrace
import Alvoki.Storage.Disk.SegmentedSessionInstall

namespace Alvoki.Storage.DiskSession

open Sequential (SnapshotHandle SnapshotPin)

/-- Interpret snapshot acquisition with the reached ready cell and its
session identity from the reference allocation report. -/
def SegmentedSession.runAcquireAt (snapshot : UInt64) :
    EStateM IO.Error SegmentedSession (Option (Nat × SnapshotPin)) := fun session =>
  acquireSnapshotWith (m := EStateM IO.Error SegmentedSession) session.phase.installed
    (fun phase state => .ok () { state with phase })
    (fun pin => (session.sessionRef, pin)) snapshot session

/-- A supported pin carries the issuing session's token. Acquisition
updates that same ready cell and preserves its allocation identity. -/
theorem SegmentedSession.runAcquireAt_ready {session : SegmentedSession} {installed : Installed}
    (phase : session.phase = .ready installed) {snapshot : UInt64} {pin : SnapshotPin} {table : PackedTable}
    (acquired : installed.table.acquireAt snapshot = some (pin, table)) :
    SegmentedSession.runAcquireAt snapshot session =
      .ok (some (session.sessionRef, pin)) { session with phase := .ready { installed with table } } := by
  simp only [SegmentedSession.runAcquireAt, acquireSnapshotWith, phase, Phase.installed, Bind.bind, EStateM.bind,
    Pure.pure, EStateM.pure, acquired]

/-- A request outside the supported interval leaves the ready session unchanged. -/
theorem SegmentedSession.runAcquireAt_unsupported {session : SegmentedSession} {installed : Installed}
    (phase : session.phase = .ready installed) {snapshot : UInt64}
    (unsupported : ¬ (installed.table.pins.floor ≤ snapshot ∧ snapshot ≤ installed.table.committed)) :
    SegmentedSession.runAcquireAt snapshot session = .ok none session := by
  have absent : installed.table.pins.acquire installed.table.committed snapshot = none := by
    cases acquired : installed.table.pins.acquire installed.table.committed snapshot with
    | none => rfl
    | some found =>
      exact False.elim (unsupported ((installed.table.pins.acquire_iff _ _).mp (by rw [acquired]; rfl)))
  simp [SegmentedSession.runAcquireAt, acquireSnapshotWith, phase, Phase.installed, Bind.bind, EStateM.bind,
    Pure.pure, EStateM.pure, PackedTable.acquireAt, absent]

/-- Interpret both phase reads in latest acquisition. In a sequential
session the first read observes the same cell used by `runAcquireAt`. -/
def SegmentedSession.runAcquire : EStateM IO.Error SegmentedSession (Nat × SnapshotPin) :=
  fun session => acquireLatestWith (m := EStateM IO.Error SegmentedSession)
    session.phase.installed SegmentedSession.runAcquireAt session

theorem SegmentedSession.runAcquire_of_acquireAt {session after : SegmentedSession}
    {installed : Installed} (ready : session.phase = .ready installed) {pin : SnapshotPin}
    (acquired : session.runAcquireAt installed.table.committed = .ok (some (session.sessionRef, pin)) after) :
    session.runAcquire = .ok (session.sessionRef, pin) after := by
  simp only [SegmentedSession.runAcquire, acquireLatestWith, ready, Phase.installed, Bind.bind,
    EStateM.bind, Pure.pure, EStateM.pure, acquired]

/-- Interpret the native release schedule with the reached session and the
observed token comparison. Only the phase cell can change. -/
def SegmentedSession.runRelease (sameSession : Bool) (handle : SnapshotHandle) :
    EStateM IO.Error SegmentedSession Unit := fun session =>
  releaseSnapshotWith (m := EStateM IO.Error SegmentedSession) session.phase.installed (pure sameSession)
    (fun phase state => .ok () { state with phase }) handle session

theorem SegmentedSession.runRelease_ready {session : SegmentedSession} {installed : Installed}
    (phase : session.phase = .ready installed) (handle : SnapshotHandle)
    {sameSession : Bool} {issuer : Nat} (compared : sameSession = decide (issuer = session.sessionRef)) :
    SegmentedSession.runRelease sameSession handle session = .ok ()
      (if issuer = session.sessionRef then
        { session with phase := .ready { installed with table := installed.table.release handle } }
      else session) := by
  by_cases localToken : issuer = session.sessionRef <;>
    simp [SegmentedSession.runRelease, releaseSnapshotWith, withLocalHandle, phase, Phase.installed,
      compared, localToken, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]

/-- Interpret the same phase and handle decisions used by `DiskTable.lookup`
and `DiskTable.range` after observing the native pointer comparison. -/
def readWithHandle (phase : Phase PackedTable) (sameSession : Bool)
    (read : PackedTable → Option α) : Except IO.Error (Option α) :=
  withLocalHandle phase.installed (.ok sameSession) none (fun table => pure (read table))

theorem withLocalHandle_closed (sameSession : Except IO.Error Bool) (foreign : β)
    (use : α → Except IO.Error β) :
    withLocalHandle (Phase.closed : Phase α).installed sameSession foreign use =
      .error (IO.userError "database is closed") := rfl

theorem withLocalHandle_poisoned (sameSession : Except IO.Error Bool) (foreign : β)
    (use : α → Except IO.Error β) :
    withLocalHandle (Phase.poisoned : Phase α).installed sameSession foreign use =
      .error (IO.userError "publication failed; reopen the database") := rfl

/-- The allocation-identity assumption interprets the actual `ST.Ref.ptrEq`
result for the issuing and current live session tokens. Even a reused local
pin number is rejected when those tokens differ. -/
theorem readWithHandle_foreign (table : PackedTable) (read : PackedTable → Option α)
    {sameSession : Bool} {issuer current : Nat}
    (compared : sameSession = decide (issuer = current)) (foreign : issuer ≠ current) :
    readWithHandle (.ready table) sameSession read = .ok none := by
  have different : sameSession = false := compared.trans (decide_eq_false foreign)
  rw [different]
  rfl

/-- Each token still held from an earlier session is foreign to the
installed result of the shared open. The allocation report covers all live
tokens, and the comparison report interprets the native pointer check. -/
theorem runOpenWithInstallation_rejectsLiveToken {image : Type} {directory descriptor nextRef acquired unlock}
    {recover : EStateM IO.Error image WalSegmentRepair.Reopened} {before final : LockedFileState image}
    {session : SegmentedSession}
    (opened : runOpenWithInstallation directory descriptor nextRef acquired unlock recover before = .ok session final)
    (liveRefs : List Nat) (fresh : ∀ ref ∈ liveRefs, ref < nextRef) {issuer : Nat}
    (oldToken : issuer ∈ liveRefs) {sameSession : Bool}
    (compared : sameSession = decide (issuer = session.sessionRef)) (read : PackedTable → Option α) :
    ∃ installed, session.phase = .ready installed ∧
      readWithHandle (.ready installed.table) sameSession read = .ok none := by
  rw [runOpenWithInstallation_outcome] at opened
  cases result : runOpenWithImage directory descriptor acquired unlock recover before with
  | error cause after => simp [result] at opened
  | ok recovered after =>
    rw [result] at opened
    obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj opened
    have old := fresh issuer oldToken
    have distinct : issuer ≠ nextRef + 1 := by omega
    exact ⟨recovered.installed, rfl, readWithHandle_foreign _ read compared distinct⟩

/-- The foreign release branch does not invoke the local state update. -/
theorem release_foreign {sameSession : Bool} {issuer current : Nat}
    (compared : sameSession = decide (issuer = current)) (foreign : issuer ≠ current)
    (table : PackedTable) (phase : σ) (release : PackedTable → EStateM IO.Error σ Unit) :
    withLocalHandle (pure table) (pure sameSession) () release phase = .ok () phase := by
  have different : sameSession = false := compared.trans (decide_eq_false foreign)
  rw [different]
  rfl

theorem readWithHandle_inactive (table : PackedTable) (sameSession : Bool) (handle : SnapshotHandle)
    (missing : table.pins.find handle = none) :
    (∀ key, readWithHandle (.ready table) sameSession (fun data => data.lookup handle key) = .ok none) ∧
    ∀ start stop, readWithHandle (.ready table) sameSession (fun data => data.range handle start stop) =
      .ok none := by
  cases sameSession
  · exact ⟨fun _ => rfl, fun _ _ => rfl⟩
  · constructor
    · intro key
      change Except.ok (table.lookup handle key) = .ok none
      simp only [PackedTable.lookup, missing, Option.map_none]
    · intro start stop
      change Except.ok (table.range handle start stop) = .ok none
      simp only [PackedTable.range, missing, Option.map_none]

/-- Releasing a local handle keeps the data and floor, removes precisely
that handle from the active registry, and makes its guarded reads inactive. -/
theorem SegmentedSession.runRelease_local {session : SegmentedSession} {installed : Installed}
    (phase : session.phase = .ready installed) (handle : SnapshotHandle)
    {sameSession : Bool} {issuer : Nat} (compared : sameSession = decide (issuer = session.sessionRef))
    (localToken : issuer = session.sessionRef) :
    let table := installed.table.release handle
    let next := { session with phase := .ready { installed with table } }
    SegmentedSession.runRelease sameSession handle session = .ok () next ∧
    table.SameData installed.table ∧
    (∀ pin, pin ∈ table.pins.active ↔ pin ∈ installed.table.pins.active ∧ pin.handle ≠ handle) ∧
    (∀ key, readWithHandle (.ready table) sameSession (fun data => data.lookup handle key) = .ok none) ∧
    ∀ start stop, readWithHandle (.ready table) sameSession (fun data => data.range handle start stop) =
      .ok none := by
  refine ⟨?_, ⟨rfl, rfl, rfl, rfl⟩, installed.table.pins.mem_release handle, ?_⟩
  · simpa [localToken] using SegmentedSession.runRelease_ready phase handle compared
  · exact readWithHandle_inactive _ _ _ (installed.table.pins.find_released handle)

/-- Other active handles continue to read at the same sequences immediately
after the local release. -/
theorem SegmentedSession.runRelease_preservesReads {session : SegmentedSession} {installed : Installed}
    (phase : session.phase = .ready installed) (handle : SnapshotHandle)
    {sameSession : Bool} {issuer : Nat} (compared : sameSession = decide (issuer = session.sessionRef))
    (localToken : issuer = session.sessionRef) {pin : SnapshotPin}
    (active : pin ∈ installed.table.pins.active) (distinct : pin.handle ≠ handle) :
    let table := installed.table.release handle
    let next := { session with phase := .ready { installed with table } }
    SegmentedSession.runRelease sameSession handle session = .ok () next ∧
    (∀ key, readWithHandle (.ready table) sameSession (fun data => data.lookup pin.handle key) =
      readWithHandle (.ready installed.table) sameSession (fun data => data.lookup pin.handle key)) ∧
    ∀ start stop, readWithHandle (.ready table) sameSession (fun data => data.range pin.handle start stop) =
      readWithHandle (.ready installed.table) sameSession (fun data => data.range pin.handle start stop) := by
  dsimp only
  obtain ⟨released, same, kept, _⟩ := SegmentedSession.runRelease_local phase handle compared localToken
  have before := installed.table.pins.find_of_mem active
  have after := (installed.table.release handle).pins.find_of_mem ((kept pin).mpr ⟨active, distinct⟩)
  have sameSession' : sameSession = true := compared.trans (decide_eq_true localToken)
  refine ⟨released, fun key => ?_, fun start stop => ?_⟩
  · rw [sameSession']
    change Except.ok ((installed.table.release handle).lookup pin.handle key) =
      Except.ok (installed.table.lookup pin.handle key)
    simp only [PackedTable.lookup, before, after, Option.map_some, PackedTable.lookupAt_eq, same.describe]
  · rw [sameSession']
    change Except.ok ((installed.table.release handle).range pin.handle start stop) =
      Except.ok (installed.table.range pin.handle start stop)
    simp only [PackedTable.range, before, after, Option.map_some, PackedTable.rangeAt_eq, same.describe]

end Alvoki.Storage.DiskSession

namespace Alvoki.WAL.Boundary

open Storage
open Sequential (SnapshotPin SnapshotTable)

/-- An active pin belonging to the installed session reads the canonical
durable WAL at its recorded sequence, using the same guard as the adapter. -/
theorem ObservedMarkedState.Valid.guardedPinnedReads {state : ObservedMarkedState} (valid : state.Valid)
    {reference : SnapshotTable UInt64} (replayed : SnapshotWalReplay .empty state.writer.history reference)
    {pin : SnapshotPin} (active : pin ∈ state.writer.table.pins.active)
    {sameSession : Bool} {issuer current : Nat}
    (compared : sameSession = decide (issuer = current)) (localHandle : issuer = current) :
    (∀ key, DiskSession.readWithHandle (.ready state.writer.table) sameSession
      (fun table => table.lookup pin.handle key) = .ok (some (reference.table.lookup key pin.sequence))) ∧
    ∀ start stop, DiskSession.readWithHandle (.ready state.writer.table) sameSession
      (fun table => table.range pin.handle start stop) = .ok (some (reference.table.range start stop pin.sequence)) := by
  have same : sameSession = true := compared.trans (decide_eq_true localHandle)
  rw [same]
  obtain ⟨lookup, range⟩ := valid.pinnedReads replayed active
  exact ⟨fun key => congrArg Except.ok (lookup key),
    fun start stop => congrArg Except.ok (range start stop)⟩

end Alvoki.WAL.Boundary
