import Alvoki.Storage.Disk.MarkedDatabaseTrace

namespace Alvoki.Storage.DiskSession

open Sequential (SnapshotHandle SnapshotPin)

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
