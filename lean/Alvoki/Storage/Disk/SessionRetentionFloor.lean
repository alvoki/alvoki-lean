import Alvoki.Storage.Disk.SessionReadGuards
import Alvoki.Storage.Disk.SegmentedWriterMaintenance

namespace Alvoki.Storage.DiskSession

open Sequential (SnapshotHandle SnapshotPins)

/-- Run the native retention-floor schedule over the installed phase cell. -/
def SegmentedSession.runAdvanceFloor (floor : UInt64) : EStateM IO.Error SegmentedSession Bool :=
  fun session => advanceFloorWith (m := EStateM IO.Error SegmentedSession) session.phase.installed
    (fun phase state => .ok () { state with phase }) floor session

theorem SegmentedSession.runAdvanceFloor_ready {session : SegmentedSession} {installed : Installed}
    (phase : session.phase = .ready installed) (floor : UInt64) :
    SegmentedSession.runAdvanceFloor floor session =
      match installed.table.advanceFloor floor with
      | none => .ok false session
      | some table => .ok true { session with phase := .ready { installed with table } } := by
  cases moved : installed.table.advanceFloor floor <;>
    simp [SegmentedSession.runAdvanceFloor, advanceFloorWith, phase, Phase.installed, moved,
      Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]

/-- A backward move, a move past a live pin, or a move past the committed
sequence leaves the whole ready session unchanged. -/
theorem SegmentedSession.runAdvanceFloor_blocked {session : SegmentedSession} {installed : Installed}
    (phase : session.phase = .ready installed) {floor : UInt64}
    (blocked : ¬ (floor ≤ installed.table.committed ∧ installed.table.pins.floor ≤ floor ∧
      ∀ pin ∈ installed.table.pins.active, floor ≤ pin.sequence)) :
    SegmentedSession.runAdvanceFloor floor session = .ok false session := by
  rw [SegmentedSession.runAdvanceFloor_ready phase]
  by_cases through : floor ≤ installed.table.committed
  · cases pins : installed.table.pins.advance floor with
    | none => simp [PackedTable.advanceFloor, through, pins]
    | some updated => exact False.elim (blocked ⟨through,
        (installed.table.pins.advance_iff floor).mp (by simp [pins])⟩)
  · simp [PackedTable.advanceFloor, through]

/-- Advancing the floor leaves the exact registered handles and rows in place.
The guarded reads agree for every handle, including foreign and inactive ones. -/
theorem SegmentedSession.runAdvanceFloor_preservesReads {session : SegmentedSession} {installed : Installed}
    (phase : session.phase = .ready installed) {floor : UInt64} {table : PackedTable}
    (advanced : installed.table.advanceFloor floor = some table) :
    SegmentedSession.runAdvanceFloor floor session =
      .ok true { session with phase := .ready { installed with table } } ∧
    table.pins.floor = floor ∧ installed.table.pins.floor ≤ floor ∧ floor ≤ table.committed ∧
    table.pins.active = installed.table.pins.active ∧ table.pins.nextHandle = installed.table.pins.nextHandle ∧
    ∀ (sameSession : Bool) (handle : SnapshotHandle),
      (∀ key, readWithHandle (.ready table) sameSession (fun data => data.lookup handle key) =
        readWithHandle (.ready installed.table) sameSession (fun data => data.lookup handle key)) ∧
      ∀ start stop, readWithHandle (.ready table) sameSession (fun data => data.range handle start stop) =
        readWithHandle (.ready installed.table) sameSession (fun data => data.range handle start stop) := by
  have moved := SegmentedSession.runAdvanceFloor_ready phase floor
  rw [advanced] at moved
  unfold PackedTable.advanceFloor at advanced
  split at advanced
  · rename_i through
    obtain ⟨updated, changed, installedTable⟩ := Option.map_eq_some_iff.mp advanced
    obtain ⟨monotone, exactFloor, active, nextHandle, _⟩ := SnapshotPins.advance_spec changed
    have registered : table.pins = updated := congrArg PackedTable.pins installedTable.symm
    have sameData : table.describe = installed.table.describe := by
      rw [← installedTable]
      rfl
    have committed : table.committed = installed.table.committed := by rw [← installedTable]
    refine ⟨moved, registered ▸ exactFloor, exactFloor ▸ monotone, committed ▸ through,
      registered ▸ active, registered ▸ nextHandle, ?_⟩
    intro sameSession handle
    have pins : table.pins.find handle = installed.table.pins.find handle := by
      simp only [registered, SnapshotPins.find, active]
    cases sameSession
    · exact ⟨fun _ => rfl, fun _ _ => rfl⟩
    · constructor
      · intro key
        change Except.ok (table.lookup handle key) = Except.ok (installed.table.lookup handle key)
        simp only [PackedTable.lookup, pins, PackedTable.lookupAt_eq, sameData]
      · intro start stop
        change Except.ok (table.range handle start stop) = Except.ok (installed.table.range handle start stop)
        simp only [PackedTable.range, pins, PackedTable.rangeAt_eq, sameData]
  · contradiction

/-- The ready phase returned after a permitted floor move is the same
writer in the retained-history model, with the same checkpoint and WAL. -/
theorem SegmentedSession.runAdvanceFloor_retained {session : SegmentedSession} {before : SegmentedWriterState}
    (phase : session.phase = .ready before.installed)
    (ready : before.RetainedReady session.directory session.descriptor)
    {floor : UInt64} {table : PackedTable}
    (advanced : before.installed.table.advanceFloor floor = some table) :
    SegmentedSession.runAdvanceFloor floor session =
      .ok true { session with phase := .ready (before.withTable table).installed } ∧
    (before.withTable table).RetainedReady session.directory session.descriptor := by
  have returned := SegmentedSession.runAdvanceFloor_ready phase floor
  rw [advanced] at returned
  exact ⟨returned, (SegmentedTableStep.advanceFloor advanced).preservesRetained ready⟩

end Alvoki.Storage.DiskSession
