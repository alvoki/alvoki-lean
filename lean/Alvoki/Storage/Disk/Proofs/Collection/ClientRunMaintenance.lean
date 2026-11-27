import Alvoki.Storage.Proofs.Table.PackedTableCompaction
import Alvoki.Storage.Disk.Proofs.Read.ClientReadTrace

namespace Alvoki.Storage.DiskSession

/-- The public in-memory rewrites both act on the current ready table. -/
inductive RunMaintenance where
  | compact (index : Nat)
  | retainRunVersions (index : Nat)

def RunMaintenance.update : RunMaintenance → PackedTable → Option PackedTable
  | .compact index => fun table => table.compact index
  | .retainRunVersions index => fun table => table.retainRunVersions index

def RunMaintenance.run (request : RunMaintenance) : EStateM IO.Error SegmentedSession Bool := fun session =>
  rewriteRunWith (m := EStateM IO.Error SegmentedSession) session.phase.installed
    (fun phase state => .ok () { state with phase }) request.update session

/-- An unavailable phase returns its original error. A rejected ready
rewrite returns false, while a successful one changes only the phase's table. -/
theorem RunMaintenance.outcome (request : RunMaintenance) (session : SegmentedSession) :
    request.run session =
      match session.phase with
      | .closed => .error (IO.userError "database is closed") session
      | .poisoned => .error (IO.userError "publication failed; reopen the database") session
      | .ready installed =>
        match request.update installed.table with
        | none => .ok false session
        | some table => .ok true { session with phase := .ready { installed with table } } := by
  cases phase : session.phase with
  | closed => rw [RunMaintenance.run, phase]; rfl
  | poisoned => rw [RunMaintenance.run, phase]; rfl
  | ready installed =>
    cases rewritten : request.update installed.table <;>
      simp [RunMaintenance.run, rewriteRunWith, phase, Phase.installed, rewritten,
        Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]

theorem RunMaintenance.update_spec (request : RunMaintenance) {before after : PackedTable}
    (updated : request.update before = some after) :
    SegmentedTableStep before after ∧ after.committed = before.committed ∧ after.pins = before.pins := by
  cases request with
  | compact _ =>
    have spec := PackedTable.compact_spec updated
    exact ⟨.compact updated, spec.2.1, spec.2.2.1⟩
  | retainRunVersions _ =>
    have spec := PackedTable.retainRunVersions_spec updated
    exact ⟨.retainRunVersions updated, spec.2.1, spec.2.2.1⟩

/-- Feed the same table returned by either native schedule into the client
trace. The successor keeps the original files, lock, WAL and pin identities.
A rejected rewrite leaves the full reached session and earlier trace available. -/
theorem SegmentedClientReadTrace.observeRunMaintenance
    {session : SegmentedSession} {before : SegmentedWriterState}
    (trace : SegmentedClientReadTrace session.directory initialDescriptor initial allowCollection log reads
      session.descriptor before)
    (request : RunMaintenance) (phase : session.phase = .ready before.installed) :
    match request.update before.installed.table with
    | none => request.run session = .ok false session
    | some table =>
      let after := before.withTable table
      request.run session = .ok true { session with phase := .ready after.installed } ∧
        table.committed = before.installed.table.committed ∧ table.pins = before.installed.table.pins ∧
        SegmentedClientReadTrace session.directory initialDescriptor initial allowCollection log reads
          session.descriptor after := by
  have result := request.outcome session
  rw [phase] at result
  cases updated : request.update before.installed.table with
  | none => simpa only [updated] using result
  | some table =>
    obtain ⟨step, clock, pins⟩ := request.update_spec updated
    refine ⟨?_, clock, pins, ?_⟩
    · simpa only [updated, SegmentedWriterState.withTable] using result
    · simpa only [List.append_nil] using trace.advance (.table .start step)

end Alvoki.Storage.DiskSession
