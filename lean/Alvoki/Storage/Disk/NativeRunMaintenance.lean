import Alvoki.Storage.Disk.NativeReadRecoveryTrace

namespace Alvoki.Storage.DiskSession

/-- The native run rewrite returns at the reached session. Its exact
outcome selects the new table or the unchanged position. Disk custody,
open anchor, snapshot pins and previously recorded reads are preserved. -/
structure NativeRunMaintenanceStep (current : NativeReadPosition history log) (request : RunMaintenance)
    (result : Bool) (next : NativeReadPosition history log) : Prop where
  returned : request.run current.state.session = .ok result next.state.session
  reached : match request.update current.state.writer.installed.table with
    | none => result = false ∧ next = current
    | some table => result = true ∧ next.state = current.state.withTable table
  opened : next.opened = current.opened
  initial : next.initial = current.initial
  files : next.state.files = current.state.files
  cache : next.state.cache = current.state.cache
  census : next.state.census = current.state.census
  owner : next.state.owner = current.state.owner
  directory : next.state.directorySlot = current.state.directorySlot
  sessionRef : next.state.session.sessionRef = current.state.session.sessionRef
  phaseRef : next.state.session.phaseRef = current.state.session.phaseRef
  committed : next.state.writer.installed.table.committed = current.state.writer.installed.table.committed
  pins : next.state.writer.installed.table.pins = current.state.writer.installed.table.pins
  reads : next.reads = current.reads

/-- Both public rewrite operations use the same native schedule. The
ready prefix continues from its exact result and retains one replay
through successful rewrites and rejected indexes. -/
theorem NativeReadPosition.rewritesRun (current : NativeReadPosition history log) (request : RunMaintenance) :
    ∃ result next, NativeRunMaintenanceStep current request result next := by
  have ran := request.outcome current.state.session
  rw [current.readPrefix.refines.1.phase] at ran
  cases rewritten : request.update current.state.writer.installed.table with
  | none =>
    refine ⟨false, current, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · simpa only [rewritten] using ran
    · rw [rewritten]
      exact ⟨rfl, rfl⟩
  | some table =>
    have returned : request.run current.state.session = .ok true (current.state.withTable table).session := by
      simpa only [rewritten, NativeReadyState.withTable] using ran
    obtain ⟨_, committed, pins⟩ := request.update_spec rewritten
    let next : NativeReadPosition history log := { current with
      state := current.state.withTable table
      readPrefix := .rewriteRun request current.readPrefix returned rewritten }
    refine ⟨true, next, returned, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, committed, pins, rfl⟩
    rw [rewritten]
    exact ⟨rfl, rfl⟩

end Alvoki.Storage.DiskSession
