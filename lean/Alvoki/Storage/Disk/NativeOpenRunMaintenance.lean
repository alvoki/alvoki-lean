import Alvoki.Storage.Disk.NativeOpenedPosition

namespace Alvoki.Storage.DiskSession

/-- The public operation corresponding to a run rewrite request. -/
def RunMaintenance.publicCall (request : RunMaintenance) (db : DiskTable) : IO Bool :=
  match request with
  | .compact index => db.compact index
  | .retainRunVersions index => db.retainRunVersions index

theorem _root_.Alvoki.Storage.DiskTable.UsesOpenReferences.rewriteRun {db : DiskTable} {directory lock files phase token}
    (uses : db.UsesOpenReferences directory lock files phase token) (request : RunMaintenance) :
    request.publicCall db = rewriteRunWith (m := IO) (do (← phase.get).installed) phase.set request.update := by
  obtain ⟨_, _, _, cell, _⟩ := uses
  rw [← cell]
  cases request with
  | compact index => exact db.compact_schedule index
  | retainRunVersions index => exact db.retainRunVersions_schedule index

variable {heap : Type} {opened : NativeOpenedHandle heap}

/-- The public rewrite uses the same table guard as the native step.
A refusal keeps the phase heap. A successful rewrite stores the exact
next table in the original opened cell. -/
theorem NativeOpenedPosition.rewritesRunViaOpenReferences
    (start : NativeOpenedPosition opened) (request : RunMaintenance) :
    request.publicCall opened.table = rewriteRunWith (m := IO) (do (← opened.phase.get).installed)
      opened.phase.set request.update ∧
    ∃ (result : Bool) (next : NativeReadPosition start.current.history start.current.submissions) (reached : heap),
      NativeRunMaintenanceStep start.current.ready request result next ∧
      rewriteRunWith (m := EStateM IO.Error heap) (do (← opened.get opened.phase).installed)
        (opened.set opened.phase) request.update start.reached = .ok result reached ∧
      opened.contents reached opened.phase = some next.state.session.phase ∧
      next.state.session.directory = opened.directory ∧
      (result = false → reached = start.reached) ∧
      (result = true → opened.set opened.phase next.state.session.phase start.reached = .ok () reached) := by
  refine ⟨start.uses.rewriteRun request, ?_⟩
  obtain ⟨result, next, returned⟩ := start.current.ready.rewritesRun request
  let state := start.current.ready.state
  have ready := start.current.ready.readPrefix.refines.1.phase
  have loaded := opened.phaseEffects.reads _ _ _ start.stored
  have outcome := returned.reached
  change (match request.update state.writer.installed.table with
    | none => result = false ∧ next = start.current.ready
    | some table => result = true ∧ next.state = state.withTable table) at outcome
  cases rewritten : request.update state.writer.installed.table with
  | none =>
    rw [rewritten] at outcome
    obtain ⟨rfl, rfl⟩ := outcome
    refine ⟨false, start.current.ready, start.reached, returned, ?_, start.stored, start.directory, fun _ => rfl, by simp⟩
    simp only [state] at rewritten
    simp only [rewriteRunWith, Bind.bind, EStateM.bind, loaded, ready, Phase.installed, Pure.pure, EStateM.pure,
      rewritten]
  | some table =>
    rw [rewritten] at outcome
    obtain ⟨rfl, sameState⟩ := outcome
    let updated := Phase.ready { state.writer.installed with table }
    obtain ⟨reached, wrote, stored⟩ := opened.phaseEffects.writes _ _ _ updated start.stored
    have phase : next.state.session.phase = updated := congrArg (fun value : NativeReadyState => value.session.phase) sameState
    have directory : next.state.session.directory = opened.directory :=
      (congrArg (fun value : NativeReadyState => value.session.directory) sameState).trans start.directory
    refine ⟨true, next, reached, returned, ?_, phase.symm ▸ stored, directory, by simp, fun _ => phase.symm ▸ wrote⟩
    simp only [state] at rewritten
    simp only [updated, state] at wrote
    simp only [rewriteRunWith, Bind.bind, EStateM.bind, loaded, ready, Phase.installed, Pure.pure, EStateM.pure,
      rewritten, wrote]

end Alvoki.Storage.DiskSession
