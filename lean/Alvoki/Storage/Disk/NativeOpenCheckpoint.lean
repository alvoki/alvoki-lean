import Alvoki.Storage.Disk.NativeOpenAcquire
import Alvoki.Storage.Disk.NativeReadyCheckpoint

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication

variable {heap : Type}

private def phaseEffect {files α : Type} (action : EStateM IO.Error heap α) :
    EStateM IO.Error (heap × files) α :=
  fun (heap, files) => match action heap with
    | .ok result after => .ok result (after, files)
    | .error cause after => .error cause (after, files)

private def fileEffect {files α : Type} (action : EStateM IO.Error files α) :
    EStateM IO.Error (heap × files) α :=
  fun (heap, files) => match action files with
    | .ok result after => .ok result (heap, after)
    | .error cause after => .error cause (heap, after)

private theorem fileEffects_forM {files : Type} (steps : List Step)
    (perform : Step → EStateM IO.Error files Unit) (entry : heap × files) :
    (steps.forM (fun step => fileEffect (perform step))) entry =
      fileEffect (steps.forM perform) entry := by
  induction steps generalizing entry with
  | nil => rfl
  | cons step remaining ih =>
    obtain ⟨heap, files⟩ := entry
    change EStateM.bind (fileEffect (perform step))
      (fun _ => remaining.forM (fun step => fileEffect (perform step))) (heap, files) = _
    change _ = fileEffect (EStateM.bind (perform step) (fun _ => remaining.forM perform)) (heap, files)
    cases ran : perform step files with
    | ok value after =>
      simpa only [EStateM.bind, fileEffect, ran] using ih (heap, after)
    | error cause after =>
      simp only [EStateM.bind, fileEffect, ran]

/-- An observed rejected checkpoint stops before any phase update or
publication callback, including from a closed or poisoned opened cell. -/
theorem CheckpointPreflight.rejectsFromOpenCell {files : Type} {phase : Phase Installed} {cause : IO.Error}
    (preflight : CheckpointPreflight phase (.error cause))
    {db : DiskTable} {directory : DiskDirectory} {lock : IO.FS.Handle} {syncFiles : DiskTable.OpenSyncFiles}
    {reference : IO.Ref (Phase Installed)} {token : IO.Ref Unit}
    (uses : db.UsesOpenReferences directory lock syncFiles reference token)
    (get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)) {entry : heap}
    (read : get reference entry = .ok phase entry) (atEntry : files)
    (publish : Installed → ByteArray → EStateM IO.Error (heap × files) Unit) :
    db.UsesOpenCheckpointSchedule directory syncFiles reference ∧
    withPreparedCheckpoint (do (← phaseEffect (get reference)).installed)
      liftCheckpointExcept publish (entry, atEntry) = .error cause (entry, atEntry) := by
  refine ⟨uses.checkpoint, ?_⟩
  apply preflight.preparesFrom
  simp only [phaseEffect, Bind.bind, EStateM.bind, read]

/-- Checkpoint returns through the same phase cell stored by the native
opener. Its reported cached file steps select the exact checkpoint
before the final setter stores the reached ready writer in that cell. -/
theorem NativeReadPosition.checkpointsViaOpenReferences {history log image}
    (current : NativeReadPosition history log) (db : DiskTable)
    {lock : IO.FS.Handle} {files : DiskTable.OpenSyncFiles} {phase : IO.Ref (Phase Installed)} {token : IO.Ref Unit}
    (uses : db.UsesOpenReferences current.state.session.directory lock files phase token)
    {contents : heap → IO.Ref (Phase Installed) → Option (Phase Installed)}
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (effects : OpenPhaseCellEffects contents get set) {entry : heap}
    (stored : contents entry phase = some current.state.session.phase)
    {attempt : SegmentedCheckpointReport current.state.session.directory current.state.writer}
    {reports : CheckpointCompletionReports (CensusDirectoryCache × image) attempt}
    (observed : NativeReadyCheckpoint current.state reports) :
    let before := current.state
    let directory := before.session.directory
    let load : EStateM IO.Error (heap × (CensusDirectoryCache × image)) Installed := do
      (← phaseEffect (get phase)).installed
    let setPhase := fun value => phaseEffect (set phase value)
    let checkpoint := withPreparedCheckpoint load liftCheckpointExcept (fun next manifest =>
      publishPrepared setPhase
        (CheckpointPublication.run next.table.runs.length
          (fun step => fileEffect (observed.primitives.cached.perform directory next manifest step)))
        (setPhase (.ready next)))
    db.UsesOpenCheckpointSchedule directory files phase ∧
    ∃ writer, ∃ poisoned reached : heap,
      get phase entry = .ok before.session.phase entry ∧
      set phase .poisoned entry = .ok () poisoned ∧ contents poisoned phase = some .poisoned ∧
      set phase (.ready writer.installed) poisoned = .ok () reached ∧
      contents reached phase = some (observed.next writer).session.phase ∧
      checkpoint (entry, before.cache, (reports.observed.atRun 0).2) =
        .ok () (reached, reports.observed.completed) ∧
      observed.Completed writer ∧ writer.history = history ∧
      db.UsesOpenReferences (observed.next writer).session.directory lock files phase token ∧
      InstalledClientReplay log current.reads history writer.installed (observed.next writer).session := by
  intro before directory load setPhase checkpoint
  obtain ⟨writer, completed, history, replay⟩ := current.readPrefix.checkpoints observed
  have loaded := effects.reads entry phase before.session.phase stored
  obtain ⟨poisoned, excluded, poisonedPhase⟩ := effects.writes entry phase before.session.phase .poisoned stored
  obtain ⟨reached, installed, readyPhase⟩ := effects.writes poisoned phase .poisoned (.ready writer.installed) poisonedPhase
  refine ⟨uses.checkpoint, writer, poisoned, reached, loaded, excluded, poisonedPhase, installed, readyPhase, ?_,
    completed, history, uses, replay⟩
  have preflight : CheckpointPreflight before.session.phase (.ok (attempt.prepared, attempt.manifest)) := by
    rw [current.readPrefix.refines.1.phase]
    exact reports.preflight
  have same : load (entry, before.cache, (reports.observed.atRun 0).2) =
      before.session.phase.installed (m := EStateM IO.Error _) (entry, before.cache, (reports.observed.atRun 0).2) := by
    simp only [load, phaseEffect, Bind.bind, EStateM.bind, loaded]
  dsimp only [checkpoint]
  rw [preflight.preparesFrom _ same]
  have published : CheckpointPublication.run attempt.prepared.table.runs.length
        (observed.primitives.cached.perform directory attempt.prepared attempt.manifest)
        (before.cache, (reports.observed.atRun 0).2) = .ok () reports.observed.completed := by
    have atRun : (before.cache, (reports.observed.atRun 0).2) = reports.observed.atRun 0 := by
      rw [← observed.initialCache]
    rw [atRun]
    have dispatch : reports.callbacks.perform directory attempt.prepared attempt.manifest =
        observed.primitives.cached.perform directory attempt.prepared attempt.manifest :=
      congrArg (fun calls => calls.perform directory attempt.prepared attempt.manifest) observed.callbacks
    rw [← dispatch]
    exact reports.observed.returns
  have kept : CheckpointPublication.run attempt.prepared.table.runs.length
      (fun step => fileEffect (observed.primitives.cached.perform directory attempt.prepared attempt.manifest step))
      (poisoned, before.cache, (reports.observed.atRun 0).2) = .ok () (poisoned, reports.observed.completed) := by
    unfold CheckpointPublication.run
    rw [fileEffects_forM]
    change fileEffect (CheckpointPublication.run attempt.prepared.table.runs.length
      (observed.primitives.cached.perform directory attempt.prepared attempt.manifest))
      (poisoned, before.cache, (reports.observed.atRun 0).2) = _
    simp only [fileEffect, published]
  have installPrepared : set phase (.ready attempt.prepared) poisoned = .ok () reached := by
    rw [← completed.installed]
    exact installed
  simp only [publishPrepared, Bind.bind, EStateM.bind, setPhase, phaseEffect, excluded, kept, installPrepared]

end Alvoki.Storage.DiskSession
