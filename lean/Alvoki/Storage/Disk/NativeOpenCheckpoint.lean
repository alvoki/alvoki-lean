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

/-- The exact return of the production checkpoint schedule with its
opened phase cell and the reached cached file step reports. -/
def NativeReadyCheckpoint.ReturnsOnOpenPhase {image : Type} {before : NativeReadyState}
    {attempt : SegmentedCheckpointReport before.session.directory before.writer}
    {reports : CheckpointCompletionReports (CensusDirectoryCache × image) attempt}
    (observed : NativeReadyCheckpoint before reports) (phase : IO.Ref (Phase Installed))
    (get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed))
    (set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit)
    (entry reached : heap) : Prop :=
  let directory := before.session.directory
  let load : EStateM IO.Error (heap × (CensusDirectoryCache × image)) Installed := do
    (← phaseEffect (get phase)).installed
  let setPhase := fun value => phaseEffect (set phase value)
  let checkpoint := withPreparedCheckpoint load liftCheckpointExcept (fun next manifest =>
    publishPrepared setPhase
      (CheckpointPublication.run next.table.runs.length
        (fun step => fileEffect (observed.primitives.cached.perform directory next manifest step)))
      (setPhase (.ready next)))
  checkpoint (entry, before.cache, (reports.observed.atRun 0).2) = .ok () (reached, reports.observed.completed)

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
    db.UsesOpenCheckpointSchedule current.state.session.directory files phase ∧
    ∃ writer, ∃ poisoned reached : heap,
      get phase entry = .ok current.state.session.phase entry ∧
      set phase .poisoned entry = .ok () poisoned ∧ contents poisoned phase = some .poisoned ∧
      set phase (.ready writer.installed) poisoned = .ok () reached ∧
      contents reached phase = some (observed.next writer).session.phase ∧
      observed.ReturnsOnOpenPhase phase get set entry reached ∧
      observed.Completed writer ∧ writer.history = history ∧
      db.UsesOpenReferences (observed.next writer).session.directory lock files phase token ∧
      InstalledClientReplay log current.reads history writer.installed (observed.next writer).session := by
  let before := current.state
  obtain ⟨writer, completed, history, replay⟩ := current.readPrefix.checkpoints observed
  have loaded := effects.reads entry phase before.session.phase stored
  obtain ⟨poisoned, excluded, poisonedPhase⟩ := effects.writes entry phase before.session.phase .poisoned stored
  obtain ⟨reached, installed, readyPhase⟩ := effects.writes poisoned phase .poisoned (.ready writer.installed) poisonedPhase
  refine ⟨uses.checkpoint, writer, poisoned, reached, loaded, excluded, poisonedPhase, installed, readyPhase, ?_,
    completed, history, uses, replay⟩
  unfold NativeReadyCheckpoint.ReturnsOnOpenPhase
  intro directory load setPhase checkpoint
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

private theorem CheckpointPreflight.returnedFileError {files : Type} {before : Phase Installed}
    {next : Installed} {manifest : ByteArray}
    (preflight : CheckpointPreflight before (.ok (next, manifest)))
    (perform : Installed → ByteArray → Step → EStateM IO.Error files Unit)
    {entry : LockedFileState files} {cause : IO.Error} {failed : files}
    (returned : runCheckpointWithEffects perform (before, entry) =
      .error cause (.poisoned, ⟨failed, entry.owners⟩)) :
    CheckpointPublication.run next.table.runs.length (perform next manifest) entry.image = .error cause failed := by
  rw [preflight.effect] at returned
  change (match CheckpointPublication.run next.table.runs.length (perform next manifest) entry.image with
    | .ok _ after => EStateM.Result.ok () (Phase.ready next, LockedFileState.mk after entry.owners)
    | .error reason after => EStateM.Result.error reason ((.poisoned : Phase Installed), LockedFileState.mk after entry.owners)) =
    .error cause (.poisoned, LockedFileState.mk failed entry.owners) at returned
  cases reached : CheckpointPublication.run next.table.runs.length (perform next manifest) entry.image with
  | ok value after =>
    simp [reached] at returned
  | error reason after =>
    simpa [reached] using returned

/-- An already verified checkpoint publication error determines the
same file failure through the opened phase cell. The raw schedule
reaches only the poison setter and the reported file sequence. -/
theorem CheckpointPreflight.publicationErrorViaOpenReferences {image : Type}
    {before : Phase Installed} {next : Installed} {manifest : ByteArray}
    (preflight : CheckpointPreflight before (.ok (next, manifest)))
    {db : DiskTable} {directory : DiskDirectory} {lock : IO.FS.Handle} {files : DiskTable.OpenSyncFiles}
    {phase : IO.Ref (Phase Installed)} {token : IO.Ref Unit}
    (uses : db.UsesOpenReferences directory lock files phase token)
    {contents : heap → IO.Ref (Phase Installed) → Option (Phase Installed)}
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (effects : OpenPhaseCellEffects contents get set) {entry : heap}
    (stored : contents entry phase = some before)
    (primitives : CheckpointPrimitiveCalls CheckpointOpenHandle image)
    {atEntry : LockedFileState (CensusDirectoryCache × image)} {cause : IO.Error} {failed : CensusDirectoryCache × image}
    (returned : runCheckpointWithEffects (primitives.cached.perform directory) (before, atEntry) =
      .error cause (.poisoned, ⟨failed, atEntry.owners⟩)) :
    let load : EStateM IO.Error (heap × (CensusDirectoryCache × image)) Installed := do
      (← phaseEffect (get phase)).installed
    let setPhase := fun value => phaseEffect (set phase value)
    let checkpoint := withPreparedCheckpoint load liftCheckpointExcept (fun next manifest =>
      publishPrepared setPhase
        (CheckpointPublication.run next.table.runs.length
          (fun step => fileEffect (primitives.cached.perform directory next manifest step)))
        (setPhase (.ready next)))
    db.UsesOpenCheckpointSchedule directory files phase ∧
    ∃ poisoned : heap,
      get phase entry = .ok before entry ∧
      set phase .poisoned entry = .ok () poisoned ∧ contents poisoned phase = some .poisoned ∧
      checkpoint (entry, atEntry.image) = .error cause (poisoned, failed) := by
  intro load setPhase checkpoint
  have loaded := effects.reads entry phase before stored
  obtain ⟨poisoned, excluded, poisonedPhase⟩ := effects.writes entry phase before .poisoned stored
  refine ⟨uses.checkpoint, poisoned, loaded, excluded, poisonedPhase, ?_⟩
  have same : load (entry, atEntry.image) =
      before.installed (m := EStateM IO.Error _) (entry, atEntry.image) := by
    simp only [load, phaseEffect, Bind.bind, EStateM.bind, loaded]
  dsimp only [checkpoint]
  rw [preflight.preparesFrom _ same]
  have failedFiles := preflight.returnedFileError (primitives.cached.perform directory) returned
  have exactError : CheckpointPublication.run next.table.runs.length
      (fun step => fileEffect (primitives.cached.perform directory next manifest step))
      (poisoned, atEntry.image) = .error cause (poisoned, failed) := by
    unfold CheckpointPublication.run
    rw [fileEffects_forM]
    change fileEffect (CheckpointPublication.run next.table.runs.length (primitives.cached.perform directory next manifest))
      (poisoned, atEntry.image) = _
    simp only [fileEffect, failedFiles]
  simp only [publishPrepared, Bind.bind, EStateM.bind, setPhase, phaseEffect, excluded, exactError]

end Alvoki.Storage.DiskSession
