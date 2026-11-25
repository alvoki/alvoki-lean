import Alvoki.Storage.Disk.NativeOpenAcquire
import Alvoki.Storage.Disk.NativeReadyCheckpoint

namespace Alvoki.Storage.CheckpointPublication

/-- The actual schedule returned the completed prefix, then its first
failing callback returned the indicated diagnostic and reached state. -/
def FirstFailure {image : Type} (count : Nat) (perform : Step → EStateM IO.Error image Unit)
    (before : image) (cause : IO.Error) (after : image) : Prop :=
  ∃ done step remaining atIssue,
    steps count = done ++ step :: remaining ∧
    (done.forM perform) before = .ok () atIssue ∧
    perform step atIssue = .error cause after

private theorem forM_firstFailure {image : Type} (actions : List Step)
    (perform : Step → EStateM IO.Error image Unit) {before after : image} {cause : IO.Error}
    (returned : (actions.forM perform) before = .error cause after) :
    ∃ done step remaining atIssue,
      actions = done ++ step :: remaining ∧
      (done.forM perform) before = .ok () atIssue ∧
      perform step atIssue = .error cause after := by
  induction actions generalizing before with
  | nil => simp [List.forM_nil, Pure.pure, EStateM.pure] at returned
  | cons step tail ih =>
    change EStateM.bind (perform step) (fun _ => tail.forM perform) before = _ at returned
    cases issued : perform step before with
    | error reason reached =>
      have failed : perform step before = .error cause after := by
        simpa only [EStateM.bind, issued] using returned
      exact ⟨[], step, tail, before, rfl, rfl, failed⟩
    | ok value reached =>
      have failed : (tail.forM perform) reached = .error cause after := by
        simpa only [EStateM.bind, issued] using returned
      obtain ⟨done, first, remaining, atIssue, order, returnedPrefix, fails⟩ := ih failed
      refine ⟨step :: done, first, remaining, atIssue, congrArg (List.cons step) order, ?_, fails⟩
      change EStateM.bind (perform step) (fun _ => done.forM perform) before = _
      simp only [EStateM.bind, issued, returnedPrefix]

theorem run_firstFailure {image : Type} {count : Nat} {perform : Step → EStateM IO.Error image Unit}
    {before after : image} {cause : IO.Error}
    (returned : run count perform before = .error cause after) :
    FirstFailure count perform before cause after :=
  forM_firstFailure (steps count) perform returned

end Alvoki.Storage.CheckpointPublication

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

/-- Interpret the public checkpoint using its opened phase cell and
one fixed model of the cached file calls. -/
def runCheckpointOnOpenPhase {image : Type}
    (perform : Installed → ByteArray → Step → EStateM IO.Error image Unit)
    (phase : IO.Ref (Phase Installed))
    (get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed))
    (set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit) :
    EStateM IO.Error (heap × image) Unit :=
  withPreparedCheckpoint (do (← phaseEffect (get phase)).installed) liftCheckpointExcept
    (fun next manifest => publishPrepared (fun value => phaseEffect (set phase value))
      (CheckpointPublication.run next.table.runs.length (fun step => fileEffect (perform next manifest step)))
      (phaseEffect (set phase (.ready next))))

/-- Pair the actual phase-heap return with its normalized file and phase
return, retaining the branch evidence from the same fixed callbacks. -/
inductive OpenCheckpointReturn {image : Type}
    (perform : Installed → ByteArray → Step → EStateM IO.Error image Unit)
    (before : Phase Installed) (files : LockedFileState image) (reference : IO.Ref (Phase Installed))
    (contents : heap → IO.Ref (Phase Installed) → Option (Phase Installed))
    (set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit) (entry : heap) :
    EStateM.Result IO.Error (heap × image) Unit →
      EStateM.Result IO.Error (Phase Installed × LockedFileState image) Unit → Prop where
  | rejected {cause : IO.Error} (preflight : CheckpointPreflight before (.error cause)) :
      OpenCheckpointReturn perform before files reference contents set entry
        (.error cause (entry, files.image)) (.error cause (before, files))
  | published {next : Installed} {manifest : ByteArray} {poisoned reached : heap} {after : image}
      (preflight : CheckpointPreflight before (.ok (next, manifest)))
      (excluded : set reference .poisoned entry = .ok () poisoned)
      (poison : contents poisoned reference = some .poisoned)
      (published : CheckpointPublication.run next.table.runs.length (perform next manifest) files.image = .ok () after)
      (installed : set reference (.ready next) poisoned = .ok () reached)
      (ready : contents reached reference = some (.ready next)) :
      OpenCheckpointReturn perform before files reference contents set entry
        (.ok () (reached, after)) (.ok () (.ready next, ⟨after, files.owners⟩))
  | fileError {next : Installed} {manifest : ByteArray} {poisoned : heap} {cause : IO.Error} {after : image}
      (preflight : CheckpointPreflight before (.ok (next, manifest)))
      (excluded : set reference .poisoned entry = .ok () poisoned)
      (poison : contents poisoned reference = some .poisoned)
      (failed : CheckpointPublication.FirstFailure next.table.runs.length (perform next manifest) files.image cause after) :
      OpenCheckpointReturn perform before files reference contents set entry
        (.error cause (poisoned, after)) (.error cause (.poisoned, ⟨after, files.owners⟩))

/-- Classify every ordinary return of this opened checkpoint. The first
failing publication step is derived from the same schedule return that
provides the exact reached image and diagnostic. -/
theorem OpenPhaseCellEffects.classifiesCheckpointReturn {image : Type}
    {db : DiskTable} {directory : DiskDirectory} {lock : IO.FS.Handle} {files : DiskTable.OpenSyncFiles}
    {reference : IO.Ref (Phase Installed)} {token : IO.Ref Unit}
    (uses : db.UsesOpenReferences directory lock files reference token)
    {contents : heap → IO.Ref (Phase Installed) → Option (Phase Installed)}
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (effects : OpenPhaseCellEffects contents get set) {entry : heap} {before : Phase Installed}
    (stored : contents entry reference = some before)
    (calls : CheckpointPrimitiveCalls CheckpointOpenHandle image)
    (fileState : LockedFileState (CensusDirectoryCache × image)) :
    db.UsesOpenCheckpointSchedule directory files reference ∧
    OpenCheckpointReturn (calls.cached.perform directory) before fileState reference contents set entry
      (runCheckpointOnOpenPhase (calls.cached.perform directory) reference get set (entry, fileState.image))
      (runCheckpointWithEffects (calls.cached.perform directory) (before, fileState)) := by
  refine ⟨uses.checkpoint, ?_⟩
  obtain ⟨preparation, preflight⟩ := CheckpointPreflight.total before
  let perform := calls.cached.perform directory
  let load : EStateM IO.Error (heap × (CensusDirectoryCache × image)) Installed := do
    (← phaseEffect (get reference)).installed
  let publish := fun next manifest => publishPrepared (fun value => phaseEffect (set reference value))
    (CheckpointPublication.run next.table.runs.length (fun step => fileEffect (perform next manifest step)))
    (phaseEffect (set reference (.ready next)))
  have loaded : load (entry, fileState.image) = before.installed (m := EStateM IO.Error _) (entry, fileState.image) := by
    simp only [load, phaseEffect, Bind.bind, EStateM.bind, effects.reads entry reference before stored]
  rw [show runCheckpointOnOpenPhase perform reference get set = withPreparedCheckpoint load liftCheckpointExcept publish from rfl,
    preflight.preparesFrom load loaded publish, preflight.effect perform fileState]
  cases preparation with
  | error cause => exact .rejected preflight
  | ok prepared =>
    obtain ⟨next, manifest⟩ := prepared
    obtain ⟨poisoned, excluded, poison⟩ := effects.writes entry reference before .poisoned stored
    have lifted : CheckpointPublication.run next.table.runs.length (fun step => fileEffect (perform next manifest step))
        (poisoned, fileState.image) =
      fileEffect (CheckpointPublication.run next.table.runs.length (perform next manifest)) (poisoned, fileState.image) :=
      fileEffects_forM (steps next.table.runs.length) (perform next manifest) (poisoned, fileState.image)
    cases published : CheckpointPublication.run next.table.runs.length (perform next manifest) fileState.image with
    | ok value after =>
      cases value
      obtain ⟨reached, installed, ready⟩ := effects.writes poisoned reference .poisoned (.ready next) poison
      simp only [publish, publishPrepared, Bind.bind, EStateM.bind, phaseEffect, excluded, lifted, fileEffect,
        published, installed, runPreparedCheckpoint, runCheckpointActions, modify, modifyGet, MonadStateOf.modifyGet,
        EStateM.modifyGet]
      exact .published preflight excluded poison published installed ready
    | error cause after =>
      simp only [publish, publishPrepared, Bind.bind, EStateM.bind, phaseEffect, excluded, lifted, fileEffect,
        published, runPreparedCheckpoint, runCheckpointActions, modify, modifyGet, MonadStateOf.modifyGet,
        EStateM.modifyGet]
      exact .fileError preflight excluded poison (CheckpointPublication.run_firstFailure published)

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
