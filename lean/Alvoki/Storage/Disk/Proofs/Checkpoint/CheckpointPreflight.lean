import Alvoki.Storage.Disk.Proofs.Checkpoint.CheckpointLockHandoff

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication

/-- The ordered checks reached by the native checkpoint before any
phase update or file effect. A later failure requires all earlier checks
to have succeeded. -/
inductive CheckpointPreflight : Phase Installed → Except IO.Error (Installed × ByteArray) → Prop where
  | closed : CheckpointPreflight .closed (.error (IO.userError "database is closed"))
  | poisoned : CheckpointPreflight .poisoned (.error (IO.userError "publication failed; reopen the database"))
  | flushError {state : Installed} {message : String}
      (flushed : (flushForCheckpoint state.table id : Except String PackedTable) = .error message) :
      CheckpointPreflight (.ready state) (.error (IO.userError message))
  | boundsError {state : Installed} {table : PackedTable}
      (flushed : (flushForCheckpoint state.table id : Except String PackedTable) = .ok table)
      (outside : ¬ (state.generation.toNat + 1 < UInt64.size ∧ table.runs.length < UInt64.size)) :
      CheckpointPreflight (.ready state) (.error (IO.userError "checkpoint generation or run count is too large"))
  | manifestError {state : Installed} {table : PackedTable} {message : String}
      (flushed : (flushForCheckpoint state.table id : Except String PackedTable) = .ok table)
      (fits : state.generation.toNat + 1 < UInt64.size ∧ table.runs.length < UInt64.size)
      (encoded : encodeCheckpointIntegrityManifest table (UInt64.ofNat (state.generation.toNat + 1)) = .error message) :
      CheckpointPreflight (.ready state) (.error (IO.userError message))
  | prepared {state : Installed} {table : PackedTable} {manifest : ByteArray}
      (flushed : (flushForCheckpoint state.table id : Except String PackedTable) = .ok table)
      (fits : state.generation.toNat + 1 < UInt64.size ∧ table.runs.length < UInt64.size)
      (encoded : encodeCheckpointIntegrityManifest table (UInt64.ofNat (state.generation.toNat + 1)) = .ok manifest) :
      CheckpointPreflight (.ready state) (.ok ({ state with table, generation := UInt64.ofNat (state.generation.toNat + 1) }, manifest))

theorem CheckpointPreflight.total (phase : Phase Installed) : ∃ result, CheckpointPreflight phase result := by
  cases phase with
  | closed => exact ⟨_, .closed⟩
  | poisoned => exact ⟨_, .poisoned⟩
  | ready state =>
    cases flushed : (flushForCheckpoint state.table id : Except String PackedTable) with
    | error message => exact ⟨_, .flushError flushed⟩
    | ok table =>
      by_cases fits : state.generation.toNat + 1 < UInt64.size ∧ table.runs.length < UInt64.size
      · cases encoded : encodeCheckpointIntegrityManifest table (UInt64.ofNat (state.generation.toNat + 1)) with
        | error message => exact ⟨_, .manifestError flushed fits encoded⟩
        | ok manifest => exact ⟨_, .prepared flushed fits encoded⟩
      · exact ⟨_, .boundsError flushed fits⟩

/-- Recover the exact guard and encoder results from the prepared outcome. -/
theorem CheckpointPreflight.preparedFacts {before next : Installed} {manifest : ByteArray}
    (preflight : CheckpointPreflight (.ready before) (.ok (next, manifest))) :
    (flushForCheckpoint before.table id : Except String PackedTable) = .ok next.table ∧
      before.generation.toNat + 1 < UInt64.size ∧ next.table.runs.length < UInt64.size ∧
      encodeCheckpointIntegrityManifest next.table (UInt64.ofNat (before.generation.toNat + 1)) = .ok manifest := by
  cases preflight with
  | prepared flushed fits encoded => exact ⟨flushed, fits.1, fits.2, encoded⟩

def liftCheckpointExcept {state α : Type} (result : Except String α) : EStateM IO.Error state α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private theorem flushCheckpoint_lift {state : Type} (table : PackedTable) :
    flushForCheckpoint (m := EStateM IO.Error state) table liftCheckpointExcept =
      liftCheckpointExcept (flushForCheckpoint (m := Except String) table id) := by
  by_cases empty : table.memoryIsEmpty = true <;> simp [flushForCheckpoint, empty, liftCheckpointExcept, pure, Except.pure]

/-- Interpret `DiskTable.checkpoint_schedule` with the reached phase cell
and the actual file callbacks. Only successful preparation enters the
same poisoned publication tail as the other checkpoint proofs. -/
def runCheckpointWithEffects {image : Type}
    (perform : Installed → ByteArray → CheckpointPublication.Step → EStateM IO.Error image Unit) :
    EStateM IO.Error (Phase Installed × LockedFileState image) Unit :=
  withPreparedCheckpoint
    (fun current => Phase.installed (m := EStateM IO.Error _) current.1 current) liftCheckpointExcept
    (fun prepared manifest => runPreparedCheckpoint prepared (perform prepared manifest))

/-- The ordered preparation consumes the supplied reached phase read.
Only a prepared outcome calls the publication continuation. -/
theorem CheckpointPreflight.preparesFrom {state : Type} {phase : Phase Installed}
    {result : Except IO.Error (Installed × ByteArray)} (preflight : CheckpointPreflight phase result)
    (load : EStateM IO.Error state Installed) {entry : state}
    (loaded : load entry = (phase.installed : EStateM IO.Error state Installed) entry)
    (publish : Installed → ByteArray → EStateM IO.Error state Unit) :
    withPreparedCheckpoint load liftCheckpointExcept publish entry = match result with
    | .error cause => .error cause entry
    | .ok (next, manifest) => publish next manifest entry := by
  cases preflight <;>
    simp [withPreparedCheckpoint, Phase.installed, Bind.bind, EStateM.bind,
      Pure.pure, EStateM.pure, flushCheckpoint_lift, liftCheckpointExcept, throw, throwThe,
      MonadExceptOf.throw, EStateM.throw, -UInt64.ofNat_add, *]

/-- A rejected phase, flush, bound or manifest leaves the exact original
state. A prepared result hands the exact manifest and writer to the
shared publication runner. -/
theorem CheckpointPreflight.effect {image : Type} {phase : Phase Installed}
    {result : Except IO.Error (Installed × ByteArray)} (preflight : CheckpointPreflight phase result)
    (perform : Installed → ByteArray → CheckpointPublication.Step → EStateM IO.Error image Unit)
    (files : LockedFileState image) :
    runCheckpointWithEffects perform (phase, files) = match result with
    | .error cause => .error cause (phase, files)
    | .ok (next, manifest) => runPreparedCheckpoint next (perform next manifest) (phase, files) :=
  preflight.preparesFrom (fun current : Phase Installed × LockedFileState image => Phase.installed (m := EStateM IO.Error _) current.1 current)
    (entry := (phase, files)) rfl (fun next manifest => runPreparedCheckpoint next (perform next manifest))

/-- A rejected preflight returns before poisoning or file dispatch. The
whole state remains in place, including the phase, lock and cache. -/
theorem CheckpointPreflight.rejected {image : Type} {phase : Phase Installed} {cause : IO.Error}
    (preflight : CheckpointPreflight phase (.error cause))
    (perform : Installed → ByteArray → CheckpointPublication.Step → EStateM IO.Error image Unit)
    (files : LockedFileState image) :
    runCheckpointWithEffects perform (phase, files) = .error cause (phase, files) :=
  preflight.effect perform files

/-- The phase and files at a checkpoint's next issued step, after its
returned prefix. The continuation describes what the full schedule does
if the remaining callbacks return. An interruption has its own effect
observation at this boundary. -/
structure CheckpointIssue {image : Type}
    (perform : Installed → ByteArray → Step → EStateM IO.Error image Unit)
    (phase : Phase Installed) (files : LockedFileState image) (next : Installed) (manifest : ByteArray)
    (completed : List Step) (current : Step) (reached : image) : Prop where
  atIssue : runCheckpointActions (completed.forM (perform next manifest)) .poisoned (phase, files) =
    .ok () (.poisoned, ⟨reached, files.owners⟩)
  continuation : ∃ remaining, steps next.table.runs.length = completed ++ current :: remaining ∧
    runCheckpointWithEffects perform (phase, files) =
      match ((current :: remaining).forM (perform next manifest)) reached with
      | .ok () after => .ok () (.ready next, ⟨after, files.owners⟩)
      | .error cause after => .error cause (.poisoned, ⟨after, files.owners⟩)

/-- Follow the same ready guard, preparation and poisoned phase write as
the full checkpoint before taking the exact reached callback prefix. -/
theorem CheckpointPreflight.reachesIssue {image : Type} {phase : Phase Installed}
    {next : Installed} {manifest : ByteArray}
    (preflight : CheckpointPreflight phase (.ok (next, manifest)))
    (perform : Installed → ByteArray → Step → EStateM IO.Error image Unit)
    (files : LockedFileState image) {completed remaining : List Step} {current : Step} {reached : image}
    (ordered : steps next.table.runs.length = completed ++ current :: remaining)
    (returned : (completed.forM (perform next manifest)) files.image = .ok () reached) :
    CheckpointIssue perform phase files next manifest completed current reached := by
  have suffix : ((completed ++ current :: remaining).forM (perform next manifest)) files.image =
      ((current :: remaining).forM (perform next manifest)) reached := by
    rw [List.forM_eq_forM, List.forM_append, ← List.forM_eq_forM]
    change EStateM.bind (completed.forM (perform next manifest))
      (fun _ => (current :: remaining).forM (perform next manifest)) files.image = _
    simp only [EStateM.bind, returned]
  refine ⟨?_, remaining, ordered, ?_⟩
  · simp only [runCheckpointActions, Bind.bind, EStateM.bind, modify, modifyGet, MonadStateOf.modifyGet,
      EStateM.modifyGet, returned]
  · rw [preflight.effect]
    simp only [runPreparedCheckpoint, runCheckpointActions, CheckpointPublication.run, Bind.bind, EStateM.bind, modify, modifyGet,
      MonadStateOf.modifyGet, EStateM.modifyGet, ordered, suffix]
    cases ((current :: remaining).forM (perform next manifest)) reached <;> rfl

/-- The native file dispatch uses the exact generation, run bytes and
manifest produced by preparation, even when a publication callback fails. -/
structure CheckpointFileCallbacks (state : Type) where
  writeRun : FilePath → ByteArray → EStateM IO.Error state Unit
  writeStaged : FilePath → ByteArray → EStateM IO.Error state Unit
  sync : Array FilePath → EStateM IO.Error state Unit
  rename : FilePath → FilePath → EStateM IO.Error state Unit

def CheckpointFileCallbacks.perform {state : Type} (callbacks : CheckpointFileCallbacks state)
    (directory : DiskDirectory) (next : Installed) (manifest : ByteArray) : Step → EStateM IO.Error state Unit :=
  performCheckpointFileStep directory next.generation next.table.runs.toArray (directory.file .stagedManifest)
    manifest (fun found => match found with
      | some run => pure run
      | none => throw (IO.userError "checkpoint run index is out of bounds"))
    callbacks.writeRun callbacks.writeStaged callbacks.sync callbacks.rename

/-- A reported publication error follows successful preflight. The
native-shaped runner returns the same error and reached state. -/
theorem CheckpointPreflight.publicationError {image : Type} {before next : Installed} {manifest : ByteArray}
    (preflight : CheckpointPreflight (.ready before) (.ok (next, manifest)))
    (callbacks : CheckpointFileCallbacks image) (directory : DiskDirectory)
    {files reached : LockedFileState image} {cause : IO.Error}
    (failed : runPreparedCheckpoint next (callbacks.perform directory next manifest) (.ready before, files) =
      .error cause (.poisoned, reached)) :
    runCheckpointWithEffects (callbacks.perform directory) (.ready before, files) =
      .error cause (.poisoned, reached) := by
  rw [preflight.effect]
  exact failed

end Alvoki.Storage.DiskSession
