import Alvoki.Storage.Disk.CheckpointLockHandoff

namespace Alvoki.Storage.DiskSession

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

private def liftCheckpointExcept {state α : Type} (result : Except String α) : EStateM IO.Error state α :=
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

/-- Interpret the actual ordered preflight under arbitrary publication
callbacks. A rejected phase, flush, bound or manifest leaves the exact
original state. A prepared result hands the exact manifest and installed
state to the shared publication runner. -/
theorem CheckpointPreflight.effect {image : Type} {phase : Phase Installed}
    {result : Except IO.Error (Installed × ByteArray)} (preflight : CheckpointPreflight phase result)
    (perform : Installed → ByteArray → CheckpointPublication.Step → EStateM IO.Error image Unit)
    (files : LockedFileState image) :
    runCheckpointWithEffects perform (phase, files) = match result with
    | .error cause => .error cause (phase, files)
    | .ok (next, manifest) => runPreparedCheckpoint next (perform next manifest) (phase, files) := by
  cases preflight <;> try rfl
  all_goals
    simp [runCheckpointWithEffects, withPreparedCheckpoint, Phase.installed, Bind.bind, EStateM.bind,
      Pure.pure, EStateM.pure, flushCheckpoint_lift, liftCheckpointExcept, throw, throwThe,
      MonadExceptOf.throw, EStateM.throw, -UInt64.ofNat_add, *]

/-- A rejected preflight returns before poisoning or file dispatch. The
whole state remains in place, including the phase, lock and cache. -/
theorem CheckpointPreflight.rejected {image : Type} {phase : Phase Installed} {cause : IO.Error}
    (preflight : CheckpointPreflight phase (.error cause))
    (perform : Installed → ByteArray → CheckpointPublication.Step → EStateM IO.Error image Unit)
    (files : LockedFileState image) :
    runCheckpointWithEffects perform (phase, files) = .error cause (phase, files) :=
  preflight.effect perform files

end Alvoki.Storage.DiskSession
