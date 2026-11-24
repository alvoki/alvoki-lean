import Alvoki.Storage.Disk.DiskTable
import Alvoki.Storage.Publication.CheckpointPublicationModel

namespace Alvoki.Storage
open System Alvoki.Compaction

/-- The primitive file effects for the model's exact checkpoint run list.
Each run is synced before the run directory barrier. The manifest is then
staged, synced, renamed and settled by the final directory sync. -/
def runCheckpointFilePlan [Monad m] (dir : DiskDirectory) (plan : CheckpointPublication.RunSet)
    (write : FilePath → ByteArray → m Unit) (sync : Array FilePath → m Unit)
    (renameFile : FilePath → FilePath → m Unit) : m Unit := do
  plan.files.zipIdx.forM fun (bytes, index) => do
    let path := dir.file (.run plan.header.generation index)
    write path bytes
    sync #[path]
  sync #[dir.path]
  let staged := dir.file .stagedManifest
  write staged (Manifest.encode plan.header)
  sync #[staged]
  renameFile staged (dir.file .manifest)
  sync #[dir.path]
  pure ()

private theorem runFileSteps_exact [Monad m] [LawfulMonad m]
    (dir : DiskDirectory) (generation : UInt64) (runs : Array CheckedRun)
    (staged : FilePath) (manifest : ByteArray) (checkRun : Option CheckedRun → m CheckedRun)
    (write : FilePath → ByteArray → m Unit) (sync : Array FilePath → m Unit)
    (renameFile : FilePath → FilePath → m Unit) (checked : ∀ run, checkRun (some run) = pure run)
    (files : List ByteArray) (start : Nat)
    (bytesAt : ∀ offset, (runs[start + offset]?).map (·.run.bytes) = files[offset]?) :
    ((List.range' start files.length).flatMap fun index =>
      [CheckpointPublication.Step.writeRun index, .syncRun index]).forM
        (performCheckpointFileStep dir generation runs staged manifest checkRun write sync renameFile) =
    (files.zipIdx start).forM (fun (bytes, index) => do
      let path := dir.file (.run generation index)
      write path bytes
      sync #[path]) := by
  induction files generalizing start with
  | nil => rfl
  | cons bytes files ih =>
    have first := bytesAt 0
    simp only [Nat.add_zero, List.getElem?_cons_zero] at first
    obtain ⟨run, found, payload⟩ : ∃ run, runs[start]? = some run ∧ run.run.bytes = bytes := by
      cases found : runs[start]? with
      | none => simp [found] at first
      | some run => exact ⟨run, rfl, by simpa [found] using first⟩
    have remaining (offset : Nat) :
        (runs[(start + 1) + offset]?).map (·.run.bytes) = files[offset]? := by
      simpa [Nat.add_assoc, Nat.add_comm 1 offset] using bytesAt (offset + 1)
    simp only [List.forM_eq_forM] at ih ⊢
    rw [List.length_cons, List.range'_succ, List.flatMap_cons, List.forM_append,
      List.zipIdx_cons, List.forM_cons, ih (start + 1) remaining]
    simp [performCheckpointFileStep, found, checked, payload, bind_assoc]

/-- The same dispatch used by the adapter executes the model's ordered run
bytes at their generation and index paths, then the directory barrier and
manifest replacement. The equation describes callback order and arguments.
Each primitive's filesystem effects are supplied by its own contract. -/
theorem run_performCheckpointFileStep [Monad m] [LawfulMonad m]
    (dir : DiskDirectory) (table : PackedTable) (generation : UInt64)
    (checkRun : Option CheckedRun → m CheckedRun)
    (write : FilePath → ByteArray → m Unit) (sync : Array FilePath → m Unit)
    (renameFile : FilePath → FilePath → m Unit) (checked : ∀ run, checkRun (some run) = pure run) :
    let plan : CheckpointPublication.RunSet :=
      ⟨checkpointHeader table generation, table.runs.map (·.run.bytes)⟩
    CheckpointPublication.run table.runs.toArray.size
      (performCheckpointFileStep dir generation table.runs.toArray (dir.file .stagedManifest)
        (Manifest.encode plan.header) checkRun write sync renameFile) =
      runCheckpointFilePlan dir plan write sync renameFile := by
  intro plan
  have bytesAt (offset : Nat) :
      (table.runs.toArray[0 + offset]?).map (·.run.bytes) = plan.files[offset]? := by
    simp [plan]
  have runSteps :=
    runFileSteps_exact dir generation table.runs.toArray (dir.file .stagedManifest)
      (Manifest.encode plan.header) checkRun write sync renameFile checked plan.files 0 bytesAt
  simp only [plan, List.length_map, ← List.range_eq_range', List.forM_eq_forM] at runSteps
  simp only [CheckpointPublication.run, CheckpointPublication.steps, List.forM_eq_forM, List.forM_append,
    List.size_toArray, CheckpointPublication.runSteps]
  rw [runSteps]
  simp [runCheckpointFilePlan, Publication.steps, performCheckpointFileStep,
    Publication.performReplacement, checkpointHeader, plan, bind_assoc]

private theorem checkpointIOLawful : LawfulMonad IO := .mk'
  (id_map := fun op => funext fun world => by
    change EST.bind op (fun value => EST.pure (id value)) world = op world
    unfold EST.bind EST.pure
    cases op world <;> rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun op next last => funext fun world => by
    change EST.bind (EST.bind op next) last world =
      EST.bind op (fun value => EST.bind (next value) last) world
    unfold EST.bind
    cases op world <;> rfl)
  (map_const := fun _ _ => rfl)

/-- The dispatch equation also holds for the native exception monad and the
adapter's checked array access. -/
theorem run_performCheckpointFileStep_io
    (dir : DiskDirectory) (table : PackedTable) (generation : UInt64)
    (write : FilePath → ByteArray → IO Unit) (sync : Array FilePath → IO Unit)
    (renameFile : FilePath → FilePath → IO Unit) :
    let plan : CheckpointPublication.RunSet :=
      ⟨checkpointHeader table generation, table.runs.map (·.run.bytes)⟩
    CheckpointPublication.run table.runs.toArray.size
      (performCheckpointFileStep dir generation table.runs.toArray (dir.file .stagedManifest)
        (Manifest.encode plan.header)
        (fun found => match found with
          | some run => pure run
          | none => throw (IO.userError "checkpoint run index is out of bounds"))
        write sync renameFile) =
      runCheckpointFilePlan dir plan write sync renameFile := by
  letI := checkpointIOLawful
  exact run_performCheckpointFileStep dir table generation _ write sync renameFile (fun _ => rfl)

end Alvoki.Storage
