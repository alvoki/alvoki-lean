import Alvoki.Storage.Disk.WalSegmentBoundedOpen

namespace Alvoki.Storage.WalSegmentRepair

open System

private theorem stagedWal_ne_checkpoint (directory : DiskDirectory) {file : DiskFile}
    (checkpoint : file = .manifest ∨ ∃ generation index, file = .run generation index) :
    directory.file .stagedWal ≠ directory.file file := by
  intro same
  have names := (String.append_right_inj (directory.path.toString ++ "/")).mp (congrArg FilePath.toString same)
  rcases checkpoint with rfl | ⟨generation, index, rfl⟩
  · exact (by decide : "WAL.next" ≠ "MANIFEST") names
  · have prefixEq := congrArg (fun name : String => name.toList.take 4) names
    change "WAL.next".toList.take 4 =
      ("run-" ++ generation.toNat.repr ++ "-" ++ index.repr ++ ".v3").toList.take 4 at prefixEq
    simp [String.toList_append] at prefixEq

private theorem walSegment_ne_checkpoint (directory : DiskDirectory) {file : DiskFile}
    (checkpoint : file = .manifest ∨ ∃ generation index, file = .run generation index) (first : Nat) :
    directory.file (.walSegment first) ≠ directory.file file := by
  intro same
  obtain ⟨_, role⟩ := DiskDirectory.walSegment_exclusive same.symm
  rcases checkpoint with rfl | ⟨_, _, rfl⟩ <;> cases role

private def reachedState {state output : Type} : EStateM.Result IO.Error state output → state
  | .ok _ after | .error _ after => after

/-- The reached state retains the projected bytes, including on error. -/
def keepsBytes {state output : Type} (bytes : state → Option ByteArray)
    (action : EStateM IO.Error state output) : Prop :=
  ∀ before, bytes (reachedState (action before)) = bytes before

private theorem keepsBytes_bind {state input output : Type} {bytes : state → Option ByteArray}
    {action : EStateM IO.Error state input} {next : input → EStateM IO.Error state output}
    (first : keepsBytes bytes action) (remaining : ∀ result, keepsBytes bytes (next result)) :
    keepsBytes bytes (action >>= next) := by
  intro before
  have firstKeeps := first before
  cases reached : action before with
  | error cause after => simpa [Bind.bind, EStateM.bind, reached, reachedState] using firstKeeps
  | ok result after =>
    change bytes (reachedState (action before)) = bytes before at firstKeeps
    rw [reached] at firstKeeps
    change bytes after = bytes before at firstKeeps
    simpa only [Bind.bind, EStateM.bind, reached] using (remaining result after).trans firstKeeps

/-- WAL repair preserves the observed bytes at the checkpoint manifest and
each run path, including after a returned error. The primitive reports must
preserve bytes outside the name they can modify, and sync must preserve
visible byte contents. These are filesystem assumptions about the reached
effects, including descriptor and pathname aliasing. -/
theorem finishBoundedMarkedOpen_preservesCheckpointBytes {state : Type} (directory : DiskDirectory) (plan : Plan)
    (keeperFileSize : Nat) (visible : state → FilePath → Option ByteArray)
    (removeFile : FilePath → EStateM IO.Error state (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error state Unit)
    (sync : Array FilePath → EStateM IO.Error state Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error state Unit)
    (removeOther : ∀ path file, path ≠ file → keepsBytes (fun state => visible state file) (removeFile path))
    (writeOther : ∀ path content file, path ≠ file → keepsBytes (fun state => visible state file) (write path content))
    (syncVisible : ∀ paths file, keepsBytes (fun state => visible state file) (sync paths))
    (renameOther : ∀ source dest file, source ≠ file → dest ≠ file →
      keepsBytes (fun state => visible state file) (renameFile source dest))
    {file : DiskFile} (checkpoint : file = .manifest ∨ ∃ generation index, file = .run generation index)
    (initial : state) :
    let path := directory.file file
    match finishBoundedMarkedOpen directory plan keeperFileSize removeFile write sync renameFile initial with
    | .ok () after | .error _ after => visible after path = visible initial path := by
  intro path
  let bytes (state : state) := visible state path
  have stepKeeps (step : Step) :
      keepsBytes bytes (performPaths directory plan removeFile throw write sync renameFile step) := by
    cases step with
    | unlink first =>
      unfold performPaths RunCollection.performPaths
      apply keepsBytes_bind (removeOther _ path (walSegment_ne_checkpoint directory checkpoint first))
      intro removed
      cases result : RunCollection.ownedUnlinkResult removed <;> exact fun _ => rfl
    | syncPruned | syncKeeper => exact syncVisible _ path
    | replace callback =>
      cases callback with
      | writeStaged => exact writeOther _ _ path (stagedWal_ne_checkpoint directory checkpoint)
      | syncStaged | syncDirectory => exact syncVisible _ path
      | renameStaged =>
        exact renameOther _ _ path (stagedWal_ne_checkpoint directory checkpoint)
          (walSegment_ne_checkpoint directory checkpoint plan.keeper)
  have stepsKeep (steps : List Step) :
      keepsBytes bytes (steps.forM (performPaths directory plan removeFile throw write sync renameFile)) := by
    induction steps with
    | nil => exact fun _ => rfl
    | cons step rest ih =>
      change keepsBytes bytes (performPaths directory plan removeFile throw write sync renameFile step >>= fun _ =>
        rest.forM (performPaths directory plan removeFile throw write sync renameFile))
      exact keepsBytes_bind (stepKeeps step) (fun _ => ih)
  have repair (replaceKeeper : Bool) : keepsBytes bytes
      (runRepairPlan directory plan replaceKeeper removeFile write sync renameFile) :=
    keepsBytes_bind (syncVisible #[directory.path] path)
      (fun _ => stepsKeep (steps plan.newer replaceKeeper))
  have preserves : keepsBytes bytes
      (finishBoundedMarkedOpen directory plan keeperFileSize removeFile write sync renameFile) := by
    unfold finishBoundedMarkedOpen
    split
    · split
      · exact keepsBytes_bind (syncVisible #[directory.path] path)
          (fun _ => syncVisible #[directory.file (.walSegment plan.keeper)] path)
      · exact fun _ => rfl
    · split
      · exact repair _
      · exact fun _ => rfl
  have unchanged := preserves initial
  cases report : finishBoundedMarkedOpen directory plan keeperFileSize removeFile write sync renameFile initial with
  | ok result after => cases result; simpa [report, reachedState, bytes] using unchanged
  | error cause after => simpa [report, reachedState, bytes] using unchanged

end Alvoki.Storage.WalSegmentRepair
