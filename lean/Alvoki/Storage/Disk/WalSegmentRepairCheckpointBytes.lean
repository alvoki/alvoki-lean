import Alvoki.Storage.Disk.WalSegmentBoundedOpen
import Alvoki.Storage.Disk.CheckpointRunChunkReports

namespace Alvoki.Storage.WalSegmentRepair

open System Manifest

private theorem stagedWal_ne_checkpoint (directory : DiskDirectory) {file : DiskFile}
    (checkpoint : file = .manifest ∨ file = .walBoundary ∨ ∃ generation index, file = .run generation index) :
    directory.file .stagedWal ≠ directory.file file := by
  intro same
  have names := (String.append_right_inj (directory.path.toString ++ "/")).mp (congrArg FilePath.toString same)
  rcases checkpoint with rfl | rfl | ⟨generation, index, rfl⟩
  · exact (by decide : "WAL.next" ≠ "MANIFEST") names
  · exact (by decide : "WAL.next" ≠ "WAL.commit") names
  · have prefixEq := congrArg (fun name : String => name.toList.take 4) names
    change "WAL.next".toList.take 4 =
      ("run-" ++ generation.toNat.repr ++ "-" ++ index.repr ++ ".v3").toList.take 4 at prefixEq
    simp [String.toList_append] at prefixEq

private theorem walSegment_ne_checkpoint (directory : DiskDirectory) {file : DiskFile}
    (checkpoint : file = .manifest ∨ file = .walBoundary ∨ ∃ generation index, file = .run generation index)
    (first : Nat) :
    directory.file (.walSegment first) ≠ directory.file file := by
  intro same
  obtain ⟨_, role⟩ := DiskDirectory.walSegment_exclusive same.symm
  rcases checkpoint with rfl | rfl | ⟨_, _, rfl⟩ <;> cases role

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

/-- WAL repair preserves the observed bytes at the checkpoint manifest,
WAL marker and each run path, including after a returned error. The
primitive reports must preserve bytes outside the names they can modify,
and sync must preserve visible byte contents. These assumptions cover
descriptor and pathname aliasing in the reached effects. -/
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
    {file : DiskFile}
    (checkpoint : file = .manifest ∨ file = .walBoundary ∨ ∃ generation index, file = .run generation index)
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

private theorem mapM_preservesRunBytes {indices : List Nat} {known visible : Nat → Option ByteArray}
    {files : List ByteArray} (stored : indices.mapM known = some files)
    (same : ∀ index ∈ indices, ∀ payload, known index = some payload → visible index = some payload) :
    indices.mapM visible = some files := by
  induction indices generalizing files with
  | nil => exact stored
  | cons index rest ih =>
    cases head : known index with
    | none => simp [List.mapM_cons, head, Bind.bind, Option.bind] at stored
    | some bytes =>
      have visibleHead := same index List.mem_cons_self bytes head
      cases tail : rest.mapM known with
      | none => simp [List.mapM_cons, head, tail, Bind.bind, Option.bind] at stored
      | some restBytes =>
        have visibleTail := ih tail (fun i member => same i (List.mem_cons_of_mem _ member))
        simpa [List.mapM_cons, visibleHead, visibleTail, Bind.bind, Option.bind] using
          (show some (bytes :: restBytes) = some files by
            simpa [List.mapM_cons, head, tail, Bind.bind, Option.bind] using stored)

/-- From exact held checkpoint reads, the WAL finisher preserves the visible
marker and the same ordered run bytes at their canonical paths. Each stat
must refer to the object visible at that path when repair starts. The
primitive locality assumptions apply also to effects before an error. -/
theorem finishBoundedMarkedOpen_preservesSelectedCheckpoint {state : Type}
    (directory : DiskDirectory) (plan : Plan) (keeperFileSize : Nat)
    (visible : state → FilePath → Option ByteArray)
    (removeFile : FilePath → EStateM IO.Error state (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error state Unit)
    (sync : Array FilePath → EStateM IO.Error state Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error state Unit)
    (removeOther : ∀ path file, path ≠ file → keepsBytes (fun state => visible state file) (removeFile path))
    (writeOther : ∀ path content file, path ≠ file → keepsBytes (fun state => visible state file) (write path content))
    (syncVisible : ∀ paths file, keepsBytes (fun state => visible state file) (sync paths))
    (renameOther : ∀ source dest file, source ≠ file → dest ≠ file →
      keepsBytes (fun state => visible state file) (renameFile source dest))
    (initial after : state)
    (reached : finishBoundedMarkedOpen directory plan keeperFileSize removeFile write sync renameFile initial =
      .ok () after ∨ ∃ cause, finishBoundedMarkedOpen directory plan keeperFileSize removeFile write sync renameFile
        initial = .error cause after)
    (pair : DirectoryPublication.Bindings)
    {durable : CheckpointPublication.RunFiles} {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint durable pair.manifest checkpoint)
    (visibleManifest : visible initial (directory.file .manifest) = pair.manifest)
    (visibleMarker : visible initial (directory.file .walBoundary) = pair.walBoundary)
    (reads : CheckpointRunChunkReads) (observed : reads.ObservesSelected directory pair.manifest durable)
    (bindings : FilePath → Option Nat)
    (sameObject : ∀ path metadata object, reads.stat path = .ok (metadata, object) → bindings path = some object)
    (objectBytes : ∀ path object, bindings path = some object → visible initial path = reads.objectBytes object) :
    let afterRuns : CheckpointPublication.RunFiles := fun generation index =>
      visible after (directory.file (.run generation index))
    visible after (directory.file .manifest) = pair.manifest ∧
    visible after (directory.file .walBoundary) = pair.walBoundary ∧
    (∀ bytes manifest, pair.manifest = some bytes → IntegrityCheckpoint.decode bytes = .ok manifest →
      ∀ index, index < manifest.header.runCount.toNat → ∀ payload,
        durable manifest.header.generation index = some payload →
        afterRuns manifest.header.generation index = some payload) ∧
    SelectedIntegrityCheckpoint afterRuns pair.manifest checkpoint := by
  intro afterRuns
  have kept {file : DiskFile}
      (input : file = .manifest ∨ file = .walBoundary ∨ ∃ generation index, file = .run generation index) :
      visible after (directory.file file) = visible initial (directory.file file) := by
    have preserved := finishBoundedMarkedOpen_preservesCheckpointBytes directory plan keeperFileSize visible
      removeFile write sync renameFile removeOther writeOther syncVisible renameOther input initial
    rcases reached with returned | ⟨_, returned⟩ <;> rw [returned] at preserved <;> exact preserved
  have runBytes bytes manifest (binding : pair.manifest = some bytes)
      (decoded : IntegrityCheckpoint.decode bytes = .ok manifest)
      index (within : index < manifest.header.runCount.toNat) payload
      (stored : durable manifest.header.generation index = some payload) :
      afterRuns manifest.header.generation index = some payload := by
    obtain ⟨seen⟩ := observed bytes manifest binding decoded index within payload stored
    have visibleRun := (objectBytes _ _ (sameObject _ _ _ seen.stat)).trans seen.contents
    exact (kept (.inr (.inr ⟨_, _, rfl⟩))).trans visibleRun
  refine ⟨(kept (.inl rfl)).trans visibleManifest, (kept (.inr (.inl rfl))).trans visibleMarker, runBytes, ?_⟩
  cases bindingEq : pair.manifest with
  | none =>
    rw [bindingEq] at selected
    cases selected
    exact .absent
  | some bytes =>
    rw [bindingEq] at selected
    cases selected with
    | @present _ manifest files table decoded stored loaded =>
      exact .present decoded (mapM_preservesRunBytes stored (fun index member =>
        runBytes bytes manifest bindingEq decoded index (List.mem_range.mp member))) loaded

end Alvoki.Storage.WalSegmentRepair
