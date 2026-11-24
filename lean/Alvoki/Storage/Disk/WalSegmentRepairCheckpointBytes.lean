import Alvoki.Storage.Disk.WalSegmentBoundedOpen
import Alvoki.Storage.Disk.CheckpointRunChunkReports
import Alvoki.Storage.Disk.WalSegmentCachedRetryCompletion

namespace Alvoki.Storage.WalSegmentRepair

open System Manifest CheckpointPublication DiskSession
open WAL.Boundary (CheckpointRepresentsPrefix)

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

private def preserves {state output : Type} (property : state → Prop)
    (action : EStateM IO.Error state output) : Prop :=
  ∀ before, property before → property (reachedState (action before))

private theorem preserves_bind {state input output : Type} {property : state → Prop}
    {action : EStateM IO.Error state input} {next : input → EStateM IO.Error state output}
    (first : preserves property action) (remaining : ∀ result, preserves property (next result)) :
    preserves property (action >>= next) := by
  intro before known
  have firstKeeps := first before known
  cases reached : action before with
  | error cause after => simpa [Bind.bind, EStateM.bind, reached, reachedState] using firstKeeps
  | ok result after =>
    rw [reached] at firstKeeps
    simpa only [Bind.bind, EStateM.bind, reached] using remaining result after firstKeeps

private theorem finisher_preserves {state : Type} (directory : DiskDirectory) (plan : Plan)
    (keeperFileSize : Nat) (property : state → Prop)
    (removeFile : FilePath → EStateM IO.Error state (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error state Unit)
    (sync : Array FilePath → EStateM IO.Error state Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error state Unit)
    (unlink : ∀ first, preserves property (removeFile (directory.file (.walSegment first))))
    (stage : ∀ bytes, preserves property (write (directory.file .stagedWal) bytes))
    (syncs : ∀ paths, preserves property (sync paths))
    (rename : ∀ first, preserves property (renameFile (directory.file .stagedWal) (directory.file (.walSegment first)))) :
    preserves property (finishBoundedMarkedOpen directory plan keeperFileSize removeFile write sync renameFile) := by
  have stepKeeps (step : Step) :
      preserves property (performPaths directory plan removeFile throw write sync renameFile step) := by
    cases step with
    | unlink first =>
      unfold performPaths RunCollection.performPaths
      apply preserves_bind (unlink first)
      intro removed
      cases result : RunCollection.ownedUnlinkResult removed <;> exact fun _ known => known
    | syncPruned | syncKeeper => exact syncs _
    | replace callback =>
      cases callback with
      | writeStaged => exact stage _
      | syncStaged | syncDirectory => exact syncs _
      | renameStaged => exact rename _
  have stepsKeep (steps : List Step) :
      preserves property (steps.forM (performPaths directory plan removeFile throw write sync renameFile)) := by
    induction steps with
    | nil => exact fun _ known => known
    | cons step rest ih =>
      change preserves property (performPaths directory plan removeFile throw write sync renameFile step >>= fun _ =>
        rest.forM (performPaths directory plan removeFile throw write sync renameFile))
      exact preserves_bind (stepKeeps step) (fun _ => ih)
  have repair (replaceKeeper : Bool) : preserves property
      (runRepairPlan directory plan replaceKeeper removeFile write sync renameFile) :=
    preserves_bind (syncs #[directory.path])
      (fun _ => stepsKeep (steps plan.newer replaceKeeper))
  unfold finishBoundedMarkedOpen
  split
  · split
    · exact preserves_bind (syncs #[directory.path]) (fun _ => syncs #[directory.file (.walSegment plan.keeper)])
    · exact fun _ known => known
  · split
    · exact repair _
    · exact fun _ known => known

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
  have stageAway := stagedWal_ne_checkpoint directory checkpoint
  have keeperAway first := walSegment_ne_checkpoint directory checkpoint first
  have unchanged := finisher_preserves directory plan keeperFileSize
    (fun state => visible state path = visible initial path) removeFile write sync renameFile
    (fun first before known => (removeOther _ path (keeperAway first) before).trans known)
    (fun bytes before known => (writeOther _ bytes path stageAway before).trans known)
    (fun paths before known => (syncVisible paths path before).trans known)
    (fun first before known => (renameOther _ _ path stageAway (keeperAway first) before).trans known)
    initial rfl
  cases report : finishBoundedMarkedOpen directory plan keeperFileSize removeFile write sync renameFile initial with
  | ok result after => cases result; simpa [report, reachedState] using unchanged
  | error cause after => simpa [report, reachedState] using unchanged

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

private theorem selectedWithKnownRuns {known after : RunFiles} {binding : Option ByteArray}
    {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint known binding checkpoint)
    (kept : ∀ bytes manifest, binding = some bytes → IntegrityCheckpoint.decode bytes = .ok manifest →
      ∀ index, index < manifest.header.runCount.toNat → ∀ payload,
        known manifest.header.generation index = some payload → after manifest.header.generation index = some payload) :
    SelectedIntegrityCheckpoint after binding checkpoint := by
  cases selected with
  | absent => exact .absent
  | @present bytes manifest files table decoded stored loaded =>
    exact .present decoded (mapM_preservesRunBytes stored (fun index member =>
      kept bytes manifest rfl decoded index (List.mem_range.mp member))) loaded

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
  exact ⟨(kept (.inl rfl)).trans visibleManifest, (kept (.inr (.inl rfl))).trans visibleMarker, runBytes,
    selectedWithKnownRuns selected runBytes⟩

/-- Run names and already durable bytes survive bounded WAL repair, including
effects reached before an error. An observed directory sync may settle the
run namespace. Every admitted later run image then loads the same checkpoint
for this manifest binding. -/
theorem finishBoundedMarkedOpen_preservesDurableCheckpoint {state : Type}
    (directory : DiskDirectory) (plan : Plan) (keeperFileSize : Nat) (runs : state → RunUnlinkImage)
    (removeFile : FilePath → EStateM IO.Error state (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error state Unit)
    (sync : Array FilePath → EStateM IO.Error state Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error state Unit)
    (unlink : ∀ first before, runs (reachedState (removeFile (directory.file (.walSegment first)) before)) = runs before)
    (stage : ∀ bytes before, runs (reachedState (write (directory.file .stagedWal) bytes before)) = runs before)
    (rename : ∀ first before, runs (reachedState
      (renameFile (directory.file .stagedWal) (directory.file (.walSegment first)) before)) = runs before)
    (syncs : ∀ paths before, runs (reachedState (sync paths before)) = runs before ∨
      directory.path ∈ paths.toList ∧ runs (reachedState (sync paths before)) = (runs before).syncDirectory)
    (initial after : state)
    (reached : finishBoundedMarkedOpen directory plan keeperFileSize removeFile write sync renameFile initial =
      .ok () after ∨ ∃ cause, finishBoundedMarkedOpen directory plan keeperFileSize removeFile write sync renameFile
        initial = .error cause after)
    {binding : Option ByteArray} {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint (runs initial).guaranteed binding checkpoint) :
    SelectedIntegrityCheckpoint (runs after).guaranteed binding checkpoint ∧
    ∀ survived ∈ (runs after).crashImages, SelectedIntegrityCheckpoint survived binding checkpoint := by
  let property (state : state) := SelectedIntegrityCheckpoint (runs state).guaranteed binding checkpoint
  have syncKeeps (paths) : preserves property (sync paths) := by
    intro before known
    change SelectedIntegrityCheckpoint (runs (reachedState (sync paths before))).guaranteed binding checkpoint
    rcases syncs paths before with same | ⟨_, settled⟩
    · rw [same]
      exact known
    · rw [settled]
      exact selectedWithKnownRuns known (fun _ manifest _ _ index _ _ stored =>
        (RunUnlinkRetry.sync (approved := []) (.start (runs before))).keepsKnown
          (name := (manifest.header.generation, index)) stored (by simp))
  have preserved := finisher_preserves directory plan keeperFileSize property removeFile write sync renameFile
    (fun first before known => by simpa only [property, unlink first before] using known)
    (fun bytes before known => by simpa only [property, stage bytes before] using known)
    syncKeeps
    (fun first before known => by simpa only [property, rename first before] using known)
    initial selected
  have current : SelectedIntegrityCheckpoint (runs after).guaranteed binding checkpoint := by
    dsimp only [property] at preserved
    rcases reached with returned | ⟨_, returned⟩ <;> rw [returned] at preserved <;> exact preserved
  refine ⟨current, ?_⟩
  intro survived chosen
  have survivedRuns : (RunUnlinkImage.settled survived).guaranteed = survived :=
    congrArg Image.durable (RunUnlinkImage.project_settled survived (.settled binding))
  rw [← survivedRuns]
  exact selectedWithKnownRuns current (fun _ manifest _ _ index _ _ stored =>
    (RunUnlinkRetry.crash (approved := []) (.start (runs after)) chosen).keepsKnown
      (name := (manifest.header.generation, index)) stored (by simp))

/-- Projections of the same reached filesystem state. WAL mutations leave
both namespaces alone. A directory sync can settle them, including before
a reported error. The callbacks are the ones used by the cached worker. -/
structure CachedCheckpointRepairEffects (state : Type) (directory : DiskDirectory) where
  metadata : state → DirectoryPublication.Image
  runs : state → RunUnlinkImage
  removeFile : FilePath → EStateM IO.Error state (Except IO.Error Unit)
  write : FilePath → ByteArray → EStateM IO.Error state Unit
  sync : Array FilePath → EStateM IO.Error state Unit
  renameFile : FilePath → FilePath → EStateM IO.Error state Unit
  unlink : ∀ first before,
    let after := reachedState (removeFile (directory.file (.walSegment first)) before)
    metadata after = metadata before ∧ runs after = runs before
  stage : ∀ bytes before,
    let after := reachedState (write (directory.file .stagedWal) bytes before)
    metadata after = metadata before ∧ runs after = runs before
  rename : ∀ first before,
    let after := reachedState (renameFile (directory.file .stagedWal) (directory.file (.walSegment first)) before)
    metadata after = metadata before ∧ runs after = runs before
  syncs : ∀ paths before,
    let after := reachedState (sync paths before)
    (metadata after = metadata before ∨
      directory.path ∈ paths.toList ∧ metadata after = (metadata before).syncDirectory) ∧
    (runs after = runs before ∨ directory.path ∈ paths.toList ∧ runs after = (runs before).syncDirectory)

def CachedCheckpointRepairEffects.reopen {state : Type} {directory : DiskDirectory}
    {image : FileImage} {history : List WAL.Write} {layout : CanonicalKeeperLayout image history}
    (effects : CachedCheckpointRepairEffects state directory) (reported : CachedRetryReadReports directory layout)
    (readRunPrefix : FilePath → Nat → Except IO.Error ByteArray) : EStateM IO.Error state Reopened :=
  reopenMarkedBoundedWithCachedExtents directory
    (fun path => liftExcept (reported.inventory.reports.readOptional path))
    (fun path => liftExcept (checkpointRunSizeReport reported.inventory.reports path))
    (fun path size => liftExcept (readRunPrefix path size))
    (fun path => liftExcept (reported.list path))
    (fun path => liftExcept (.ok (reported.inventory.reports.lstat path) : Except IO.Error _))
    (fun path size => liftExcept (reported.readSeal path size))
    (fun path size physical => liftExcept (reported.readKeeper path size physical))
    effects.removeFile effects.write effects.sync effects.renameFile

/-- A cached retry of an already settled pair reads its exact checkpoint
before repair. Even on a reported repair error, the same physical crash
outcome selects that pair and contains the same ordered durable run bytes.
The two crash observations refer to one state. -/
theorem CachedRetryReadReports.checkpointSurvivesRepair {state : Type} {directory : DiskDirectory}
    {image : FileImage} {history : List WAL.Write} {layout : CanonicalKeeperLayout image history}
    (reported : CachedRetryReadReports directory layout) (effects : CachedCheckpointRepairEffects state directory)
    (initial after : state) (observedDirectory : effects.metadata initial = image.directory)
    (settled : image.directory.crashImages = [image.directory.active])
    (laterValid : image.later.Beyond layout.range.through)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : (⟨image.directory.project .manifest, (effects.runs initial).guaranteed⟩ : Image).AcceptsVersioned
      history.length.toUInt64 (CheckpointRepresentsPrefix history) image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    (sizes : SizedCheckpointRunReports directory reported.inventory.reports image.directory.active.manifest
      (effects.runs initial).guaranteed)
    (manifestRead : reported.inventory.reports.readOptional (directory.file .manifest) = .ok image.directory.active.manifest)
    (markerRead : reported.inventory.reports.readOptional (directory.file .walBoundary) = .ok image.directory.active.walBoundary)
    (reached : reachedState (effects.reopen reported sizes.readPrefix initial) = after) :
    ∃ opened checkpoint,
      (effects.reopen reported sizes.readPrefix initial = .ok opened after ∨
        ∃ cause, effects.reopen reported sizes.readPrefix initial = .error cause after) ∧
      recoverSelected (checkpoint.getD (.empty, 0)).1 (WAL.encode history) = .ok opened.table ∧
      opened.generation = (checkpoint.getD (.empty, 0)).2 ∧
      opened.walBytes.toNat = history.length * WAL.frameSize ∧
      opened.keeper = layout.keeper.first ∧
      effects.metadata after = image.directory ∧
      SelectedIntegrityCheckpoint (effects.runs after).guaranteed image.directory.active.manifest checkpoint ∧
      ∀ crashed : state,
        (effects.metadata crashed).active ∈ (effects.metadata after).crashImages →
        (effects.runs crashed).visible ∈ (effects.runs after).crashImages →
        (effects.metadata crashed).active = image.directory.active ∧
        SelectedIntegrityCheckpoint (effects.runs crashed).visible (effects.metadata crashed).active.manifest checkpoint := by
  obtain ⟨opened, checkpoint, _, prepared, selected, replay, generation, bytes, keeper, _⟩ :=
    reported.prepares initial laterValid following accepted ordered sizes manifestRead markerRead
  let finish := finishBoundedMarkedOpen directory layout.boundedPlan layout.plan.keeperBytes.size
    effects.removeFile effects.write effects.sync effects.renameFile
  have ran : effects.reopen reported sizes.readPrefix initial =
      match finish initial with
      | .ok _ next => .ok opened next
      | .error cause next => .error cause next := by
    change EStateM.bind (reported.prepare sizes.readPrefix)
      (fun (plan, prepared, size) => do
        finishBoundedMarkedOpen directory plan size effects.removeFile effects.write effects.sync effects.renameFile
        return prepared) initial = _
    simp only [EStateM.bind, prepared, Bind.bind, Pure.pure, EStateM.pure, finish]
    cases finishBoundedMarkedOpen directory layout.boundedPlan layout.plan.keeperBytes.size
      effects.removeFile effects.write effects.sync effects.renameFile initial <;> rfl
  have result : (effects.reopen reported sizes.readPrefix initial = .ok opened after ∨
      ∃ cause, effects.reopen reported sizes.readPrefix initial = .error cause after) ∧
      (finish initial = .ok () after ∨ ∃ cause, finish initial = .error cause after) := by
    rw [ran] at reached ⊢
    cases phase : finish initial with
    | ok value next =>
      cases value
      rw [phase] at reached
      change next = after at reached
      subst after
      exact ⟨.inl rfl, .inl rfl⟩
    | error cause next =>
      rw [phase] at reached
      change next = after at reached
      subst after
      exact ⟨.inr ⟨cause, rfl⟩, .inr ⟨cause, rfl⟩⟩
  have directoryFixed : image.directory.syncDirectory = image.directory := by
    unfold DirectoryPublication.Image.syncDirectory
    rw [← settled]
  let property (state : state) := effects.metadata state = image.directory
  have syncKeeps paths : preserves property (effects.sync paths) := by
    intro before same
    rcases (effects.syncs paths before).1 with unchanged | ⟨_, settled⟩
    · exact unchanged.trans same
    · change effects.metadata (reachedState (effects.sync paths before)) = image.directory
      change effects.metadata before = image.directory at same
      rw [settled, same, directoryFixed]
  have preserved := finisher_preserves directory layout.boundedPlan layout.plan.keeperBytes.size property
    effects.removeFile effects.write effects.sync effects.renameFile
    (fun first before same => (effects.unlink first before).1.trans same)
    (fun bytes before same => (effects.stage bytes before).1.trans same)
    syncKeeps
    (fun first before same => (effects.rename first before).1.trans same)
    initial observedDirectory
  have sameDirectory : effects.metadata after = image.directory := by
    change property (reachedState (finish initial)) at preserved
    rcases result.2 with returned | ⟨_, returned⟩ <;> rw [returned] at preserved <;> exact preserved
  have durable := finishBoundedMarkedOpen_preservesDurableCheckpoint
    directory layout.boundedPlan layout.plan.keeperBytes.size effects.runs
    effects.removeFile effects.write effects.sync effects.renameFile
    (fun first before => (effects.unlink first before).2) (fun bytes before => (effects.stage bytes before).2)
    (fun first before => (effects.rename first before).2) (fun paths before => (effects.syncs paths before).2)
    initial after result.2 selected
  refine ⟨opened, checkpoint, result.1, replay, generation, bytes, keeper, sameDirectory, durable.1, ?_⟩
  intro crashed metadataSurvives runSurvives
  rw [sameDirectory, settled] at metadataSurvives
  have samePair := List.mem_singleton.mp metadataSurvives
  exact ⟨samePair, samePair.symm ▸ durable.2 _ runSurvives⟩

/-- A failed first directory barrier ends the cached worker before it
can prune or replace anything. Before the effect, a crash can still
select any original pair. After the effect, it can select only the pair
used by preparation. The run and metadata observations are from the
same crash state. Each originally selectable pair needs its own durable
checkpoint witness. -/
theorem CachedRetryReadReports.checkpointAfterAuthorizationError
    {state : Type} {directory : DiskDirectory} {image : FileImage} {history : List WAL.Write}
    {layout : CanonicalKeeperLayout image history}
    (reported : CachedRetryReadReports directory layout) (effects : CachedCheckpointRepairEffects state directory)
    {initial after : state} (observedDirectory : effects.metadata initial = image.directory)
    (laterValid : image.later.Beyond layout.range.through)
    (following : ∀ start ∈ ((layout.sealed ++ [layout.keeper]).map WalSegment.first).drop 1,
      layout.range.watermark < start)
    (accepted : (⟨image.directory.project .manifest, (effects.runs initial).guaranteed⟩ : Image).AcceptsVersioned
      history.length.toUInt64 (CheckpointRepresentsPrefix history) image.directory.active.manifest)
    (ordered : WAL.OrdinalsFrom 1 history)
    (sizes : SizedCheckpointRunReports directory reported.inventory.reports image.directory.active.manifest
      (effects.runs initial).guaranteed)
    (manifestRead : reported.inventory.reports.readOptional (directory.file .manifest) = .ok image.directory.active.manifest)
    (markerRead : reported.inventory.reports.readOptional (directory.file .walBoundary) = .ok image.directory.active.walBoundary)
    (previous : ∀ pair ∈ image.directory.crashImages, ∃ checkpoint,
      SelectedIntegrityCheckpoint (effects.runs initial).guaranteed pair.manifest checkpoint)
    {cause : IO.Error} (failed : effects.sync #[directory.path] initial = .error cause after) :
    (effects.reopen reported sizes.readPrefix initial = .error cause after) ∧
    (effects.metadata after = image.directory ∨ effects.metadata after = image.directory.syncDirectory) ∧
    ∃ opened checkpoint,
      reported.prepare sizes.readPrefix initial = .ok (layout.boundedPlan, opened, layout.plan.keeperBytes.size) initial ∧
      SelectedIntegrityCheckpoint (effects.runs initial).guaranteed image.directory.active.manifest checkpoint ∧
      recoverSelected (checkpoint.getD (.empty, 0)).1 (WAL.encode history) = .ok opened.table ∧
      opened.generation = (checkpoint.getD (.empty, 0)).2 ∧
      opened.walBytes.toNat = history.length * WAL.frameSize ∧ opened.keeper = layout.keeper.first ∧
      ∀ crashed : state,
        (effects.metadata crashed).active ∈ (effects.metadata after).crashImages →
        (effects.runs crashed).visible ∈ (effects.runs after).crashImages →
        ∃ recovered,
          SelectedIntegrityCheckpoint (effects.runs crashed).visible (effects.metadata crashed).active.manifest recovered ∧
          ((effects.metadata crashed).active.manifest = image.directory.active.manifest → recovered = checkpoint) := by
  obtain ⟨opened, checkpoint, _, prepared, selected, replay, generation, bytes, keeper, _⟩ :=
    reported.prepares initial laterValid following accepted ordered sizes manifestRead markerRead
  have size : layout.plan.keeperSize = layout.keeper.bytes.size := layout.target.trimmedSize.symm
  have valid : layout.plan.valid = true := by
    refine (Plan.valid_iff _).mpr ⟨layout.target.firstCovered, ?_, laterValid _ List.mem_cons_self⟩
    rw [size]
    simp [CanonicalKeeperLayout.plan, ByteArray.size_append]
  have stopped : finishBoundedMarkedOpen directory layout.boundedPlan layout.plan.keeperBytes.size
      effects.removeFile effects.write effects.sync effects.renameFile initial = .error cause after := by
    rw [layout.boundedPlan_eq_extract, finishBoundedMarkedOpen_eq_full _ _ valid]
    by_cases aligned : layout.plan.alignedWithoutPrune = true
    · simp only [finishMarkedOpen, aligned, ite_true, Bind.bind, EStateM.bind, failed]
    · simp only [finishMarkedOpen, ite_eq_right aligned, runAt, runRepairPlan, Bind.bind, EStateM.bind, Pure.pure,
        EStateM.pure, valid, ite_true, failed]
  have outcome : effects.reopen reported sizes.readPrefix initial = .error cause after := by
    change EStateM.bind (reported.prepare sizes.readPrefix)
      (fun (plan, prepared, size) => do
        finishBoundedMarkedOpen directory plan size effects.removeFile effects.write effects.sync effects.renameFile
        return prepared) initial = _
    simp only [EStateM.bind, prepared, Bind.bind, stopped]
  have metadata := (effects.syncs #[directory.path] initial).1
  rw [failed] at metadata
  change effects.metadata after = effects.metadata initial ∨
    directory.path ∈ (#[directory.path] : Array FilePath).toList ∧
      effects.metadata after = (effects.metadata initial).syncDirectory at metadata
  have directories : effects.metadata after = image.directory ∨ effects.metadata after = image.directory.syncDirectory :=
    metadata.elim (fun unchanged => .inl (unchanged.trans observedDirectory))
      (fun settled => .inr (settled.2.trans (congrArg DirectoryPublication.Image.syncDirectory observedDirectory)))
  refine ⟨outcome, directories, opened, checkpoint, prepared, selected, replay, generation, bytes, keeper, ?_⟩
  intro crashed metadataSurvives runsSurvive
  have choice : ∃ recovered,
      SelectedIntegrityCheckpoint (effects.runs initial).guaranteed (effects.metadata crashed).active.manifest recovered ∧
      ((effects.metadata crashed).active.manifest = image.directory.active.manifest → recovered = checkpoint) := by
    by_cases sameManifest : (effects.metadata crashed).active.manifest = image.directory.active.manifest
    · exact ⟨checkpoint, sameManifest.symm ▸ selected, fun _ => rfl⟩
    rcases directories with unchanged | synced
    · rw [unchanged] at metadataSurvives
      obtain ⟨recovered, priorCheckpoint⟩ := previous _ metadataSurvives
      exact ⟨recovered, priorCheckpoint, fun same => (sameManifest same).elim⟩
    · rw [synced] at metadataSurvives
      have pair := (DirectoryPublication.Image.survives_syncDirectory_iff _ _).mp metadataSurvives
      exact (sameManifest (congrArg DirectoryPublication.Bindings.manifest pair)).elim
  obtain ⟨recovered, initialCheckpoint, matching⟩ := choice
  have durable := finishBoundedMarkedOpen_preservesDurableCheckpoint
    directory layout.boundedPlan layout.plan.keeperBytes.size effects.runs
    effects.removeFile effects.write effects.sync effects.renameFile
    (fun first before => (effects.unlink first before).2) (fun bytes before => (effects.stage bytes before).2)
    (fun first before => (effects.rename first before).2) (fun paths before => (effects.syncs paths before).2)
    initial after (.inr ⟨cause, stopped⟩) initialCheckpoint
  exact ⟨recovered, durable.2 _ runsSurvive, matching⟩

end Alvoki.Storage.WalSegmentRepair
