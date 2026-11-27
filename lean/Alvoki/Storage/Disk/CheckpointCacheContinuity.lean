import Alvoki.Storage.Disk.CheckpointPreflight
import Alvoki.Storage.Disk.StagedHandleCustody
import Alvoki.Storage.Disk.Proofs.Write.WriteGroupFsync

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting

/-- The checkpoint file callbacks before cache routing. The two writers
return the handle whose write and flush completed. Rename, open and fsync
callbacks expose their filesystem effects independently of cache updates. -/
structure CheckpointCacheCalls (handle image : Type) where
  writeRun : FilePath → ByteArray → EStateM IO.Error image handle
  writeStaged : FilePath → ByteArray → EStateM IO.Error image handle
  openRead : FilePath → EStateM IO.Error image handle
  fsync : handle → EStateM IO.Error image Unit
  rename : FilePath → FilePath → EStateM IO.Error image Unit

namespace CheckpointCacheCalls

variable {handle image : Type}

/-- The dispatcher uses the same guarded run write, staged manifest update,
grouped path sync and rename positions as the checkpoint file schedule. -/
noncomputable def callbacks (calls : CheckpointCacheCalls handle image) (directory : DiskDirectory) :
    CheckpointFileCallbacks (Cache handle × image) where
  writeRun := fun path bytes => stageFreshWithCache path bytes calls.writeRun
  writeStaged := fun path bytes => stageFreshWithCache path bytes calls.writeStaged
  sync := SyncPathGroup.run (sync directory.path calls.openRead calls.fsync)
  rename := fun source target (cache, before) => withCache cache (calls.rename source target before)

noncomputable abbrev perform (calls : CheckpointCacheCalls handle image) (directory : DiskDirectory) :=
  (calls.callbacks directory).perform directory

/-- A successful stage remembers the issued handle. An error leaves the
previous pending entries as they were. -/
noncomputable def cacheAfterStage (cache : Cache handle) (path : FilePath) :
    EStateM.Result IO.Error image handle → Cache handle
  | .ok handle _ => cache.remember path handle
  | .error _ _ => cache

/-- Directory selection takes precedence over pending matches. For any
other path, a pending match is consumed before the issued fsync. -/
def cacheAfterSync (cache : Cache handle) (directory path : FilePath) : Cache handle :=
  if path == directory then cache
  else if (cache.pending.find? (fun entry => entry.1 == path)).isSome then cache.consume path else cache

private theorem stageCache (path : FilePath) (bytes : ByteArray)
    (write : FilePath → ByteArray → EStateM IO.Error image handle) (cache : Cache handle) (before : image) :
    (reachedState (stageFreshWithCache path bytes write (cache, before))).1 =
      cacheAfterStage cache path (write path bytes before) := by
  cases returned : write path bytes before <;>
    simp only [stageFreshWithCache, returned, cacheAfterStage, reachedState]

private theorem cacheAfterResolved (directory path : FilePath) (cache : Cache handle) (before : image)
    (openRead : FilePath → EStateM IO.Error image handle) :
    (reachedState (cache.resolve directory path openRead before)).1 = cacheAfterSync cache directory path := by
  by_cases onDirectory : path = directory
  · cases found : cache.directory <;> simp [Cache.resolve, cacheAfterSync, onDirectory, reachedState, found]
  · cases pending : cache.pending.find? (fun entry => entry.1 == path) with
    | some entry => simp [Cache.resolve, cacheAfterSync, onDirectory, pending, reachedState]
    | none =>
      have opened : (reachedState (withCache cache (openRead path before))).1 = cache := by
        cases openRead path before <;> rfl
      cases active : cache.active with
      | none => simp [Cache.resolve, cacheAfterSync, onDirectory, pending, active, opened]
      | some entry =>
        obtain ⟨name, descriptor⟩ := entry
        by_cases same : name = path
        · simp [Cache.resolve, cacheAfterSync, onDirectory, pending, active, same, reachedState]
        · simpa [Cache.resolve, cacheAfterSync, onDirectory, pending, active, same] using opened

private theorem singletonSyncCache (calls : CheckpointCacheCalls handle image) (directory path : FilePath)
    (cache : Cache handle) (before : image) :
    (reachedState (SyncPathGroup.run (sync directory calls.openRead calls.fsync) #[path] (cache, before))).1 =
      cacheAfterSync cache directory path := by
  have selected := cacheAfterResolved directory path cache before calls.openRead
  have synced : (reachedState (sync directory calls.openRead calls.fsync path (cache, before))).1 =
      cacheAfterSync cache directory path := by
    unfold sync
    cases resolved : cache.resolve directory path calls.openRead before with
    | error cause reached => simpa only [resolved, reachedState] using selected
    | ok descriptor reached =>
      obtain ⟨cached, files⟩ := reached
      cases returned : calls.fsync descriptor files <;>
        simpa only [resolved, returned, withCache, reachedState] using selected
  rw [SyncPathGroup.run_single]
  cases returned : sync directory calls.openRead calls.fsync path (cache, before) with
  | error cause reached => simpa only [returned, reachedState] using synced
  | ok value reached => cases value; simpa only [returned, reachedState] using synced

/-- The resulting cache of every issued checkpoint step, including a
returned error. A run-index guard rejection performs no cache action. -/
theorem stepCache (calls : CheckpointCacheCalls handle image) (directory : DiskDirectory)
    (next : Installed) (manifest : ByteArray) (step : Step) (cache : Cache handle) (before : image) :
    (reachedState (calls.perform directory next manifest step (cache, before))).1 =
      match step with
      | .writeRun index =>
        match next.table.runs.toArray[index]? with
        | none => cache
        | some run => cacheAfterStage cache (directory.file (.run next.generation index))
            (calls.writeRun (directory.file (.run next.generation index)) run.run.bytes before)
      | .syncRun index => cacheAfterSync cache directory.path (directory.file (.run next.generation index))
      | .syncRunsDirectory => cache
      | .manifest .writeStaged => cacheAfterStage cache (directory.file .stagedManifest)
          (calls.writeStaged (directory.file .stagedManifest) manifest before)
      | .manifest .syncStaged => cacheAfterSync cache directory.path (directory.file .stagedManifest)
      | .manifest .renameStaged | .manifest .syncDirectory => cache := by
  cases step with
  | writeRun index =>
    cases found : next.table.runs.toArray[index]? with
    | none =>
      simp [CheckpointFileCallbacks.perform, performCheckpointFileStep, found, Bind.bind, EStateM.bind,
        throw, throwThe, MonadExceptOf.throw, EStateM.throw, reachedState]
    | some run =>
      simpa only [CheckpointFileCallbacks.perform, performCheckpointFileStep, found, Bind.bind, EStateM.bind,
        Pure.pure, EStateM.pure, callbacks] using
        stageCache (directory.file (.run next.generation index)) run.run.bytes calls.writeRun cache before
  | syncRun index => exact calls.singletonSyncCache directory.path (directory.file (.run next.generation index)) cache before
  | syncRunsDirectory =>
    change (reachedState (SyncPathGroup.run (sync directory.path calls.openRead calls.fsync)
      #[directory.path] (cache, before))).1 = cache
    simpa only [cacheAfterSync, beq_self_eq_true, ↓reduceIte] using
      calls.singletonSyncCache directory.path directory.path cache before
  | manifest step =>
    cases step with
    | writeStaged => exact stageCache (directory.file .stagedManifest) manifest calls.writeStaged cache before
    | syncStaged => exact calls.singletonSyncCache directory.path (directory.file .stagedManifest) cache before
    | renameStaged =>
      change (reachedState (withCache cache
        (calls.rename (directory.file .stagedManifest) (directory.file .manifest) before))).1 = cache
      cases calls.rename (directory.file .stagedManifest) (directory.file .manifest) before <;> rfl
    | syncDirectory =>
      change (reachedState (SyncPathGroup.run (sync directory.path calls.openRead calls.fsync)
        #[directory.path] (cache, before))).1 = cache
      simpa only [cacheAfterSync, beq_self_eq_true, ↓reduceIte] using
        calls.singletonSyncCache directory.path directory.path cache before

private theorem stageKeepsRoutes (cache : Cache handle) (path : FilePath)
    (result : EStateM.Result IO.Error image handle) :
    (cacheAfterStage cache path result).directory = cache.directory ∧
      (cacheAfterStage cache path result).active = cache.active := by
  cases result <;> exact ⟨rfl, rfl⟩

private theorem syncKeepsRoutes (cache : Cache handle) (directory path : FilePath) :
    (cacheAfterSync cache directory path).directory = cache.directory ∧
      (cacheAfterSync cache directory path).active = cache.active := by
  unfold cacheAfterSync
  split
  · exact ⟨rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl⟩

private theorem stepKeepsRoutes (calls : CheckpointCacheCalls handle image) (directory : DiskDirectory)
    (next : Installed) (manifest : ByteArray) (step : Step) (cache : Cache handle) (before : image) :
    let reached := (reachedState (calls.perform directory next manifest step (cache, before))).1
    reached.directory = cache.directory ∧ reached.active = cache.active := by
  dsimp only
  rw [calls.stepCache]
  cases step with
  | writeRun index =>
    cases found : next.table.runs.toArray[index]? with
    | none => simp [found]
    | some run => simpa only [found] using (stageKeepsRoutes cache
        (directory.file (.run next.generation index))
        (calls.writeRun (directory.file (.run next.generation index)) run.run.bytes before))
  | syncRun _ => exact syncKeepsRoutes cache _ _
  | syncRunsDirectory => exact ⟨rfl, rfl⟩
  | manifest step =>
    cases step with
    | writeStaged => exact stageKeepsRoutes cache _ _
    | syncStaged => exact syncKeepsRoutes cache _ _
    | renameStaged | syncDirectory => exact ⟨rfl, rfl⟩

/-- A returned prefix can stop after any successful step or on the first
error. Both outcomes keep the original directory and active routes. -/
theorem prefixKeepsRoutes (calls : CheckpointCacheCalls handle image) (directory : DiskDirectory)
    (next : Installed) (manifest : ByteArray) (steps : List Step) (before : Cache handle × image) :
    let reached := (reachedState ((steps.forM (calls.perform directory next manifest)) before)).1
    reached.directory = before.1.directory ∧ reached.active = before.1.active := by
  induction steps generalizing before with
  | nil => exact ⟨rfl, rfl⟩
  | cons step rest ih =>
    have current := calls.stepKeepsRoutes directory next manifest step before.1 before.2
    dsimp only at current ⊢
    change (let reached := (reachedState (EStateM.bind (calls.perform directory next manifest step)
      (fun _ => rest.forM (calls.perform directory next manifest)) before)).1
      reached.directory = before.1.directory ∧ reached.active = before.1.active)
    cases returned : calls.perform directory next manifest step before with
    | error cause reached =>
      rw [returned] at current
      simpa only [EStateM.bind, returned, reachedState] using current
    | ok value reached =>
      rw [returned] at current
      have later := ih reached
      simp only [EStateM.bind, returned]
      exact ⟨later.1.trans current.1, later.2.trans current.2⟩

end CheckpointCacheCalls

/-- The precise next publication issue carries the original directory and
active handles without requiring the current step or suffix to return. -/
theorem CheckpointIssue.keepsCacheRoutes {handle image : Type} {directory : DiskDirectory}
    {calls : CheckpointCacheCalls handle image} {phase : Phase Installed}
    {files : LockedFileState (Cache handle × image)} {next : Installed} {manifest : ByteArray}
    {completed : List Step} {current : Step} {reached : Cache handle × image}
    (issue : CheckpointIssue (calls.perform directory) phase files next manifest completed current reached) :
    reached.1.directory = files.image.1.directory ∧ reached.1.active = files.image.1.active := by
  have atIssue := issue.atIssue
  simp only [runCheckpointActions, Bind.bind, EStateM.bind, modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet] at atIssue
  have routes := calls.prefixKeepsRoutes directory next manifest completed files.image
  cases returned : (completed.forM (calls.perform directory next manifest)) files.image with
  | error cause stopped =>
    rw [returned] at atIssue
    contradiction
  | ok value stopped =>
    rw [returned] at atIssue
    have same : stopped = reached := by
      exact congrArg (fun (state : Phase Installed × LockedFileState (Cache handle × image)) => state.2.image)
        (EStateM.Result.ok.inj atIssue).2
    simpa only [returned, reachedState, same] using routes

/-- A fully returned checkpoint uses the same route frame. A rejected
preflight performs no file dispatch, and a publication error returns the
cache reached at its first failing callback. -/
theorem CheckpointCacheCalls.checkpointKeepsRoutes {handle image : Type}
    (calls : CheckpointCacheCalls handle image) (directory : DiskDirectory)
    (phase : Phase Installed) (files : LockedFileState (Cache handle × image)) :
    let after := (reachedState (runCheckpointWithEffects (calls.perform directory) (phase, files))).2.image.1
    after.directory = files.image.1.directory ∧ after.active = files.image.1.active := by
  obtain ⟨prepared, preflight⟩ := CheckpointPreflight.total phase
  have effect := preflight.effect (calls.perform directory) files
  dsimp only
  rw [effect]
  cases prepared with
  | error cause => exact ⟨rfl, rfl⟩
  | ok preparation =>
    obtain ⟨next, manifest⟩ := preparation
    have routes := calls.prefixKeepsRoutes directory next manifest (steps next.table.runs.length) files.image
    simp only [runPreparedCheckpoint, runCheckpointActions, CheckpointPublication.run, Bind.bind, EStateM.bind,
      modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
    cases returned : ((steps next.table.runs.length).forM (calls.perform directory next manifest)) files.image <;>
      simpa only [returned, reachedState] using routes

end Alvoki.Storage.DiskSession
