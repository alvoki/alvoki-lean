import Alvoki.Storage.Disk.Proofs.Checkpoint.CheckpointCacheContinuity
import Alvoki.Storage.Disk.Proofs.Checkpoint.CheckpointRunWriteCustody

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication SyncHandleRouting

/-- The file primitives used by one checkpoint, before pending-handle
routing. Run and manifest writes use the same data callbacks. -/
structure CheckpointPrimitiveCalls (handle image : Type) where
  lookup : FilePath → EStateM IO.Error image (Except IO.Error IO.FS.Metadata)
  openRun : FilePath → EStateM IO.Error image handle
  tryCreateStage : FilePath → EStateM IO.Error image (Except IO.Error handle)
  unlink : FilePath → EStateM IO.Error image (Except IO.Error Unit)
  createStage : FilePath → EStateM IO.Error image handle
  write : handle → ByteArray → EStateM IO.Error image Unit
  flush : handle → EStateM IO.Error image Unit
  drop : handle → EStateM IO.Error image Unit
  openRead : FilePath → EStateM IO.Error image handle
  fsync : handle → EStateM IO.Error image Unit
  rename : FilePath → FilePath → EStateM IO.Error image Unit

namespace CheckpointPrimitiveCalls

variable {handle image : Type}

/-- A returned write or flush error keeps its original cause and the
reported effects of dropping that handle. Successful data callbacks pass
the same handle to the cache. -/
noncomputable def cached (calls : CheckpointPrimitiveCalls handle image) : CheckpointCacheCalls handle image where
  writeRun := fun path bytes => writeCheckpointRunWith calls.lookup calls.openRun
    (fun h bytes => withDataErrorDrop calls.drop h (calls.write h bytes))
    (fun h => withDataErrorDrop calls.drop h (calls.flush h)) path bytes pure
  writeStaged := writeFreshStagedWith calls.tryCreateStage (removeStaleStagingWith calls.lookup calls.unlink)
    calls.createStage (fun h bytes => withDataErrorDrop calls.drop h (calls.write h bytes))
    (fun h => withDataErrorDrop calls.drop h (calls.flush h))
  openRead := calls.openRead
  fsync := calls.fsync
  rename := calls.rename

/-- The reported run guard, open and data returns derive the raw handle
result used by the common cached dispatcher. -/
theorem wroteRun (calls : CheckpointPrimitiveCalls handle image) {path : FilePath} {bytes : ByteArray}
    {before opened buffered flushed : image} {descriptor : handle}
    (guard : AcceptedRunGuard calls.lookup path before)
    (opening : calls.openRun path before = .ok descriptor opened)
    (written : calls.write descriptor bytes opened = .ok () buffered)
    (returned : calls.flush descriptor buffered = .ok () flushed) :
    calls.cached.writeRun path bytes before = .ok descriptor flushed := by
  let observed : RunWriteReports path bytes before flushed descriptor :=
    ⟨calls.lookup, calls.openRun, fun h bytes => withDataErrorDrop calls.drop h (calls.write h bytes),
      fun h => withDataErrorDrop calls.drop h (calls.flush h), guard, opened, buffered, opening,
      by simp only [withDataErrorDrop, written], by simp only [withDataErrorDrop, returned]⟩
  exact observed.captures

/-- The returned pending entry comes from the original installed run
array and the handle used by its guarded write and flush. -/
theorem remembersRun (calls : CheckpointPrimitiveCalls handle image) (directory : DiskDirectory)
    (next : Installed) (manifest : ByteArray) {index : Nat} {run : Compaction.CheckedRun}
    (selected : next.table.runs.toArray[index]? = some run)
    (cache : Cache handle) {before opened buffered flushed : image} {descriptor : handle} :
    let path := directory.file (.run next.generation index)
    AcceptedRunGuard calls.lookup path before →
    calls.openRun path before = .ok descriptor opened →
    calls.write descriptor run.run.bytes opened = .ok () buffered →
    calls.flush descriptor buffered = .ok () flushed →
    calls.cached.perform directory next manifest (.writeRun index) (cache, before) =
      .ok () (cache.remember path descriptor, flushed) := by
  intro path guard opening written returned
  have wrote := calls.wroteRun guard opening written returned
  simp only [CheckpointCacheCalls.perform, CheckpointFileCallbacks.perform, performCheckpointFileStep,
    selected, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, CheckpointCacheCalls.callbacks]
  change stageFreshWithCache path run.run.bytes calls.cached.writeRun (cache, before) = _
  rw [stageFreshWithCache, wrote]

/-- The reached exclusive staging open can return immediately or succeed
after EEXIST and the reported stale-name cleanup. -/
inductive StageOpened (calls : CheckpointPrimitiveCalls handle image) (path : FilePath) (before : image) :
    handle → image → Prop where
  | first (opened : calls.tryCreateStage path before = .ok (.ok descriptor) reached) :
      StageOpened calls path before descriptor reached
  | afterStale {name details : String}
      (exists' : calls.tryCreateStage path before = .ok (.error (.alreadyExists name 17 details)) conflict)
      (detached : removeStaleStagingWith calls.lookup calls.unlink path conflict = .ok () cleaned)
      (opened : calls.createStage path cleaned = .ok descriptor reached) :
      StageOpened calls path before descriptor reached

/-- Staging returns the same exclusively opened handle through both data
callbacks, using the shared acquisition and stale-detach schedule. -/
theorem wroteStage (calls : CheckpointPrimitiveCalls handle image) {path : FilePath} {bytes : ByteArray}
    {before opened buffered flushed : image} {descriptor : handle}
    (opening : calls.StageOpened path before descriptor opened)
    (written : calls.write descriptor bytes opened = .ok () buffered)
    (returned : calls.flush descriptor buffered = .ok () flushed) :
    calls.cached.writeStaged path bytes before = .ok descriptor flushed := by
  cases opening with
  | first succeeds =>
    simp [cached, writeFreshStagedWith, withFreshStaging, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
      succeeds, withDataErrorDrop, written, returned]
  | afterStale exists' detached succeeds =>
    simp [cached, writeFreshStagedWith, withFreshStaging, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
      exists', detached, succeeds, withDataErrorDrop, written, returned]

/-- The reached manifest stage records the returned handle under the
canonical staged-manifest path for the next barrier. -/
theorem remembersManifest (calls : CheckpointPrimitiveCalls handle image) (directory : DiskDirectory)
    (next : Installed) (manifest : ByteArray) (cache : Cache handle)
    {before opened buffered flushed : image} {descriptor : handle} :
    let path := directory.file .stagedManifest
    calls.StageOpened path before descriptor opened →
    calls.write descriptor manifest opened = .ok () buffered →
    calls.flush descriptor buffered = .ok () flushed →
    calls.cached.perform directory next manifest (.manifest .writeStaged) (cache, before) =
      .ok () (cache.remember path descriptor, flushed) := by
  intro path opening written returned
  change stageFreshWithCache path manifest calls.cached.writeStaged (cache, before) = _
  rw [stageFreshWithCache, calls.wroteStage opening written returned]

end CheckpointPrimitiveCalls
end Alvoki.Storage.DiskSession
