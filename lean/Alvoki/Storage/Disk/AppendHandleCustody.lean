import Alvoki.Storage.Disk.StagedHandleCustody

namespace Alvoki.Storage.SyncHandleRouting

open System

/-- Interpret the native append helper's reference reads and writes as
cache actions. The remaining callbacks report filesystem effects. -/
def runAppendWithCache {handle state : Type} (path : FilePath) (bytes : ByteArray)
    (openAppend : FilePath → EStateM IO.Error state handle)
    (write : handle → ByteArray → EStateM IO.Error state Unit) (flush : handle → EStateM IO.Error state Unit) :
    EStateM IO.Error (Cache handle × state) Unit :=
  appendWithActive (fun before => .ok before.1.active before)
    (fun active (cache, files) => .ok () ({ cache with active }, files))
    (fun name (cache, files) => withCache cache (openAppend name files))
    (fun file value (cache, files) => withCache cache (write file value files))
    (fun file (cache, files) => withCache cache (flush file files))
    path bytes

private theorem selectAppendHandle_withCache {handle state : Type} (cache : Cache handle)
    (path : FilePath) (openAppend : FilePath → EStateM IO.Error state handle) (before : state) :
    selectAppendHandle (m := EStateM IO.Error (Cache handle × state)) cache.active
      (fun name (cache, files) => withCache cache (openAppend name files)) path
      (cache, before) = withCache cache (selectAppendHandle cache.active openAppend path before) := by
  cases active : cache.active with
  | none => rfl
  | some entry =>
    obtain ⟨name, file⟩ := entry
    by_cases same : path = name <;>
      simp [selectAppendHandle, same, Pure.pure, EStateM.pure, withCache]

/-- An open failure reaches no write or cache update. After a write or
flush error the active entry is cleared, and the returned state includes
the filesystem effects reached before that error. Only complete success
installs the captured handle for the next durability barrier. -/
theorem runAppendWithCache_effect {handle state : Type} (cache : Cache handle) (before : state)
    (path : FilePath) (bytes : ByteArray) (openAppend : FilePath → EStateM IO.Error state handle)
    (write : handle → ByteArray → EStateM IO.Error state Unit) (flush : handle → EStateM IO.Error state Unit) :
    runAppendWithCache path bytes openAppend write flush (cache, before) =
      match selectAppendHandle cache.active openAppend path before with
      | .error cause reached => .error cause (cache, reached)
      | .ok file opened => match write file bytes opened with
        | .error cause reached => .error cause ({ cache with active := none }, reached)
        | .ok () written => match flush file written with
          | .error cause reached => .error cause ({ cache with active := none }, reached)
          | .ok () reached => .ok () ({ cache with active := some (path, file) }, reached) := by
  simp only [runAppendWithCache, appendWithActive, Bind.bind, EStateM.bind]
  rw [selectAppendHandle_withCache]
  cases selected : selectAppendHandle cache.active openAppend path before with
  | error => rfl
  | ok file opened =>
    cases writing : write file bytes opened with
    | error =>
      simp [withCache, writing, MonadExcept.tryCatch, MonadExceptOf.tryCatch, tryCatchThe, EStateM.tryCatch,
        EStateM.bind, EStateM.Backtrackable.restore, EStateM.dummyRestore, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
    | ok result written =>
      cases result
      cases flushing : flush file written <;>
        simp [withCache, writing, flushing, MonadExcept.tryCatch, MonadExceptOf.tryCatch, tryCatchThe, EStateM.tryCatch,
          EStateM.bind, EStateM.Backtrackable.restore, EStateM.dummyRestore, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-- A selected append using the retained handle matches the active binding.
On a cache miss, the observed open supplies the corresponding identity. -/
theorem Cache.selectAppend_owned {handle state : Type} {cache : Cache handle} {dir path : FilePath}
    (openAppend : FilePath → EStateM IO.Error state handle) (bindings : state → FilePath → Option Nat)
    (inode : handle → Nat) {before opened : state} {file : handle}
    (owned : cache.Agrees dir inode (bindings before))
    (fresh : ∀ {captured reached}, openAppend path before = .ok captured reached →
      bindings reached path = some (inode captured))
    (selected : selectAppendHandle cache.active openAppend path before = .ok file opened) :
    bindings opened path = some (inode file) := by
  cases active : cache.active with
  | none => exact fresh (by simpa [selectAppendHandle, active] using selected)
  | some entry =>
    obtain ⟨name, captured⟩ := entry
    by_cases same : path = name
    · subst name
      simp [selectAppendHandle, active, Pure.pure, EStateM.pure] at selected
      obtain ⟨rfl, rfl⟩ := selected
      exact owned.active active
    · exact fresh (by simpa [selectAppendHandle, active, same] using selected)

/-- Successful append and flush leave the exact selected description in the
active cache. In the existing-file route the path bindings stay fixed, so
the reached cache satisfies the ownership condition for the WAL barrier. -/
theorem runAppendWithCache_owned {handle state : Type} {cache : Cache handle} {dir path : FilePath}
    (bytes : ByteArray) (openAppend : FilePath → EStateM IO.Error state handle)
    (write : handle → ByteArray → EStateM IO.Error state Unit) (flush : handle → EStateM IO.Error state Unit)
    (bindings : state → FilePath → Option Nat) (inode : handle → Nat) {before opened written reached : state}
    {file : handle} (owned : cache.Agrees dir inode (bindings before))
    (fresh : ∀ {captured after}, openAppend path before = .ok captured after →
      bindings after path = some (inode captured))
    (selected : selectAppendHandle cache.active openAppend path before = .ok file opened)
    (wrote : write file bytes opened = .ok () written) (flushed : flush file written = .ok () reached)
    (bindingsPreserved : bindings reached = bindings before)
    (selectedPreserved : bindings reached path = bindings opened path) :
    let active := { cache with active := some (path, file) }
    runAppendWithCache path bytes openAppend write flush (cache, before) = .ok () (active, reached) ∧
      active.Agrees dir inode (bindings reached) := by
  have captured := selectedPreserved.trans (cache.selectAppend_owned openAppend bindings inode owned fresh selected)
  exact ⟨by simp only [runAppendWithCache_effect, selected, wrote, flushed],
    (bindingsPreserved.symm ▸ owned).activate captured⟩

/-- The first sync of the WAL barrier uses the description that wrote and
flushed the append. Staging a different pathname adds only its pending
handle. With no pending keeper match, the shared sync takes the active
entry without reopening the keeper. The callback runs on the state left
by staging and preserves its outcome, including errors after an effect. -/
theorem appendThenStage_syncKeeper {handle state : Type} (cache : Cache handle) (before : state)
    (dir keeper staged : FilePath) (frame marker : ByteArray)
    (openAppend openRead : FilePath → EStateM IO.Error state handle)
    (write : handle → ByteArray → EStateM IO.Error state Unit) (flush : handle → EStateM IO.Error state Unit)
    (stage : FilePath → ByteArray → EStateM IO.Error state handle) (fsync : handle → EStateM IO.Error state Unit)
    {file stagedFile : handle} {opened written appended prepared : state}
    (keeperNotDirectory : keeper ≠ dir) (stagedIsDifferent : staged ≠ keeper)
    (keeperMiss : cache.pending.find? (fun entry => entry.1 == keeper) = none)
    (selected : selectAppendHandle cache.active openAppend keeper before = .ok file opened)
    (wrote : write file frame opened = .ok () written) (flushed : flush file written = .ok () appended)
    (markerWritten : stage staged marker appended = .ok stagedFile prepared) :
    let captured := ({ cache with active := some (keeper, file) } : Cache handle).remember staged stagedFile
    ((runAppendWithCache keeper frame openAppend write flush >>= fun _ =>
        stageFreshWithCache staged marker stage >>= fun _ => sync dir openRead fsync keeper) (cache, before)) =
      withCache captured (fsync file prepared) := by
  simp [runAppendWithCache_effect, stageFreshWithCache, sync, Cache.resolve, Cache.remember, pushPending,
    Bind.bind, EStateM.bind, keeperNotDirectory, stagedIsDifferent, keeperMiss, selected, wrote, flushed,
    markerWritten]

end Alvoki.Storage.SyncHandleRouting
