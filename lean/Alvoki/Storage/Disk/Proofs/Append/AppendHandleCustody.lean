import Alvoki.Storage.Disk.Proofs.Filesystem.StagedHandleCustody

namespace Alvoki.Storage.SyncHandleRouting

open System

/-- The raw append retains the heap reached by its actual cache store.
Clearing the active cell can release a stream with pending effects. -/
theorem appendWithActive_effect {handle state : Type}
    (getActive : EStateM IO.Error state (Option (FilePath × handle)))
    (setActive : Option (FilePath × handle) → EStateM IO.Error state Unit)
    (openAppend : FilePath → EStateM IO.Error state handle)
    (write : handle → ByteArray → EStateM IO.Error state Unit)
    (flush : handle → EStateM IO.Error state Unit)
    (path : FilePath) (bytes : ByteArray) (entry : state) :
    appendWithActive getActive setActive openAppend write flush path bytes entry =
      match getActive entry with
      | .error cause reached => .error cause reached
      | .ok active loaded =>
        match selectAppendHandle active openAppend path loaded with
        | .error cause reached => .error cause reached
        | .ok file opened =>
          match ((write file bytes) >>= fun _ => flush file) opened with
          | .error cause failed =>
            (setActive none >>= fun _ => EStateM.throw cause) failed
          | .ok () flushed => setActive (some (path, file)) flushed := by
  simp only [appendWithActive, Bind.bind]
  cases loaded : getActive entry with
  | error => simp [EStateM.bind, loaded]
  | ok active ready =>
    cases selected : selectAppendHandle active openAppend path ready with
    | error => simp [EStateM.bind, loaded, selected]
    | ok file opened =>
      cases attempted : (EStateM.bind (write file bytes) (fun _ => flush file)) opened with
      | error cause failed =>
        simp [EStateM.bind, loaded, selected, MonadExcept.tryCatch, MonadExceptOf.tryCatch, tryCatchThe,
          EStateM.tryCatch, EStateM.Backtrackable.restore, EStateM.dummyRestore] at attempted ⊢
        rw [attempted]
        cases cleared : setActive none failed <;>
          simp [cleared, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
      | ok value reached =>
        cases value
        simp [EStateM.bind, loaded, selected, MonadExcept.tryCatch, MonadExceptOf.tryCatch, tryCatchThe,
          EStateM.tryCatch] at attempted ⊢
        rw [attempted]

/-- Interpret both the cache update and the observed effects of
releasing the references at that update. The returned diagnostic is
determined by the data action, even if release changes the file state. -/
def runAppendWithCacheEffects {handle state : Type} (path : FilePath) (bytes : ByteArray)
    (openAppend : FilePath → EStateM IO.Error state handle)
    (write : handle → ByteArray → EStateM IO.Error state Unit) (flush : handle → EStateM IO.Error state Unit)
    (afterStore : Cache handle → Option (FilePath × handle) → state → state) :
    EStateM IO.Error (Cache handle × state) Unit :=
  appendWithActive (fun before => .ok before.1.active before)
    (fun active (cache, files) => .ok () ({ cache with active }, afterStore cache active files))
    (fun name (cache, files) => withCache cache (openAppend name files))
    (fun file value (cache, files) => withCache cache (write file value files))
    (fun file (cache, files) => withCache cache (flush file files))
    path bytes

/-- A file model whose cache updates have no extra file effects. -/
def runAppendWithCache {handle state : Type} (path : FilePath) (bytes : ByteArray)
    (openAppend : FilePath → EStateM IO.Error state handle)
    (write : handle → ByteArray → EStateM IO.Error state Unit) (flush : handle → EStateM IO.Error state Unit) :
    EStateM IO.Error (Cache handle × state) Unit :=
  runAppendWithCacheEffects path bytes openAppend write flush (fun _ _ files => files)

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

/-- An open failure reaches no write or cache update. A data failure
clears the active entry and retains the file effects of that clear. -/
theorem runAppendWithCacheEffects_effect {handle state : Type} (cache : Cache handle) (before : state)
    (path : FilePath) (bytes : ByteArray) (openAppend : FilePath → EStateM IO.Error state handle)
    (write : handle → ByteArray → EStateM IO.Error state Unit) (flush : handle → EStateM IO.Error state Unit)
    (afterStore : Cache handle → Option (FilePath × handle) → state → state) :
    runAppendWithCacheEffects path bytes openAppend write flush afterStore (cache, before) =
      match selectAppendHandle cache.active openAppend path before with
      | .error cause reached => .error cause (cache, reached)
      | .ok file opened => match write file bytes opened with
        | .error cause reached => .error cause ({ cache with active := none }, afterStore cache none reached)
        | .ok () written => match flush file written with
          | .error cause reached => .error cause ({ cache with active := none }, afterStore cache none reached)
          | .ok () reached =>
            let active := some (path, file)
            .ok () ({ cache with active }, afterStore cache active reached) := by
  refine (appendWithActive_effect (state := Cache handle × state)
    (fun before => .ok before.1.active before)
    (fun active (cache, files) => .ok () ({ cache with active }, afterStore cache active files))
    (fun name (cache, files) => withCache cache (openAppend name files))
    (fun file value (cache, files) => withCache cache (write file value files))
    (fun file (cache, files) => withCache cache (flush file files)) path bytes (cache, before)).trans ?_
  dsimp only
  rw [selectAppendHandle_withCache]
  cases selected : selectAppendHandle cache.active openAppend path before with
  | error => rfl
  | ok file opened =>
    cases writing : write file bytes opened with
    | error => simp [withCache, writing, Bind.bind, EStateM.bind, EStateM.throw]
    | ok result written =>
      cases result
      cases flushing : flush file written <;>
        simp [withCache, writing, flushing, Bind.bind, EStateM.bind, EStateM.throw]

/-- The effect for the file model in which active references can be
replaced without extra file effects. -/
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
          | .ok () reached => .ok () ({ cache with active := some (path, file) }, reached) :=
  runAppendWithCacheEffects_effect cache before path bytes openAppend write flush (fun _ _ files => files)

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
