import Alvoki.Storage.Disk.WalGroupSyncSchedule

namespace Alvoki.Storage.SyncHandleRouting

open System

/-- A newly captured handle takes precedence over earlier handles for the same path. -/
@[macro_inline] def pushPending {handle : Type} (path : FilePath) (descriptor : handle)
    (pending : List (FilePath × handle)) : List (FilePath × handle) :=
  (path, descriptor) :: pending

/-- Only an aligned keeper needs to retain its read handle for fsync. -/
@[macro_inline] def readKeeperWith [Monad m] [MonadExceptOf IO.Error m] {handle : Type}
    (openRead : FilePath → m handle) (readPrefix : handle → Nat → m ByteArray)
    (remember : FilePath → handle → m Unit) (path : FilePath) (count fileSize : Nat) : m ByteArray := do
  unless count ≤ fileSize ∧ count < USize.size do
    throw (IO.userError s!"WAL keeper does not cover its selected prefix: '{path}'")
  let file ← openRead path
  let bytes ← readPrefix file count
  if count == fileSize then remember path file
  return bytes

/-- Reuse the active append description only while writing its recorded path. -/
@[macro_inline] def selectAppendHandle [Monad m] {handle : Type}
    (active : Option (FilePath × handle)) (openAppend : FilePath → m handle) (path : FilePath) : m handle :=
  match active with
  | some (name, handle) => if path == name then pure handle else openAppend path
  | none => openAppend path

/-- Keep the active description after a successful write and flush. A
write or flush failure drops the possibly dirty stream while the lock is
still held. An open error occurs before writing or changing the cache. -/
@[macro_inline] def appendWithActive [Monad m] [MonadExceptOf IO.Error m] {handle : Type}
    (getActive : m (Option (FilePath × handle))) (setActive : Option (FilePath × handle) → m Unit)
    (openAppend : FilePath → m handle) (write : handle → ByteArray → m Unit) (flush : handle → m Unit)
    (path : FilePath) (bytes : ByteArray) : m Unit := do
  let active ← getActive
  let file ← selectAppendHandle active openAppend path
  try
    write file bytes
    flush file
  catch error =>
    setActive none
    throw error
  setActive (some (path, file))

/-- Use only the cache fields required by this lookup. A pending match
removes every entry for the path before the chosen handle is synced. -/
@[macro_inline] def syncWithHandles [Monad m] [MonadExceptOf IO.Error m] {handle : Type}
    (dir path : FilePath) (getDirectory : m (Option handle))
    (getPending : m (List (FilePath × handle))) (setPending : List (FilePath × handle) → m Unit)
    (getActive : m (Option (FilePath × handle))) (openRead : FilePath → m handle)
    (fsync : handle → m Unit) : m Unit := do
  let file ← if path == dir then do
    let some handle ← getDirectory | throw (IO.userError "database is closed")
    pure handle
  else do
    let pending ← getPending
    if let some (_, handle) := pending.find? (fun entry => entry.1 == path) then
      setPending (pending.filter (fun entry => entry.1 != path))
      pure handle
    else if let some (active, handle) ← getActive then
      if active == path then pure handle else openRead path
    else openRead path
  fsync file

/-- Each handle token identifies the captured open description. The
external state records filesystem effects separately from the cache. -/
structure Cache (handle : Type) where
  directory : Option handle
  active : Option (FilePath × handle)
  pending : List (FilePath × handle)

/-- Carry the reached cache through either result of a modeled file action. -/
def withCache (cache : Cache handle) :
    EStateM.Result IO.Error state α → EStateM.Result IO.Error (Cache handle × state) α
  | .ok result after => .ok result (cache, after)
  | .error cause after => .error cause (cache, after)

def Cache.consume (cache : Cache handle) (path : FilePath) : Cache handle :=
  { cache with pending := cache.pending.filter (fun entry => entry.1 != path) }

/-- Interpret the handle selection in the Linux adapter. Directory
selection comes first, including its closed-session error. A pending
match consumes all entries for that pathname before fsync. The active
cache is consulted only after a pending miss. -/
def Cache.resolve (cache : Cache handle) (dir path : FilePath)
    (openRead : FilePath → EStateM IO.Error state handle) (before : state) :
    EStateM.Result IO.Error (Cache handle × state) handle :=
  if path == dir then
    match cache.directory with
    | some descriptor => .ok descriptor (cache, before)
    | none => .error (IO.userError "database is closed") (cache, before)
  else
    match cache.pending.find? (fun entry => entry.1 == path) with
    | some (_, descriptor) => .ok descriptor (cache.consume path, before)
    | none =>
      match cache.active with
      | some (active, descriptor) =>
        if active == path then .ok descriptor (cache, before)
        else withCache cache (openRead path before)
      | none => withCache cache (openRead path before)

/-- The fsync gets exactly the resolved description and the state it
reached. A resolution error never runs fsync, and an fsync error retains
the consumed cache and any filesystem effects from the call. -/
def sync (dir : FilePath) (openRead : FilePath → EStateM IO.Error state handle)
    (fsync : handle → EStateM IO.Error state Unit) (path : FilePath) :
    EStateM IO.Error (Cache handle × state) Unit := fun (cache, before) =>
  match cache.resolve dir path openRead before with
  | .ok descriptor (cache, atEffect) => withCache cache (fsync descriptor atEffect)
  | .error cause after => .error cause after

private def readCache (get : Cache handle → α) : EStateM IO.Error (Cache handle × state) α :=
  fun before => .ok (get before.1) before

private def setPending (pending : List (FilePath × handle)) :
    EStateM IO.Error (Cache handle × state) Unit :=
  fun (cache, before) => .ok () ({cache with pending}, before)

private def onFiles (act : EStateM IO.Error state α) :
    EStateM IO.Error (Cache handle × state) α :=
  fun (cache, before) => withCache cache (act before)

/-- The selector used by the adapter has the exact modeled schedule
when ref reads and writes are interpreted as cache actions. The supplied
open and fsync callbacks still determine object identity and file effects. -/
theorem syncWithHandles_cache (dir path : FilePath) (cache : Cache handle) (before : state)
    (openRead : FilePath → EStateM IO.Error state handle)
    (fsync : handle → EStateM IO.Error state Unit) :
    syncWithHandles dir path (readCache Cache.directory) (readCache Cache.pending)
      setPending (readCache Cache.active) (fun path => onFiles (openRead path))
      (fun handle => onFiles (fsync handle)) (cache, before) =
        sync dir openRead fsync path (cache, before) := by
  by_cases directory : path = dir
  · cases found : cache.directory <;>
      simp [syncWithHandles, sync, Cache.resolve, directory, found,
        readCache, onFiles, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, throw, throwThe,
        MonadExceptOf.throw, EStateM.throw]
  · cases pending : cache.pending.find? (fun entry => entry.1 == path) with
    | some entry =>
      obtain ⟨_, captured⟩ := entry
      simp [syncWithHandles, sync, Cache.resolve, directory, pending, readCache, setPending,
        Cache.consume, onFiles, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
    | none =>
      cases active : cache.active with
      | none =>
        cases report : openRead path before <;>
          simp [syncWithHandles, sync, Cache.resolve, directory, pending, active,
            readCache, onFiles, withCache, Bind.bind, EStateM.bind, report]
      | some entry =>
        obtain ⟨name, captured⟩ := entry
        by_cases same : path = name
        · subst name
          simp [syncWithHandles, sync, Cache.resolve, directory, pending, active,
            readCache, onFiles, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
        · cases report : openRead path before <;>
            simp [syncWithHandles, sync, Cache.resolve, directory, pending, active, Ne.symm same,
              readCache, onFiles, withCache, Bind.bind, EStateM.bind, report]

/-- Under ownership, each selectable cached description names the inode
currently bound to its recorded path. A handle may be used for delayed
effects after rebinding, but those effects use the captured description
without running this path lookup again. -/
structure Cache.Agrees (cache : Cache handle) (dir : FilePath)
    (inode : handle → Nat) (binding : FilePath → Option Nat) : Prop where
  directory : ∀ {descriptor}, cache.directory = some descriptor →
    binding dir = some (inode descriptor)
  pending : ∀ {path descriptor}, cache.pending.find? (fun entry => entry.1 == path) =
    some (path, descriptor) → binding path = some (inode descriptor)
  active : ∀ {path descriptor}, cache.active = some (path, descriptor) →
    binding path = some (inode descriptor)

/-- A successful handle lookup puts a description for the requested inode
at the fsync boundary. Cached hits do not change external state before the
boundary. A fresh opening supplies the binding in its returned state. -/
theorem Cache.resolve_owned {cache : Cache handle} {dir path : FilePath}
    {inode : handle → Nat} {bindings : state → FilePath → Option Nat}
    {openRead : FilePath → EStateM IO.Error state handle} {before atEffect : state}
    {descriptor : handle} {after : Cache handle}
    (owned : cache.Agrees dir inode (bindings before))
    (fresh : ∀ {opened reached}, openRead path before = .ok opened reached →
      bindings reached path = some (inode opened))
    (resolved : cache.resolve dir path openRead before = .ok descriptor (after, atEffect)) :
    bindings atEffect path = some (inode descriptor) := by
  by_cases directory : path = dir
  · subst path
    cases found : cache.directory with
    | none => simp [resolve, found] at resolved
    | some captured =>
      simp [resolve, found] at resolved
      obtain ⟨rfl, _, rfl⟩ := resolved
      exact owned.directory found
  · have opened_eq (result : withCache cache (openRead path before) =
        .ok descriptor (after, atEffect)) : bindings atEffect path = some (inode descriptor) := by
      cases report : openRead path before with
      | error cause reached => simp [report, withCache] at result
      | ok opened reached =>
        simp [report, withCache] at result
        obtain ⟨rfl, _, rfl⟩ := result
        exact fresh report
    cases pending : cache.pending.find? (fun entry => entry.1 == path) with
    | some found =>
      obtain ⟨name, captured⟩ := found
      have named : name = path := by simpa using List.find?_some pending
      subst name
      simp [resolve, directory, pending] at resolved
      obtain ⟨rfl, _, rfl⟩ := resolved
      exact owned.pending pending
    | none =>
      cases active : cache.active with
      | none => exact opened_eq (by simpa [resolve, directory, pending, active] using resolved)
      | some found =>
        obtain ⟨name, captured⟩ := found
        by_cases named : name = path
        · subst name
          simp [resolve, directory, pending, active] at resolved
          obtain ⟨rfl, _, rfl⟩ := resolved
          exact owned.active active
        · exact opened_eq (by simpa [resolve, directory, pending, active, named] using resolved)

/-- A pending descriptor is consumed before its sync even if the callback
reports an error. Subsequent callbacks see no pending entry for this path.
The directory and active references are unchanged. -/
theorem pendingSync {cache : Cache handle} {dir path : FilePath} {descriptor : handle}
    (notDirectory : path ≠ dir)
    (pending : cache.pending.find? (fun entry => entry.1 == path) = some (path, descriptor))
    (openRead : FilePath → EStateM IO.Error state handle)
    (fsync : handle → EStateM IO.Error state Unit) (before : state) :
    let remaining := cache.pending.filter (fun entry => entry.1 != path)
    sync dir openRead fsync path (cache, before) =
      withCache { cache with pending := remaining } (fsync descriptor before) ∧
    remaining.find? (fun entry => entry.1 == path) = none := by
  dsimp only
  constructor
  · simp [sync, Cache.resolve, Cache.consume, notDirectory, pending]
  · rw [List.find?_eq_none]
    intro entry kept found
    have retained := (List.mem_filter.mp kept).2
    exact (by simpa using retained : entry.1 ≠ path) (by simpa using found)

/-- In the usual WAL barrier, the active keeper is synced before consuming
the staged marker's pending handle. The second sync sees the external state
left by the first even on failure, and the returned cache consumes the
marker in every outcome. -/
theorem groupedActivePending {cache : Cache handle} {dir keeper staged : FilePath}
    {keeperHandle stagedHandle : handle}
    (keeperNotDirectory : keeper ≠ dir) (stagedNotDirectory : staged ≠ dir)
    (keeperMiss : cache.pending.find? (fun entry => entry.1 == keeper) = none)
    (active : cache.active = some (keeper, keeperHandle))
    (pending : cache.pending.find? (fun entry => entry.1 == staged) = some (staged, stagedHandle))
    (openRead : FilePath → EStateM IO.Error state handle)
    (fsync : handle → EStateM IO.Error state Unit) (before : state) :
    let consumed := cache.consume staged
    SyncPathGroup.run (sync dir openRead fsync) #[keeper, staged] (cache, before) =
      match fsync keeperHandle before with
      | .ok () afterKeeper =>
        match fsync stagedHandle afterKeeper with
        | .ok () afterStaged => .ok () (consumed, afterStaged)
        | .error cause afterStaged => .error (IO.userError s!"sync failed for '{staged}': {cause}")
            (consumed, afterStaged)
      | .error cause afterKeeper =>
        match fsync stagedHandle afterKeeper with
        | .ok () afterStaged | .error _ afterStaged =>
          .error (IO.userError s!"sync failed for '{keeper}': {cause}") (consumed, afterStaged) := by
  have syncKeeper : sync dir openRead fsync keeper (cache, before) =
      withCache cache (fsync keeperHandle before) := by
    simp [sync, Cache.resolve, keeperNotDirectory, keeperMiss, active]
  rw [SyncPathGroup.run_pair, syncKeeper]
  cases fsync keeperHandle before with
  | ok result afterKeeper =>
    cases result
    simp only [withCache]
    rw [(pendingSync stagedNotDirectory pending openRead fsync afterKeeper).1]
    cases fsync stagedHandle afterKeeper <;> rfl
  | error cause afterKeeper =>
    simp only [withCache]
    rw [(pendingSync stagedNotDirectory pending openRead fsync afterKeeper).1]
    cases fsync stagedHandle afterKeeper <;> rfl

end Alvoki.Storage.SyncHandleRouting
