import Alvoki.Storage.Disk.SyncHandleCustody
import Alvoki.Storage.Disk.WalSegmentRepairIO

namespace Alvoki.Storage.SyncHandleRouting

open System

def Cache.captureKeeper (cache : Cache handle) (path : FilePath) (descriptor : handle) (count fileSize : Nat) :
    Cache handle :=
  if count = fileSize then cache.remember path descriptor else cache

private def rememberCache (path : FilePath) (descriptor : handle) :
    EStateM IO.Error (Cache handle × state) Unit :=
  fun (cache, files) => .ok () (cache.remember path descriptor, files)

/-- The native reader records the exact descriptor that supplied the prefix
only when the selected bytes fill the physical keeper. -/
theorem readKeeperWith_success (cache : Cache handle) (path : FilePath) (count fileSize : Nat)
    (openRead : FilePath → EStateM IO.Error (Cache handle × state) handle)
    (readPrefix : handle → Nat → EStateM IO.Error (Cache handle × state) ByteArray)
    {before openedState reached : state} {descriptor : handle} {bytes : ByteArray}
    (fits : count ≤ fileSize ∧ count < USize.size)
    (opened : openRead path (cache, before) = .ok descriptor (cache, openedState))
    (read : readPrefix descriptor count (cache, openedState) = .ok bytes (cache, reached)) :
    readKeeperWith openRead readPrefix rememberCache path count fileSize (cache, before) =
      .ok bytes (cache.captureKeeper path descriptor count fileSize, reached) := by
  by_cases aligned : count = fileSize
  · subst fileSize
    simp [readKeeperWith, Cache.captureKeeper, rememberCache, fits.2, opened, read,
      Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
  · simp [readKeeperWith, Cache.captureKeeper, fits, opened, read, aligned,
      Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]

/-- A read error returns the reached file state without capturing a handle. -/
theorem readKeeperWith_readError (cache : Cache handle) (path : FilePath) (count fileSize : Nat)
    (openRead : FilePath → EStateM IO.Error (Cache handle × state) handle)
    (readPrefix : handle → Nat → EStateM IO.Error (Cache handle × state) ByteArray)
    {before openedState reached : state} {descriptor : handle} {cause : IO.Error}
    (fits : count ≤ fileSize ∧ count < USize.size)
    (opened : openRead path (cache, before) = .ok descriptor (cache, openedState))
    (failed : readPrefix descriptor count (cache, openedState) = .error cause (cache, reached)) :
    readKeeperWith openRead readPrefix rememberCache path count fileSize (cache, before) =
      .error cause (cache, reached) := by
  simp [readKeeperWith, fits, opened, failed, Bind.bind, EStateM.bind]

/-- With no active append handle, the captured keeper agrees with its held
binding. The long-file branch leaves the cache as it was. -/
theorem Cache.Agrees.captureKeeper {cache : Cache handle} {dir path : FilePath}
    {descriptor : handle} {count fileSize : Nat} {inode : handle → Nat}
    {binding : FilePath → Option Nat} (owned : cache.Agrees dir inode binding)
    (separate : path ≠ dir) (inactive : cache.active = none)
    (captured : binding path = some (inode descriptor)) :
    (cache.captureKeeper path descriptor count fileSize).Agrees dir inode binding := by
  by_cases aligned : count = fileSize
  · rw [Cache.captureKeeper, ite_eq_left aligned]
    exact owned.remember separate (by simp [inactive]) captured (fun _ => rfl)
  · simpa [Cache.captureKeeper, aligned] using owned

theorem file_ne_directory (dir : DiskDirectory) (file : DiskFile) : dir.file file ≠ dir.path := by
  intro same
  have length := congrArg (fun path : FilePath => path.toString.length) same
  simp [DiskDirectory.file, String.length_append] at length
  have slash : "/".length = 1 := by decide
  rw [slash] at length
  omega

private theorem runSingletonOk {σ : Type} (perform : FilePath → EStateM IO.Error σ Unit)
    (path : FilePath) {before after : σ} (outcome : perform path before = .ok () after) :
    SyncPathGroup.run perform #[path] before = .ok () after := by
  rw [SyncPathGroup.run_single, outcome]

open WalSegmentRepair

/-- The aligned repair step syncs the description that supplied the prefix.
After the call, the cache again contains only the directory handle. -/
theorem alignedKeeperStep (dir : DiskDirectory) (plan : Plan) (directory keeper : handle)
    (openRead : FilePath → EStateM IO.Error state handle)
    (fsync : handle → EStateM IO.Error state Unit)
    (remove : FilePath → EStateM IO.Error (Cache handle × state) (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error (Cache handle × state) Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error (Cache handle × state) Unit)
    {before after : state} (effect : fsync keeper before = .ok () after) :
    let initial : Cache handle := ⟨some directory, none, []⟩
    let path := dir.file (.walSegment plan.keeper)
    performPaths dir plan remove throw write (SyncPathGroup.run (sync dir.path openRead fsync)) renameFile
      .syncKeeper (initial.captureKeeper path keeper plan.keeperSize plan.keeperSize, before) =
      .ok () (initial, after) := by
  dsimp only
  rw [Cache.captureKeeper, ite_eq_left rfl]
  apply runSingletonOk
  rw [syncRemembered (file_ne_directory _ _) keeper openRead fsync before, effect]
  rfl

/-- On a long keeper the prefix handle was never captured. Once the
replacement's staged file sync succeeds, the actual rename callback receives
a directory-only cache, with no stale handle for either pathname. -/
theorem replacementKeeperBeforeRename (dir : DiskDirectory) (plan : Plan) (directory keeper staged : handle)
    {fileSize : Nat} (long : plan.keeperSize < fileSize)
    (openRead : FilePath → EStateM IO.Error state handle)
    (fsync : handle → EStateM IO.Error state Unit)
    (remove : FilePath → EStateM IO.Error (Cache handle × state) (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error (Cache handle × state) Unit)
    (renameFile : FilePath → FilePath → EStateM IO.Error (Cache handle × state) Unit)
    {before after : state} (effect : fsync staged before = .ok () after) :
    let initial : Cache handle := ⟨some directory, none, []⟩
    let path := dir.file (.walSegment plan.keeper)
    let stagedPath := dir.file .stagedWal
    let run := performPaths dir plan remove throw write (SyncPathGroup.run (sync dir.path openRead fsync)) renameFile
    (run (.replace .syncStaged) >>= fun _ => run (.replace .renameStaged))
      ((initial.captureKeeper path keeper plan.keeperSize fileSize).remember stagedPath staged, before) =
      renameFile stagedPath path (initial, after) := by
  dsimp only
  rw [Cache.captureKeeper, ite_eq_right (Nat.ne_of_lt long)]
  have synced :=
    runSingletonOk (sync dir.path openRead fsync) (dir.file .stagedWal)
      (before := (((⟨some directory, none, []⟩ : Cache handle).remember (dir.file .stagedWal) staged), before))
      (after := ((⟨some directory, none, []⟩ : Cache handle), after)) (by
        rw [syncRemembered (file_ne_directory _ _) staged openRead fsync before, effect]
        rfl)
  simp only [performPaths, Publication.performReplacement, Array.push_empty, Bind.bind, EStateM.bind, synced]

end Alvoki.Storage.SyncHandleRouting
