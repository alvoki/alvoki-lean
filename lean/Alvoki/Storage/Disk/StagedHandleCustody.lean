import Alvoki.Storage.Disk.StagingFile
import Alvoki.Storage.Disk.SyncHandleCustody

namespace Alvoki.Storage.SyncHandleRouting

open System

/-- Model the file effects of dropping the unretained handle on a data
error. The pinned runtime calls `fclose` and ignores its status. -/
def dataErrorDropState {handle state : Type} (drop : handle → EStateM IO.Error state Unit)
    (descriptor : handle) (before : state) : state :=
  match drop descriptor before with
  | .ok _ after | .error _ after => after

def withDataErrorDrop {handle state : Type} (drop : handle → EStateM IO.Error state Unit)
    (descriptor : handle) (action : EStateM IO.Error state Unit) : EStateM IO.Error state Unit :=
  fun before =>
    match action before with
    | .ok () after => .ok () after
    | .error cause after => .error cause (dataErrorDropState drop descriptor after)

/-- The reported finalizer effect follows the original data callback's
error. It supplies the reached file state while the cause stays original. -/
theorem withDataErrorDrop_error {handle state : Type} (drop : handle → EStateM IO.Error state Unit)
    (descriptor : handle) (action : EStateM IO.Error state Unit) {before after : state} {cause : IO.Error}
    (failed : action before = .error cause after) :
    withDataErrorDrop drop descriptor action before = .error cause (dataErrorDropState drop descriptor after) := by
  simp only [withDataErrorDrop, failed]

/-- Interpret `SyncFiles.stage` as the fresh staged write followed by
pending-handle insertion on successful return. A failed open, write or
flush can already have filesystem effects, which the result retains. -/
noncomputable def stageFreshWithCache {handle state : Type} (path : FilePath) (bytes : ByteArray)
    (stage : FilePath → ByteArray → EStateM IO.Error state handle) :
    EStateM IO.Error (Cache handle × state) Unit := fun (cache, before) =>
  match stage path bytes before with
  | .ok descriptor after => .ok () (cache.remember path descriptor, after)
  | .error cause after => .error cause (cache, after)

/-- Any failed staging step preserves its reached external state and
leaves the pending-handle cache alone. -/
theorem stageFreshWithCache_error {handle state : Type} (cache : Cache handle) (path : FilePath) (bytes : ByteArray)
    (stage : FilePath → ByteArray → EStateM IO.Error state handle) {before after : state} {cause : IO.Error}
    (reported : stage path bytes before = .error cause after) :
    stageFreshWithCache path bytes stage (cache, before) = .error cause (cache, after) := by
  simp only [stageFreshWithCache, reported]

/-- The reached path binding of the staged description and the unchanged
neighboring bindings preserve cache ownership. -/
theorem stageFreshWithCache_owned {handle state : Type} {cache : Cache handle} {dir path : FilePath}
    (bytes : ByteArray) (stage : FilePath → ByteArray → EStateM IO.Error state handle)
    (bindings : state → FilePath → Option Nat) (inode : handle → Nat) {before after : state} {descriptor : handle}
    (owned : cache.Agrees dir inode (bindings before)) (separate : path ≠ dir)
    (notKeeper : ∀ {active}, cache.active ≠ some (path, active))
    (reported : stage path bytes before = .ok descriptor after)
    (captured : bindings after path = some (inode descriptor))
    (other : ∀ {name}, name ≠ path → bindings after name = bindings before name) :
    stageFreshWithCache path bytes stage (cache, before) =
      .ok () (cache.remember path descriptor, after) ∧
    (cache.remember path descriptor).Agrees dir inode (bindings after) := by
  exact ⟨by simp only [stageFreshWithCache, reported], owned.remember separate notKeeper captured other⟩

/-- Syncing the staged path passes the exact returned description to
the callback. With `writeFreshStagedWith`, that is the description used
for write and flush. Either sync outcome retains its reached state. -/
theorem stageFreshWithCache_sync {handle state : Type} {cache : Cache handle} {dir path : FilePath}
    (bytes : ByteArray) (stage : FilePath → ByteArray → EStateM IO.Error state handle)
    (openRead : FilePath → EStateM IO.Error state handle) (fsync : handle → EStateM IO.Error state Unit)
    {before after : state} {descriptor : handle} (separate : path ≠ dir)
    (reported : stage path bytes before = .ok descriptor after) :
    (stageFreshWithCache path bytes stage >>= fun _ => sync dir openRead fsync path)
      (cache, before) = withCache (cache.consume path) (fsync descriptor after) := by
  simp only [stageFreshWithCache, Bind.bind, EStateM.bind, reported]
  rw [syncRemembered separate descriptor openRead fsync after]
  cases fsync descriptor after <;> rfl

end Alvoki.Storage.SyncHandleRouting
