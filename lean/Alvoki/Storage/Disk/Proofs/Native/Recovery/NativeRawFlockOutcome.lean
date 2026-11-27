import Alvoki.Storage.Disk.Proofs.Native.Open.NativeRawOpenPrefixReturn

namespace Alvoki.Storage.DiskSession

open System

variable {heap : Type}

/-- Classify all ordinary flock returns on the handle produced by the
actual admission prefix. Only true enters the held cache/recovery
schedule with its unlock-on-error handler. -/
theorem RawOpenAdmissionCallbacks.runsAfterFlock
    (calls : RawOpenAdmissionCallbacks heap) (input : FilePath)
    {entry atFlock : heap} {directory : DiskDirectory} {handle : IO.FS.Handle}
    (opened : calls.beforeFlock input entry = .ok (directory, handle) atFlock)
    (init : OpenSyncCacheCallbacks heap)
    (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
    (recovery : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap α) :
    calls.runOpen input init makeCache recovery entry =
      match calls.flock handle atFlock with
      | .error cause reached => .error cause reached
      | .ok false reached => .error (IO.userError s!"database already open: {directory.path}") reached
      | .ok true reached =>
        (tryCatchThe IO.Error (do
          let cache ← openSyncFilesWith (init.openDirectory directory.path) init.newRef init.newRef init.newRef makeCache
          recovery directory handle cache) fun cause => do
            calls.unlock handle
            throw cause) reached := by
  rw [calls.runsAfterPrefix input init makeCache recovery entry, opened]
  cases result : calls.flock handle atFlock with
  | error cause reached => simp only [openWithLock, Bind.bind, EStateM.bind, result]
  | ok granted reached =>
    cases granted <;> simp only [openWithLock, Bind.bind, EStateM.bind, result, Bool.false_eq_true, ↓reduceIte,
      throw, throwThe, MonadExceptOf.throw, EStateM.throw, MonadExcept.tryCatch, tryCatchThe]

/-- A flock error reports the exact reached heap. Its local ownership
effect is a separate observation, with an acquisition only from a
vacant lock. This report ends before any later handle finalization. -/
structure RawOpenFlockError {image : Type} (calls : RawOpenAdmissionCallbacks heap)
    (view : OpenCloseHeapView heap image) (input : FilePath) (entry : heap) where
  directory : DiskDirectory
  handle : IO.FS.Handle
  atFlock : heap
  reached : heap
  opened : calls.beforeFlock input entry = .ok (directory, handle) atFlock
  cause : IO.Error
  flock : calls.flock handle atFlock = .error cause reached
  sameSlot : (view.handle reached handle).2.1 = (view.handle atFlock handle).2.1
  live : (view.handle atFlock handle).2.1 ∈ (view.descriptors atFlock).slots
  census : view.descriptors reached = view.descriptors atFlock
  files : (view.files reached).image = (view.files atFlock).image
  tookEffect : Bool
  vacant : tookEffect = true → (view.files atFlock).owners (directory.file .lock) = none
  owners : (view.files reached).owners =
    if tookEffect then
      (view.files atFlock).owners.set (directory.file .lock) (some (view.handle atFlock handle).2.1.description)
    else (view.files atFlock).owners

/-- An observed flock error returns before the held block, regardless
of the reported local ownership effect. If acquired, the error leaves
that same description held until a later observed release. -/
theorem RawOpenFlockError.returns
    {image : Type} {view : OpenCloseHeapView heap image} {calls : RawOpenAdmissionCallbacks heap}
    {input : FilePath} {entry : heap} (seen : RawOpenFlockError calls view input entry)
    (init : OpenSyncCacheCallbacks heap)
    (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
    (recovery : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap α) :
    let slot := (view.handle seen.atFlock seen.handle).2.1
    let before := view.files seen.atFlock
    let after := view.files seen.reached
    calls.runOpen input init makeCache recovery entry = .error seen.cause seen.reached ∧
    view.descriptors seen.reached = view.descriptors seen.atFlock ∧
    (view.handle seen.reached seen.handle).2.1 = slot ∧ slot ∈ (view.descriptors seen.reached).slots ∧
    after.image = before.image ∧
    (seen.tookEffect = false → after = before) ∧
    (seen.tookEffect = true → before.owners (seen.directory.file .lock) = none ∧
      after.owners.Owns seen.directory slot.description) ∧
    (TryLockObserves after.owners seen.directory (.ok true) ↔
      seen.tookEffect = false ∧ before.owners (seen.directory.file .lock) = none) := by
  intro slot before after
  refine ⟨?_, seen.census, seen.sameSlot, seen.census.symm ▸ seen.live, seen.files, ?_, ?_, ?_⟩
  · rw [calls.runsAfterFlock input seen.opened init makeCache recovery, seen.flock]
  · intro unchanged
    have owners : after.owners = before.owners := by
      simpa only [slot, before, after, unchanged, Bool.false_eq_true, ↓reduceIte] using seen.owners
    exact (LockedFileState.mk.injEq _ _ _ _).mpr ⟨seen.files, owners⟩
  · intro acquired
    refine ⟨seen.vacant acquired, ?_⟩
    change after.owners (seen.directory.file .lock) = some slot.description
    simp [after, seen.owners, acquired, LockOwners.set, slot]
  · cases effect : seen.tookEffect <;> simp [after, before, seen.owners, effect, TryLockObserves, LockOwners.set]

end Alvoki.Storage.DiskSession
