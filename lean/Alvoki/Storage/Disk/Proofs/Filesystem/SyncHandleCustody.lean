import Alvoki.Storage.Disk.SyncHandleRouting

namespace Alvoki.Storage.SyncHandleRouting

open System

def Cache.remember (cache : Cache handle) (path : FilePath) (descriptor : handle) : Cache handle :=
  { cache with pending := pushPending path descriptor cache.pending }

/-- Capturing the directory handle starts a cache with no file handles. -/
theorem Cache.Agrees.initial {descriptor : handle} {dir : FilePath}
    {inode : handle → Nat} {binding : FilePath → Option Nat} (captured : binding dir = some (inode descriptor)) :
    (⟨some descriptor, none, []⟩ : Cache handle).Agrees dir inode binding := by
  constructor
  · intro found exact
    cases exact
    exact captured
  · intro _ _ exact
    simp at exact
  · intro _ _ exact
    cases exact

/-- A reported stage or successor creation may replace its own binding.
Its newly opened handle shadows prior pending handles for that path.
The directory, active keeper and other recorded paths keep their bindings. -/
theorem Cache.Agrees.remember {cache : Cache handle} {dir path : FilePath} {descriptor : handle}
    {inode : handle → Nat} {before after : FilePath → Option Nat}
    (owned : cache.Agrees dir inode before)
    (separate : path ≠ dir)
    (notKeeper : ∀ {active}, cache.active ≠ some (path, active))
    (captured : after path = some (inode descriptor))
    (other : ∀ {name}, name ≠ path → after name = before name) :
    (cache.remember path descriptor).Agrees dir inode after := by
  constructor
  · intro found selected
    exact (other (Ne.symm separate)).trans (owned.directory selected)
  · intro name found selected
    by_cases same : name = path
    · subst name
      have exactHandle : descriptor = found := by
        simpa [Cache.remember, pushPending] using selected
      exact exactHandle ▸ captured
    · have previous : cache.pending.find? (fun entry => entry.1 == name) = some (name, found) := by
        simpa [Cache.remember, pushPending, Ne.symm same] using selected
      exact (other same).trans (owned.pending previous)
  · intro name found selected
    have activeOther : name ≠ path := by
      intro same
      subst name
      exact notKeeper selected
    exact (other activeOther).trans (owned.active selected)

/-- Appending preserves the binding. A successful open or retained append
supplies the identity of the handle now stored as the active keeper. -/
theorem Cache.Agrees.activate {cache : Cache handle} {dir path : FilePath} {descriptor : handle}
    {inode : handle → Nat} {binding : FilePath → Option Nat}
    (owned : cache.Agrees dir inode binding) (captured : binding path = some (inode descriptor)) :
    ({ cache with active := some (path, descriptor) } : Cache handle).Agrees dir inode binding := by
  refine ⟨owned.directory, owned.pending, ?_⟩
  intro name found selected
  cases selected
  exact captured

/-- Removing all pending entries for a path leaves the first match for
each other path intact, including when the selected fsync reports an error. -/
theorem Cache.Agrees.consume {cache : Cache handle} {dir path : FilePath}
    {inode : handle → Nat} {binding : FilePath → Option Nat}
    (owned : cache.Agrees dir inode binding) : (cache.consume path).Agrees dir inode binding := by
  refine ⟨owned.directory, ?_, owned.active⟩
  intro name found selected
  have foundKept := List.mem_of_find?_eq_some selected
  have nameOther : name ≠ path := by
    simpa [Cache.consume] using (List.mem_filter.mp foundKept).2
  have sameMatch : (fun entry : FilePath × handle => (entry.1 != path) && (entry.1 == name)) =
      (fun entry => entry.1 == name) := by
    funext entry
    by_cases same : entry.1 = name
    · simp [same, nameOther]
    · simp [same]
  rw [Cache.consume, List.find?_filter] at selected
  exact owned.pending (sameMatch ▸ selected)

/-- The newly captured object is the one handed to the subsequent
pending-file barrier. Its effect leaves no pending handle for that name. -/
theorem Cache.resolveRemembered {cache : Cache handle} {dir path : FilePath} (separate : path ≠ dir)
    (descriptor : handle) (openRead : FilePath → EStateM IO.Error state handle) (before : state) :
    (cache.remember path descriptor).resolve dir path openRead before =
      .ok descriptor (cache.consume path, before) := by
  have different : (path == dir) = false := beq_eq_false_iff_ne.mpr separate
  simp [Cache.resolve, Cache.remember, Cache.consume, pushPending, different]

theorem syncRemembered {cache : Cache handle} {dir path : FilePath} (separate : path ≠ dir)
    (descriptor : handle) (openRead : FilePath → EStateM IO.Error state handle)
    (fsync : handle → EStateM IO.Error state Unit) (before : state) :
    sync dir openRead fsync path (cache.remember path descriptor, before) =
      match fsync descriptor before with
      | .ok result after => .ok result (cache.consume path, after)
      | .error cause after => .error cause (cache.consume path, after) := by
  simp only [sync, Cache.resolveRemembered separate descriptor openRead before]
  cases fsync descriptor before <;> rfl

end Alvoki.Storage.SyncHandleRouting
