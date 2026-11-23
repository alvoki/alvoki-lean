import Alvoki.Storage.Publication.DiskPublicationModel

namespace Alvoki.Storage.DirectoryPublication

inductive Entry where
  | manifest
  | walBoundary
  deriving DecidableEq

/-- The checkpoint and WAL marker read from one directory image. -/
structure Bindings where
  manifest : Option ByteArray
  walBoundary : Option ByteArray

def Bindings.get (bindings : Bindings) : Entry → Option ByteArray
  | .manifest => bindings.manifest
  | .walBoundary => bindings.walBoundary

def Bindings.replace (bindings : Bindings) : Entry → ByteArray → Bindings
  | .manifest, bytes => { bindings with manifest := some bytes }
  | .walBoundary, bytes => { bindings with walBoundary := some bytes }

/-- A crash chooses one pair of directory bindings. Each replacement attempt
overwrites its staging name first. WAL contents and run file durability are
modeled separately. -/
structure Image where
  active : Bindings
  crashImages : List Bindings
  staged : Entry → Option (ByteArray × Bool) := fun _ => none

def Image.settled (bindings : Bindings) : Image := ⟨bindings, [bindings], fun _ => none⟩

/-- All directory barriers use the same operation, including the run-directory
barrier and the sync at the end of either successful reopen path. -/
def Image.syncDirectory (image : Image) : Image :=
  { image with crashImages := [image.active] }

private def Image.setStaged (image : Image) (entry : Entry)
    (staged : Option (ByteArray × Bool)) : Image :=
  { image with staged := fun name => if name = entry then staged else image.staged name }

/-- Before a barrier, a rename may persist along with any earlier possible
outcome, or the earlier outcome alone may persist. This conservatively allows
either persistence order for different names. -/
private def Image.rename (image : Image) (entry : Entry) (bytes : ByteArray) : Image :=
  { image.setStaged entry none with
    active := image.active.replace entry bytes
    crashImages := image.crashImages.map (·.replace entry bytes) ++ image.crashImages }

def Image.step (image : Image) (entry : Entry) (bytes : ByteArray) : Publication.Step → Option Image
  | .writeStaged => some (image.setStaged entry (some (bytes, false)))
  | .syncStaged => (image.staged entry).map fun staged =>
      image.setStaged entry (some (staged.1, true))
  | .renameStaged =>
    match image.staged entry with
    | some (synced, true) => some (image.rename entry synced)
    | _ => none
  | .syncDirectory => some image.syncDirectory

/-- A failed sync may have settled both names. Retaining all prior crash
candidates conservatively covers an error with no durability guarantee,
including a partially effective sync. -/
inductive Image.SyncFailure (before : Image) : Image → Prop where
  | beforeEffect : SyncFailure before before
  | afterEffect : SyncFailure before before.syncDirectory

def Image.project (image : Image) (entry : Entry) : Publication.Image :=
  ⟨image.active.get entry, image.crashImages.map (·.get entry), image.staged entry⟩

theorem Image.project_survives_iff (image : Image) (entry : Entry) (bytes : Option ByteArray) :
    bytes ∈ (image.project entry).crashImages ↔
      ∃ bindings ∈ image.crashImages, bindings.get entry = bytes := List.mem_map

theorem Image.syncDirectory_project (image : Image) (entry : Entry) (bytes : ByteArray) :
    (image.project entry).step bytes .syncDirectory = some (image.syncDirectory.project entry) := rfl

theorem Image.survives_syncDirectory_iff (image : Image) (bindings : Bindings) :
    bindings ∈ image.syncDirectory.crashImages ↔ bindings = image.active := List.mem_singleton

structure Image.Valid (acceptable : Bindings → Prop) (image : Image) : Prop where
  activeMaySurvive : image.active ∈ image.crashImages
  crashValid : ∀ candidate ∈ image.crashImages, acceptable candidate

theorem Image.Valid.activeValid {acceptable : Bindings → Prop} {image : Image}
    (valid : image.Valid acceptable) : acceptable image.active :=
  valid.crashValid image.active valid.activeMaySurvive

theorem Image.settled_valid {acceptable : Bindings → Prop} {bindings : Bindings}
    (valid : acceptable bindings) : (settled bindings).Valid acceptable := by
  refine ⟨by simp [settled], ?_⟩
  intro candidate survives
  exact (List.mem_singleton.mp survives).symm ▸ valid

theorem Image.Valid.project {acceptable : Bindings → Prop} {image : Image}
    (valid : image.Valid acceptable) (entry : Entry) {entryValid : Option ByteArray → Prop}
    (projectValid : ∀ bindings, acceptable bindings → entryValid (bindings.get entry)) :
    (image.project entry).Valid entryValid := by
  refine ⟨?_, projectValid _ valid.activeValid, ?_⟩
  · intro noCrashes
    have survives : image.active.get entry ∈ (image.project entry).crashImages :=
      List.mem_map_of_mem valid.activeMaySurvive
    simp [noCrashes] at survives
  · intro bytes survives
    obtain ⟨bindings, canSurvive, rfl⟩ := (image.project_survives_iff entry bytes).mp survives
    exact projectValid _ (valid.crashValid _ canSurvive)

theorem Image.Valid.syncDirectory {acceptable : Bindings → Prop} {image : Image}
    (valid : image.Valid acceptable) : image.syncDirectory.Valid acceptable := by
  refine ⟨by simp [Image.syncDirectory], ?_⟩
  intro candidate survives
  exact ((image.survives_syncDirectory_iff candidate).mp survives).symm ▸ valid.activeValid

private theorem Image.Valid.rename {acceptable : Bindings → Prop} {image : Image}
    (valid : image.Valid acceptable) (entry : Entry) (bytes : ByteArray)
    (replacementValid : ∀ candidate ∈ image.crashImages, acceptable (candidate.replace entry bytes)) :
    (image.rename entry bytes).Valid acceptable := by
  refine ⟨List.mem_append_left _ (List.mem_map_of_mem valid.activeMaySurvive), ?_⟩
  intro candidate survives
  rcases List.mem_append.mp survives with updated | unchanged
  · obtain ⟨earlier, survivesEarlier, rfl⟩ := List.mem_map.mp updated
    exact replacementValid _ survivesEarlier
  · exact valid.crashValid _ unchanged

/-- The caller supplies the semantic check for introducing the synced staged
bytes at each surviving pair. All other steps preserve acceptance on their own. -/
def Image.RenamePreserves (image : Image) (acceptable : Bindings → Prop)
    (entry : Entry) (action : Publication.Step) : Prop :=
  action = .renameStaged → ∀ bytes, image.staged entry = some (bytes, true) →
    ∀ candidate ∈ image.crashImages, acceptable (candidate.replace entry bytes)

theorem Image.step_valid {acceptable : Bindings → Prop} {before after : Image}
    {entry : Entry} {action : Publication.Step} {bytes : ByteArray}
    (valid : before.Valid acceptable) (replacement : before.RenamePreserves acceptable entry action)
    (step : before.step entry bytes action = some after) : after.Valid acceptable := by
  cases action with
  | writeStaged =>
    cases step
    exact ⟨valid.activeMaySurvive, valid.crashValid⟩
  | syncStaged =>
    simp only [Image.step] at step
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp step
    exact ⟨valid.activeMaySurvive, valid.crashValid⟩
  | renameStaged =>
    simp only [Image.step] at step
    split at step
    · rename_i synced staged
      cases step
      exact valid.rename entry synced (replacement rfl synced staged)
    · contradiction
  | syncDirectory =>
    cases step
    exact valid.syncDirectory

/-- Retries may start from the still-visible image after an I/O error or from
one of the crash pairs. This relation admits individual steps for reasoning
about cuts in a schedule. The adapter's replacement schedule starts each
attempt by overwriting the selected staging name. -/
inductive Retry (acceptable : Bindings → Prop) (initial : Image) : Image → Prop where
  | start : Retry acceptable initial initial
  | step (path : Retry acceptable initial before)
      (replacement : before.RenamePreserves acceptable entry action)
      (step : before.step entry bytes action = some after) : Retry acceptable initial after
  | failedSync (path : Retry acceptable initial before) (failed : before.SyncFailure after) :
      Retry acceptable initial after
  | crash (path : Retry acceptable initial before) (survives : bindings ∈ before.crashImages) :
      Retry acceptable initial (.settled bindings)

theorem retry_preserves {acceptable : Bindings → Prop} {initial after : Image}
    (valid : initial.Valid acceptable) (retry : Retry acceptable initial after) :
    after.Valid acceptable := by
  induction retry with
  | start => exact valid
  | step _ replacement step earlier => exact Image.step_valid earlier replacement step
  | failedSync _ failed earlier =>
    cases failed
    · exact earlier
    · exact earlier.syncDirectory
  | crash _ survives earlier => exact Image.settled_valid (earlier.crashValid _ survives)

end Alvoki.Storage.DirectoryPublication
