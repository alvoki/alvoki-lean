import DiskPublication
import Recovery

namespace Alvoki.Storage.Publication

/-- One active name and a protocol-owned temporary name in a fixed directory.
The active contents survive a crash according to the separate directory outcomes.
An outstanding staged file can be overwritten on the next attempt. -/
structure Image where
  active : Option ByteArray
  crashImages : List (Option ByteArray)
  staged : Option (ByteArray × Bool) := none

def Image.settled (active : Option ByteArray) : Image := ⟨active, [active], none⟩

/-- A synced temporary inode can become visible via rename before its name is
durable. Both the old name binding and the replacement may survive until a
directory sync selects the current binding. -/
def Image.step (image : Image) (bytes : ByteArray) (action : Step) : Option Image :=
  match action with
  | .writeStaged => some { image with staged := some (bytes, false) }
  | .syncStaged => image.staged.map fun staged => { image with staged := some (staged.1, true) }
  | .renameStaged =>
    match image.staged with
    | some (synced, true) => some ⟨some synced, some synced :: image.crashImages, none⟩
    | _ => none
  | .syncDirectory => some { image with crashImages := [image.active] }

def Image.execute (image : Image) (bytes : ByteArray) (actions : List Step) : Option Image :=
  actions.foldlM (fun current action => current.step bytes action) image

structure Image.Valid (acceptable : Option ByteArray → Prop) (image : Image) : Prop where
  hasCrashImage : image.crashImages ≠ []
  activeValid : acceptable image.active
  crashValid : ∀ candidate ∈ image.crashImages, acceptable candidate

theorem Image.settled_valid {acceptable : Option ByteArray → Prop} {active : Option ByteArray}
    (valid : acceptable active) : (settled active).Valid acceptable := by
  refine { hasCrashImage := by simp [settled], activeValid := valid, crashValid := ?_ }
  intro candidate survives
  exact (List.mem_singleton.mp survives).symm ▸ valid

/-- Full success publishes the exact new bytes and settles the directory entry. -/
theorem successful_replace (initial : Image) (bytes : ByteArray) :
    initial.execute bytes steps = some (.settled (some bytes)) := by
  rfl

def Image.perform (bytes : ByteArray) (action : Step) : StateT Image Option Unit :=
  fun current => (current.step bytes action).map ((), ·)

theorem run_model_success (initial : Image) (bytes : ByteArray) :
    (run (Image.perform bytes)).run initial = some ((), .settled (some bytes)) := by
  rfl

private theorem cut_preserves {acceptable : Option ByteArray → Prop} {initial : Image}
    {bytes : ByteArray} (old : initial.Valid acceptable) (new : acceptable (some bytes))
    (cut : Nat) {after : Image} (ran : initial.execute bytes (steps.take cut) = some after) :
    after.Valid acceptable := by
  rcases cut with _ | _ | _ | _ | cut
  · cases ran; exact old
  · cases ran
    exact {
      hasCrashImage := old.hasCrashImage
      activeValid := old.activeValid
      crashValid := old.crashValid
    }
  · cases ran
    exact {
      hasCrashImage := old.hasCrashImage
      activeValid := old.activeValid
      crashValid := old.crashValid
    }
  · cases ran
    refine { hasCrashImage := by simp, activeValid := new, crashValid := ?_ }
    intro candidate atCut
    rcases List.mem_cons.mp atCut with rfl | earlier
    · exact new
    · exact old.crashValid candidate earlier
  · simp [steps, Image.execute, Image.step] at ran
    cases ran
    exact Image.settled_valid new

/-- A recovery may start again from a crash image even if a crash interrupted
an earlier recovery. A process failure may leave the current image visible. -/
inductive Retry (mayReplace : Image → ByteArray → Prop) : Image → Image → Prop where
  | refl (image) : Retry mayReplace image image
  | attempt (path : Retry mayReplace initial before) (chosen : mayReplace before bytes)
      (cut : Nat) (ran : before.execute bytes (steps.take cut) = some after) :
      Retry mayReplace initial after
  | crash (path : Retry mayReplace initial before) (survives : candidate ∈ before.crashImages) :
      Retry mayReplace initial (.settled candidate)

theorem retry_preserves {mayReplace : Image → ByteArray → Prop}
    {acceptable : Option ByteArray → Prop} {initial after : Image}
    (validReplacement : ∀ image bytes, image.Valid acceptable → mayReplace image bytes → acceptable (some bytes))
    (old : initial.Valid acceptable) (path : Retry mayReplace initial after) : after.Valid acceptable := by
  induction path with
  | refl => exact old
  | attempt _ chosen cut ran earlier => exact cut_preserves earlier (validReplacement _ _ earlier chosen) cut ran
  | crash _ survives earlier => exact Image.settled_valid (earlier.crashValid _ survives)

def choosesRepair (image : Image) (replacement : ByteArray) : Prop :=
  ∃ bytes, image.active = some bytes ∧ WAL.repairPrefix bytes = some replacement

theorem repaired_bytes_have_same_replay {base : PackedTable} {bytes trimmed : ByteArray}
    (selected : WAL.repairPrefix bytes = some trimmed) :
    recoverCheckpoint base trimmed = recoverCheckpoint base bytes := by
  simpa [selected] using recoverCheckpoint_repair base bytes

/-- At any retry boundary, all surviving WAL images yield the same replay result
when the initial images do and each replacement uses the executable tail trim. -/
theorem repair_retry_preserves_replay {initial after : Image} {base : PackedTable}
    {expected : Except String PackedTable}
    (old : initial.Valid (fun image => ∃ bytes, image = some bytes ∧
      recoverCheckpoint base bytes = expected))
    (path : Retry choosesRepair initial after) :
    after.Valid (fun image => ∃ bytes, image = some bytes ∧ recoverCheckpoint base bytes = expected) := by
  apply retry_preserves _ old path
  intro before replacement valid chosen
  obtain ⟨current, active, selected⟩ := chosen
  obtain ⟨matched, same, recovered⟩ := valid.activeValid
  rw [active] at same
  cases same
  exact ⟨replacement, rfl, (repaired_bytes_have_same_replay selected).trans recovered⟩

end Alvoki.Storage.Publication
