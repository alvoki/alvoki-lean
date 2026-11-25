import Alvoki.Storage.Disk.WalSegmentRetryReads

namespace Alvoki.Storage.DiskSession

open CheckpointPublication

/-- Compare the run maps only at the indices named by the selected manifest. -/
def SelectedRunsAgree (binding : Option ByteArray) (left right : RunFiles) : Prop :=
  ∀ bytes metadata, binding = some bytes → Manifest.IntegrityCheckpoint.decode bytes = .ok metadata →
    ∀ index < metadata.header.runCount.toNat,
      left metadata.header.generation index = right metadata.header.generation index

theorem SelectedRunsAgree.symm {binding : Option ByteArray} {left right : RunFiles}
    (same : SelectedRunsAgree binding left right) : SelectedRunsAgree binding right left :=
  fun bytes metadata selected decoded index inside => (same bytes metadata selected decoded index inside).symm

/-- A selected checkpoint depends only on the indices named by its manifest. -/
theorem SelectedIntegrityCheckpoint.withRunMap {binding : Option ByteArray}
    {left right : RunFiles} {checkpoint : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint left binding checkpoint)
    (same : SelectedRunsAgree binding left right) : SelectedIntegrityCheckpoint right binding checkpoint := by
  cases selected with
  | absent => exact .absent
  | @present bytes metadata files table decoded stored loaded =>
    have reads (indices : List Nat) (valid : ∀ index ∈ indices, index < metadata.header.runCount.toNat) :
        indices.mapM (left metadata.header.generation) = indices.mapM (right metadata.header.generation) := by
      induction indices with
      | nil => rfl
      | cons index rest ih =>
        simp only [List.mapM_cons, same bytes metadata rfl decoded index (valid index List.mem_cons_self),
          ih (fun other included => valid other (List.mem_cons_of_mem index included))]
    exact .present decoded
      ((reads (List.range metadata.header.runCount.toNat) (fun _ included => List.mem_range.mp included)).symm.trans stored)
      loaded

end Alvoki.Storage.DiskSession
