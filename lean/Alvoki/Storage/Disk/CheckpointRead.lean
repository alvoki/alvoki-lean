import Alvoki.Storage.Disk.Manifest
import Alvoki.Storage.Table.PackedTable

namespace Alvoki.Storage
open Alvoki.Compaction (CheckedRun)

private def installRuns (runs : List CheckedRun) (header : Manifest.Checkpoint) :
    Except String PackedTable :=
  match PackedTable.restore runs header.committed header.floor with
  | none => .error "installed v3 runs exceed the manifest watermark"
  | some table => .ok table

/-- Validate the ordered file contents identified by a checkpoint. -/
def loadRunSet (header : Manifest.Checkpoint) (files : List ByteArray) : Except String PackedTable := do
  if files.length ≠ header.runCount.toNat then throw "installed run count differs from the manifest"
  let runs ← files.mapM CheckedRun.openBytes
  installRuns runs header

/-- A successful run-set load decodes the ordered files and restores the
table with the selected manifest watermark and floor. -/
theorem loadRunSet_restored {header : Manifest.Checkpoint} {files : List ByteArray}
    {table : PackedTable} (loaded : loadRunSet header files = .ok table) :
    ∃ runs, files.mapM CheckedRun.openBytes = .ok runs ∧
      PackedTable.restore runs header.committed header.floor = some table := by
  unfold loadRunSet at loaded
  split at loaded
  · contradiction
  · cases decoded : files.mapM CheckedRun.openBytes with
    | error => rw [decoded] at loaded; contradiction
    | ok runs =>
      rw [decoded] at loaded
      change installRuns runs header = Except.ok table at loaded
      unfold installRuns at loaded
      split at loaded
      · contradiction
      · rename_i restored restoredEq
        cases loaded
        exact ⟨runs, rfl, restoredEq⟩

/-- A loaded checkpoint starts a new session with no active snapshot pins. -/
theorem loadRunSet_clearsPins {header : Manifest.Checkpoint} {files : List ByteArray}
    {table : PackedTable} (loaded : loadRunSet header files = .ok table) :
    table.pins.active = [] := by
  obtain ⟨_, _, restored⟩ := loadRunSet_restored loaded
  exact (PackedTable.restore_spec restored).2.2.2.2

private theorem readWrittenRuns (runs : List CheckedRun) :
    (runs.map (·.run.bytes)).mapM CheckedRun.openBytes = Except.ok runs := by
  induction runs with
  | nil => rfl
  | cons run rest ih =>
    simp only [List.map_cons, List.mapM_cons, run.openOwnBytes]
    change Except.map (run :: ·) ((rest.map (·.run.bytes)).mapM CheckedRun.openBytes) = _
    rw [ih]
    rfl

theorem loadRunSet_written (header : Manifest.Checkpoint) (runs : List CheckedRun)
    (count : runs.length = header.runCount.toNat) (floor : header.floor ≤ header.committed)
    (bounded : ∀ run ∈ runs, ∀ row ∈ run.history.rows, row.sequence ≤ header.committed) :
    ∃ table, loadRunSet header (runs.map (·.run.bytes)) = .ok table ∧
      PackedTable.restore runs header.committed header.floor = some table := by
  obtain ⟨table, restored⟩ := PackedTable.restore_complete runs header.committed header.floor floor bounded
  refine ⟨table, ?_, restored⟩
  simp only [loadRunSet, List.length_map, count, ne_eq, not_true_eq_false, ↓reduceIte,
    readWrittenRuns]
  change installRuns runs header = .ok table
  simp [installRuns, restored]

/-- Read the manifest's run files in increasing index order. Grow the array
as reads succeed since the run count comes from on-disk input. -/
@[inline] def readCheckpointRunBytes [Monad m] (read : UInt64 → Nat → m ByteArray)
    (manifest : Manifest.Checkpoint) : m (List ByteArray) := do
  let mut files : Array ByteArray := #[]
  for index in [:manifest.runCount.toNat] do
    files := files.push (← read manifest.generation index)
  return files.toList

/-- The executable loop reads exactly the manifest's run indices in order. -/
theorem readCheckpointRunBytes_eq_mapM [Monad m] [LawfulMonad m]
    (read : UInt64 → Nat → m ByteArray) (header : Manifest.Checkpoint) :
    readCheckpointRunBytes read header =
      (List.range header.runCount.toNat).mapM (read header.generation) := by
  simp [readCheckpointRunBytes, Std.Legacy.Range.size, ← List.range_eq_range']

end Alvoki.Storage
