import Alvoki.Experiments.SSTable.Recursive.NativeWriteProofs

namespace ImmutableSSTable.Recursive

open Unified (Checksum Layout NativeWriteEffects NativeWriteM NativeWriteState)

/-- Failure of exclusive create returns the exact error and reached state.
This branch does not enter the writer, the sync barrier or cleanup. -/
theorem buildFileWith_createError {ops : OutputOps (NativeWriteM handle inode) handle}
    {path : System.FilePath} {nextRow : NativeWriteM handle inode (Option Entry)}
    {crc : Checksum} {layout : Layout} {options : BuildOptions}
    {before reached : NativeWriteState handle inode} {error : String}
    (create : (ops.openFile path .writeNew).run before = .error error reached) :
    (buildFileWith ops crc path layout nextRow id options).run before = .error error reached := by
  unfold buildFileWith
  rw [freshOutput_result, create]

/-- Every error reported by the actual streaming writer, including a
supplier, validation, append or flush error, starts cleanup in the state
reached by that error. Cleanup cannot replace the primary error. -/
theorem buildFileWith_writeError {ops : OutputOps (NativeWriteM handle inode) handle}
    {path : System.FilePath} {nextRow : NativeWriteM handle inode (Option Entry)}
    {crc : Checksum} {layout : Layout} {options : BuildOptions} {output : handle}
    {before created reached : NativeWriteState handle inode} {error : String}
    (create : (ops.openFile path .writeNew).run before = .ok output created)
    (write : (buildStream crc layout (ops.sink output) nextRow id options).run created =
      .error error reached) :
    (buildFileWith ops crc path layout nextRow id options).run before =
      match (ops.remove path).run reached with
      | .ok _ after | .error _ after => .error error after := by
  unfold buildFileWith
  rw [freshOutput_result]
  simp only [create, write, failedOutput]
  cases (ops.remove path).run reached <;> rfl

/-- Healthy primitive effects turn exact model success into a native run
that produces the same image on its exclusively created, synced inode. -/
theorem buildFileWith_healthy {ops : OutputOps (NativeWriteM handle inode) handle}
    {path : System.FilePath} {nextRow : NativeWriteM handle inode (Option Entry)}
    {crc : Checksum} {layout : Layout} {options : BuildOptions}
    {before : NativeWriteState handle inode} {count : Nat} {bytes : ByteArray}
    (effects : NativeWriteEffects ops path nextRow)
    (available : HealthyNativeWrite ops path nextRow) (fresh : before.binding = none)
    (model : modelBuild crc layout before.rows options = .ok (count, bytes)) :
    count = before.rows.length ∧ Image layout crc bytes before.rows ∧
      ∃ after, (buildFileWith ops crc path layout nextRow id options).run before = .ok count after ∧
        after.rows = [] ∧ after.appended = bytes ∧ after.flushed = true ∧
        ∃ output identity created, (ops.openFile path .writeNew).run before = .ok output created ∧
          after.BoundTo path output identity ∧ after.durable = some (identity, bytes) := by
  obtain ⟨exactCount, image⟩ := modelBuild_ok model
  exact ⟨exactCount, image, buildFileWith_of_modelBuild_ok effects available fresh model⟩

end ImmutableSSTable.Recursive
