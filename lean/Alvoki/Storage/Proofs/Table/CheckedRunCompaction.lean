import Alvoki.Storage.Table.CompactionRead
import CompactionProofs

namespace Alvoki.Compaction
open Alvoki.Opt

theorem CheckedRun.compact_spec {left right out : CheckedRun} {floor : UInt64}
    (compacted : left.compact right floor = .ok out) :
    out.history = Sequential.compactPair left.history right.history floor := by
  have parsed := (openBytes_spec compacted).1
  rw [compactSpans_eq_compact] at parsed
  exact compact_history left.accepted right.accepted parsed

theorem CheckedRun.retainVersions_spec {run out : CheckedRun} {floor : UInt64}
    (retained : run.retainVersions floor = .ok out) : out.history = run.history.retain floor := by
  unfold retainVersions at retained
  cases encoded : ofHistory .empty with
  | error => simp [encoded, Bind.bind, Except.bind] at retained
  | ok empty =>
    have compacted : run.compact empty floor = .ok out := by
      simpa [encoded, Bind.bind, Except.bind] using retained
    rw [compact_spec compacted, ofHistory_spec encoded]
    apply Sequential.History.ext_rows
    simp [Sequential.compactPair, Sequential.History.union, Sequential.History.retain,
      Sequential.History.empty, Model.union_nil_right]

/-- Bound the actual packed file by the retained history's input rows.
The fixed v3 header and row width also account for retained tombstones. -/
theorem CheckedRun.byteSize_le_of_retainedHistory {source : Sequential.History UInt64} {out : CheckedRun}
    {floor : UInt64} (retained : out.history = source.retain floor) :
    out.run.bytes.size ≤ 16 + 32 * Model.retentionRowBound source.rows floor := by
  rw [out.byteSize_eq_history, retained]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left 32 (Model.retain_length_le source.ordered floor)) 16

theorem CheckedRun.retainVersions_byteSize_le {run out : CheckedRun} {floor : UInt64}
    (retained : run.retainVersions floor = .ok out) :
    out.run.bytes.size ≤ 16 + 32 * Model.retentionRowBound run.history.rows floor :=
  byteSize_le_of_retainedHistory (retainVersions_spec retained)

theorem CheckedRun.compact_byteSize_le {left right out : CheckedRun} {floor : UInt64}
    (compacted : left.compact right floor = .ok out) :
    out.run.bytes.size ≤ 16 + 32 * Model.retentionRowBound (left.history.union right.history).rows floor :=
  byteSize_le_of_retainedHistory (compact_spec compacted)

theorem CheckedRun.retainVersions_complete (run : CheckedRun) (floor : UInt64) :
    ∃ out, run.retainVersions floor = .ok out := by
  obtain ⟨empty, encoded⟩ := ofHistory_complete .empty (by
    have width := USize.le_size
    simp only [Sequential.History.empty, List.length_nil, Nat.mul_zero, Nat.add_zero]
    omega)
  have emptyRows : empty.run.decodeV3 = [] := by
    have mapped := congrArg Sequential.History.rows (ofHistory_spec encoded)
    change (empty.run.decodeV3.map _ : List (Model.Entry (Option UInt64))) = [] at mapped
    exact List.map_eq_nil_iff.mp mapped
  have limit : 16 + 32 * (retainedRows run.run empty.run floor).length < USize.size := by
    rw [retainedRows, emptyRows, Model.union_nil_right]
    have kept := (Model.retainFrom_sublist run.run.decodeV3 floor 0 false).length_le
    change (Model.retain run.run.decodeV3 floor).length ≤ run.run.decodeV3.length at kept
    have count : run.run.decodeV3.length = run.run.count.toNat := rawRows_length _ _
    rw [count] at kept
    have fits := run.fits
    rw [run.run.size_eq] at fits
    omega
  obtain ⟨_, parsed, _⟩ := compact_roundtrip run.accepted empty.accepted floor limit
  unfold retainVersions
  simp only [encoded, Bind.bind, Except.bind, CheckedRun.compact, openBytes]
  split
  · rename_i failed
    rw [compactSpans_eq_compact, parsed] at failed
    contradiction
  · exact ⟨_, rfl⟩


end Alvoki.Compaction
