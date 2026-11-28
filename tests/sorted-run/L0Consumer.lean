import Alvoki.Experiments.L0.Proofs
import Alvoki.Experiments.SortedRun.Proofs

namespace ExperimentalL0

/-- The materialized oracle from compaction research PR #31 at f69b6522. -/
private def mergeReference (newer older : Rows) : Rows :=
  (replay (older.reverse ++ newer.reverse)).toList

private theorem reference_lookup (newer older : Rows) (key : UInt64) :
    lookupRows (mergeReference newer older) key =
      (lookupRows newer key).or (lookupRows older key) := by
  rw [mergeReference, rows_lookup, replay_lookup, latest_append]
  simp [latest, lookupRows]

private theorem merge_lookupRows (rows : Rows) (key : UInt64) :
    lookupRows rows key = (SortedRun.lookup Prod.fst rows key).map Prod.snd := by
  have keyTest (row : Change) : (row.1 == key) = decide (row.1 = key) := by
    apply Bool.eq_iff_iff.mpr
    simp
  simp [lookupRows, SortedRun.lookup, keyTest]

theorem sortedRun_matches_compaction_reference {newer older : Rows}
    (left : newer.Ordered) (right : older.Ordered) (key : UInt64) :
    lookupRows (SortedRun.merge Prod.fst newer older) key =
      lookupRows (mergeReference newer older) key := by
  rw [reference_lookup, merge_lookupRows, SortedRun.merge_lookup Prod.fst left right,
    merge_lookupRows newer, merge_lookupRows older]
  cases SortedRun.lookup Prod.fst newer key <;> rfl

/-- The engine's tombstone is the winning value, including against a put
with the same key in the older run. -/
example :
    lookupRows (SortedRun.merge Prod.fst [(1, .delete)] [(1, .put 7), (2, .put 9)]) 1 =
      some .delete := by
  rw [SortedRun.merge]
  simp [lookupRows, show ¬ (1 : UInt64) < 1 by decide]

end ExperimentalL0
