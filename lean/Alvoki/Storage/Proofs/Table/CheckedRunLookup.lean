import Alvoki.Storage.Table.CompactionRead

namespace Alvoki.Compaction

private theorem key_le_bound (checked : CheckedRun) (target : UInt64) (i : Nat)
    (within : i < checked.run.count.toNat) :
    (rawRow checked.run.bytes i).key ≤ target ↔ i < (checked.upperBoundKey target).toNat := by
  have ⟨_, lo, hi⟩ := checked.upperBoundKey_spec target
  constructor
  · intro le
    by_cases past : (checked.upperBoundKey target).toNat ≤ i
    · exact (of_decide_eq_false (hi i past within) le).elim
    · omega
  · intro before
    exact of_decide_eq_true (lo i before)

private theorem raw_keyVersions (checked : CheckedRun) (key : UInt64) :
    (checked.run.decodeV3.filter (fun row => row.key == key)) =
      (List.range' (checked.lowerBoundKey key).toNat
        ((checked.upperBoundKey key).toNat - (checked.lowerBoundKey key).toNat)).map (rawRow checked.run.bytes) := by
  unfold Run.decodeV3 rawRows
  rw [List.filter_map]
  apply congrArg (List.map (rawRow checked.run.bytes))
  apply filterIndexRange _ _ _ _ (checked.upperBoundKey_spec key).1
  intro i bound
  have lo := checked.key_lt_bound key i bound
  have hi := key_le_bound checked key i bound
  simp only [Function.comp_apply, beq_iff_eq, ← hi, ← Nat.not_lt, ← lo, UInt64.not_lt]
  exact ⟨fun e => e ▸ ⟨UInt64.le_refl _, UInt64.le_refl _⟩,
    fun ⟨ge, le⟩ => UInt64.le_antisymm le ge⟩

/-- Mapping decoded values commutes with choosing the first eligible row. -/
theorem rawLookup_eq_winner (rows : List RawEntry) (key snapshot : UInt64) :
    ((rows.filter (fun row => row.key == key)).find?
      (fun row => row.sequence ≤ snapshot)).map RawEntry.version =
      Model.winner (rows.map RawEntry.version) key snapshot := by
  rw [List.find?_filter]
  change _ = (rows.map RawEntry.version).find? _
  rw [List.find?_map]
  rfl

theorem CheckedRun.lookupEntry_eq (checked : CheckedRun) (key snapshot : UInt64) :
    checked.lookupEntry key snapshot = Model.winner checked.history.rows key snapshot := by
  rw [checked.lookupEntry_as_interval, ← raw_keyVersions, rawLookup_eq_winner]
  rfl

theorem CheckedRun.lookup_eq (checked : CheckedRun) (key snapshot : UInt64) :
    checked.lookup key snapshot = Model.read checked.history.rows key snapshot := by
  rw [CheckedRun.lookup, checked.lookupEntry_eq, Model.read]

end Alvoki.Compaction
