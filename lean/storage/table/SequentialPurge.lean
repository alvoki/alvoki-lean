import SequentialModel

namespace Alvoki.Sequential
open Compaction.Model

private def versionBoundaries (key floor : UInt64) (runs : List (History α)) : List UInt64 :=
  runs.flatMap fun run =>
    (run.rows.filter fun row => row.key == key && floor ≤ row.sequence).map Entry.sequence

private def purgeBoundaries (before after : Table α) (key floor : UInt64) : List UInt64 :=
  floor :: versionBoundaries key floor (before.histories ++ after.histories)

private theorem find_same_predicate (rows : List β) (a b : β → Bool)
    (same : ∀ row ∈ rows, a row = b row) :
    rows.find? a = rows.find? b := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [List.find?_cons, same row List.mem_cons_self,
      ih (fun r mem => same r (List.mem_cons_of_mem _ mem))]

private theorem across_same_eligibility (runs : List (History α)) (key at₁ at₂ : UInt64)
    (same : ∀ run ∈ runs, ∀ row ∈ run.rows, row.key = key →
      (row.sequence ≤ at₁ ↔ row.sequence ≤ at₂)) :
    across key at₁ runs = across key at₂ runs := by
  induction runs with
  | nil => rfl
  | cons run runs ih =>
    rw [across, across, ih (fun r mem => same r (List.mem_cons_of_mem _ mem))]
    have equalRows : winner run.rows key at₁ = winner run.rows key at₂ := by
      unfold winner
      apply find_same_predicate
      intro row mem
      by_cases matching : row.key = key
      · simp [eligible, matching, same run List.mem_cons_self row mem matching]
      · have miss : (row.key == key) = false := Bool.eq_false_iff.mpr (fun h => matching (beq_iff_eq.mp h))
        simp [eligible, miss]
    rw [equalRows]

private theorem boundary_mem {runs : List (History α)} {run : History α} {row : Entry (Option α)}
    {key floor : UInt64} (fromRun : run ∈ runs) (rowMem : row ∈ run.rows)
    (matching : row.key = key) (above : floor ≤ row.sequence) :
    row.sequence ∈ versionBoundaries key floor runs :=
  List.mem_flatMap.mpr ⟨run, fromRun, List.mem_map.mpr
    ⟨row, List.mem_filter.mpr ⟨rowMem, by simp [matching, above]⟩, rfl⟩⟩

/-- Each snapshot agrees with the greatest listed boundary at or below it. -/
private theorem purge_boundary_covers (before after : Table α) (key floor snapshot : UInt64)
    (live : floor ≤ snapshot) :
    ∃ boundary ∈ purgeBoundaries before after key floor,
      before.visibleEntry key snapshot = before.visibleEntry key boundary ∧
      after.visibleEntry key snapshot = after.visibleEntry key boundary := by
  let boundaries := purgeBoundaries before after key floor
  let eligibleBoundaries := boundaries.filter (fun b => b ≤ snapshot)
  have floorMem : floor ∈ eligibleBoundaries :=
    List.mem_filter.mpr ⟨by simp [boundaries, purgeBoundaries], decide_eq_true live⟩
  have nonempty : eligibleBoundaries ≠ [] := List.ne_nil_of_mem floorMem
  obtain ⟨bound, greatest, below⟩ : ∃ boundary ∈ eligibleBoundaries,
      ∀ b ∈ eligibleBoundaries, b ≤ boundary := by
    cases maxFound : eligibleBoundaries.max? with
    | none => exact (nonempty (List.max?_eq_none_iff.mp maxFound)).elim
    | some m => exact ⟨m, (List.max?_eq_some_iff.mp maxFound).1,
        (List.max?_eq_some_iff.mp maxFound).2⟩
  have boundLe : bound ≤ snapshot := of_decide_eq_true (List.mem_filter.mp greatest).2
  have agree (run : History α) (mem : run ∈ before.histories ++ after.histories)
      (row : Entry (Option α)) (rowMem : row ∈ run.rows) (matching : row.key = key) :
      row.sequence ≤ snapshot ↔ row.sequence ≤ bound := by
    refine ⟨fun visible => ?_, fun visible => UInt64.le_trans visible boundLe⟩
    by_cases above : floor ≤ row.sequence
    · apply below
      exact List.mem_filter.mpr
        ⟨List.mem_cons_of_mem _ (boundary_mem mem rowMem matching above), decide_eq_true visible⟩
    · exact UInt64.le_trans (UInt64.le_of_lt (UInt64.not_le.mp above)) (below floor floorMem)
  refine ⟨bound, (List.mem_filter.mp greatest).1, ?_, ?_⟩
  · unfold Table.visibleEntry
    rw [across_same_eligibility before.histories key snapshot bound
      (fun r mem => agree r (List.mem_append_left _ mem))]
  · unfold Table.visibleEntry
    rw [across_same_eligibility after.histories key snapshot bound
      (fun r mem => agree r (List.mem_append_right _ mem))]

/-- Check the floor and every relevant version boundary over both actual run sets. -/
def Table.purgeSafe [DecidableEq α] (before after : Table α) (key floor : UInt64) : Bool :=
  (purgeBoundaries before after key floor).all fun boundary =>
    decide (after.visibleEntry key boundary = before.visibleEntry key boundary)

theorem Table.purgeSafe_iff [DecidableEq α] (before after : Table α) (key floor : UInt64) :
    before.purgeSafe after key floor = true ↔
      ∀ snapshot, floor ≤ snapshot →
        after.visibleEntry key snapshot = before.visibleEntry key snapshot := by
  constructor
  · intro safe snapshot live
    let ⟨boundary, mem, old, new⟩ := purge_boundary_covers before after key floor snapshot live
    exact new.trans ((of_decide_eq_true (List.all_eq_true.mp safe boundary mem)).trans old.symm)
  · intro same
    apply List.all_eq_true.mpr
    intro boundary mem
    apply decide_eq_true
    apply same
    change boundary ∈ floor :: _ at mem
    rcases List.mem_cons.mp mem with rfl | version
    · exact UInt64.le_refl _
    · obtain ⟨run, _, occurs⟩ := List.mem_flatMap.mp version
      obtain ⟨row, rowMem, rfl⟩ := List.mem_map.mp occurs
      exact of_decide_eq_true (Bool.and_eq_true_iff.mp (List.mem_filter.mp rowMem).2).2

/-- Publish a candidate purge only when none of the actual remaining runs exposes a put. -/
def Table.purgeAt [DecidableEq α] (table : Table α) (index : Nat) (key sequence floor : UInt64) :
    Option (Table α) := do
  let candidate ← table.purgeCandidate index key sequence
  if table.purgeSafe candidate key floor then some candidate else none

theorem Table.purgeAt_visibleEntry [DecidableEq α] {table result : Table α}
    {index : Nat} {key sequence floor snapshot : UInt64}
    (changed : table.purgeAt index key sequence floor = some result)
    (live : floor ≤ snapshot) (query : UInt64) :
    result.visibleEntry query snapshot = table.visibleEntry query snapshot := by
  unfold Table.purgeAt at changed
  cases candidate : table.purgeCandidate index key sequence with
  | none => simp [candidate] at changed
  | some proposed =>
    by_cases safe : table.purgeSafe proposed key floor = true
    · have eq : proposed = result := by simpa [candidate, safe] using changed
      subst result
      by_cases queryEq : query = key
      · subst query
        exact (table.purgeSafe_iff proposed key floor).mp safe snapshot live
      · unfold Table.visibleEntry
        rw [Table.purgeCandidate_other_key candidate query snapshot queryEq]
    · simp [candidate, safe] at changed

theorem Table.purgeAt_preserves [DecidableEq α] {table result : Table α}
    {index : Nat} {key sequence floor snapshot : UInt64}
    (changed : table.purgeAt index key sequence floor = some result)
    (live : floor ≤ snapshot) (query start stop : UInt64) :
    result.lookup query snapshot = table.lookup query snapshot ∧
      result.range start stop snapshot = table.range start stop snapshot := by
  have same := Table.purgeAt_visibleEntry changed live
  constructor
  · rw [Table.lookup_eq_visibleEntry, Table.lookup_eq_visibleEntry, same query]
  · exact Table.range_of_visibleEntry_eq start stop snapshot same

end Alvoki.Sequential
