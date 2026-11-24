import Alvoki.Storage.Disk.Recovery

namespace Alvoki.Sequential
open Compaction.Model

/-- Every version, including tombstones, is covered by the indicated clock. -/
def Table.RowsBounded (table : Table α) (committed : UInt64) : Prop :=
  ∀ run ∈ table.histories, ∀ row ∈ run.rows, row.sequence ≤ committed

private theorem newest_none_right (candidate : Option (Entry α)) :
    newest candidate none = candidate := by cases candidate <;> rfl

private theorem newest_if_fresh {run : History α} {row : Entry (Option α)}
    (fresh : ∀ old ∈ run.rows, old.sequence < row.sequence)
    (key snapshot : UInt64) (fallback : Option (Entry (Option α))) :
    newest (winner run.rows key snapshot) (if eligible key snapshot row then some row else fallback) =
      if eligible key snapshot row then some row
      else newest (winner run.rows key snapshot) fallback := by
  split
  · cases found : winner run.rows key snapshot with
    | none => rfl
    | some old =>
      have earlier := fresh old (List.mem_of_find?_eq_some found)
      simp [newest, UInt64.not_lt.mpr (UInt64.le_of_lt earlier)]
  · rfl

private theorem across_write_fresh (runs : List (History α)) (memory : History α)
    (row : Entry (Option α)) (key snapshot : UInt64)
    (fresh : ∀ run ∈ runs ++ [memory], ∀ old ∈ run.rows, old.sequence < row.sequence) :
    across key snapshot (runs ++ [memory.union (.singleton row)]) =
      if eligible key snapshot row then some row else across key snapshot (runs ++ [memory]) := by
  induction runs with
  | nil =>
    simp only [List.nil_append, across, newest_none_right]
    change winner (Compaction.Model.union memory.rows (History.singleton row).rows) key snapshot = _
    rw [winner_union memory.ordered (History.singleton row).ordered]
    have single : winner (History.singleton row).rows key snapshot =
        if eligible key snapshot row then some row else none := by
      simp [History.singleton, winner]
    rw [single, newest_if_fresh (fresh memory (by simp)), newest_none_right]
  | cons run rest ih =>
    have tailFresh : ∀ source ∈ rest ++ [memory], ∀ old ∈ source.rows,
        old.sequence < row.sequence :=
      fun source member => fresh source (List.mem_cons_of_mem run member)
    simp only [List.cons_append, across, ih tailFresh]
    exact newest_if_fresh (fresh run (by simp)) key snapshot _

/-- A strictly newer row sets its key at and after its sequence. Other
keys and earlier snapshots still use their original winners. -/
theorem Table.visibleEntry_write_fresh {table : Table α} {committed : UInt64}
    (bounded : table.RowsBounded committed) {row : Entry (Option α)}
    (newer : committed < row.sequence) (key snapshot : UInt64) :
    (table.write row).visibleEntry key snapshot =
      if eligible key snapshot row then (some row).filter (·.payload.isSome)
      else table.visibleEntry key snapshot := by
  unfold visibleEntry
  change (across key snapshot (table.runs ++ [table.memory.union (.singleton row)])).filter
    (·.payload.isSome) = _
  rw [across_write_fresh _ _ _ _ _ (fun run member old inside =>
    UInt64.lt_of_le_of_lt (bounded run member old inside) newer)]
  split <;> rfl

theorem SnapshotTable.write_rowsBounded {before after : SnapshotTable α}
    {key : UInt64} {value : Option α} (written : before.write key value = some after)
    (bounded : before.table.RowsBounded before.committed) :
    after.table.RowsBounded after.committed := by
  obtain ⟨seq, _, updated⟩ := write_spec written
  have advances : before.committed ≤ after.committed := by
    rw [UInt64.le_iff_toNat_le, seq]
    omega
  intro run member row inside
  rw [updated] at member
  change run ∈ before.table.runs ++ [before.table.memory.union (.singleton _)] at member
  rcases List.mem_append.mp member with prior | pending
  · exact UInt64.le_trans (bounded run (List.mem_append_left _ prior) row inside) advances
  · obtain rfl := List.mem_singleton.mp pending
    rcases mem_union inside with prior | added
    · have oldBound := bounded before.table.memory (by simp [Table.histories]) row prior
      exact UInt64.le_trans oldBound advances
    · obtain rfl := List.mem_singleton.mp added
      exact UInt64.le_refl _

end Alvoki.Sequential

namespace Alvoki.Storage
open Sequential

/-- Transfer the bounds on the packed runs and memtable to the rows of
their abstract interpretation. -/
theorem PackedTable.Refines.rowsBounded {state : PackedTable} {model : SnapshotTable UInt64}
    (refines : state.Refines model) (bounded : state.RowBounds) :
    model.table.RowsBounded model.committed := by
  rw [← refines.table, ← refines.committed]
  intro run member row inside
  change run ∈ state.runs.map (·.history) ++ [state.memory] at member
  rcases List.mem_append.mp member with fromRun | pending
  · obtain ⟨source, present, rfl⟩ := List.mem_map.mp fromRun
    exact bounded.runs source present row inside
  · obtain rfl := List.mem_singleton.mp pending
    exact bounded.memory row inside

/-- Replaying the same sequenced WAL frames preserves visible entries from
the chosen retention floor upward, even for snapshots past the current
clock. The latter case lets the agreement carry through subsequent writes. -/
theorem SnapshotWalReplay.visibleEntry_agrees {left right leftAfter rightAfter : SnapshotTable UInt64}
    {events : List WAL.Write} {floor : UInt64}
    (leftReplay : SnapshotWalReplay left events leftAfter)
    (rightReplay : SnapshotWalReplay right events rightAfter)
    (clock : left.committed = right.committed)
    (leftBound : left.table.RowsBounded left.committed)
    (rightBound : right.table.RowsBounded right.committed)
    (visible : ∀ snapshot : UInt64, floor ≤ snapshot → ∀ key,
      left.table.visibleEntry key snapshot = right.table.visibleEntry key snapshot) :
    leftAfter.committed = rightAfter.committed ∧
      leftAfter.table.RowsBounded leftAfter.committed ∧
      rightAfter.table.RowsBounded rightAfter.committed ∧
      ∀ snapshot : UInt64, floor ≤ snapshot → ∀ key,
        leftAfter.table.visibleEntry key snapshot = rightAfter.table.visibleEntry key snapshot := by
  induction leftReplay generalizing right rightAfter with
  | nil =>
    cases rightReplay
    exact ⟨clock, leftBound, rightBound, visible⟩
  | @cons left leftNext leftAfter event rest leftWrite leftSequence _ ih =>
    cases rightReplay with
    | @cons right rightNext rightAfter _ _ rightWrite rightSequence suffix =>
      obtain ⟨leftSuccessor, _, leftTable⟩ := SnapshotTable.write_spec leftWrite
      obtain ⟨rightSuccessor, _, rightTable⟩ := SnapshotTable.write_spec rightWrite
      have freshLeft : left.committed < leftNext.committed := by
        rw [UInt64.lt_iff_toNat_lt, leftSuccessor]
        omega
      have freshRight : right.committed < rightNext.committed := by
        rw [UInt64.lt_iff_toNat_lt, rightSuccessor]
        omega
      refine ih suffix (leftSequence.trans rightSequence.symm)
        (SnapshotTable.write_rowsBounded leftWrite leftBound)
        (SnapshotTable.write_rowsBounded rightWrite rightBound) ?_
      intro snapshot retained key
      rw [leftTable, rightTable, Table.visibleEntry_write_fresh leftBound freshLeft,
        Table.visibleEntry_write_fresh rightBound freshRight, leftSequence, rightSequence,
        visible snapshot retained key]

/-- The suffix preserves point and ordered range reads wherever the two
base tables agreed on visible entries. -/
theorem SnapshotWalReplay.reads_agree {left right leftAfter rightAfter : SnapshotTable UInt64}
    {events : List WAL.Write} {floor : UInt64}
    (leftReplay : SnapshotWalReplay left events leftAfter)
    (rightReplay : SnapshotWalReplay right events rightAfter)
    (clock : left.committed = right.committed)
    (leftBound : left.table.RowsBounded left.committed)
    (rightBound : right.table.RowsBounded right.committed)
    (visible : ∀ snapshot : UInt64, floor ≤ snapshot → ∀ key,
      left.table.visibleEntry key snapshot = right.table.visibleEntry key snapshot)
    {snapshot : UInt64} (retained : floor ≤ snapshot) :
    (∀ key, leftAfter.table.lookup key snapshot = rightAfter.table.lookup key snapshot) ∧
      ∀ start stop,
        leftAfter.table.range start stop snapshot = rightAfter.table.range start stop snapshot := by
  obtain ⟨_, _, _, agreement⟩ := leftReplay.visibleEntry_agrees rightReplay clock leftBound rightBound visible
  have same := agreement snapshot retained
  exact ⟨fun key => by rw [Table.lookup_eq_visibleEntry, Table.lookup_eq_visibleEntry, same key],
    fun start stop => Table.range_of_visibleEntry_eq start stop snapshot same⟩

end Alvoki.Storage
