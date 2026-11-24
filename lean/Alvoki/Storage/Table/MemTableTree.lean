import Alvoki.Storage.Table.MemTableContract
import Std.Data.TreeMap

namespace Alvoki.Storage
open Alvoki.Sequential (History)
open Alvoki.Compaction.Model
open Std

private abbrev Version := UInt64 × UInt64

private def compareVersion : Version → Version → Ordering :=
  compareLex (compareOn Prod.fst) (fun a b => compare b.2 a.2)

private instance : TransCmp compareVersion := by
  unfold compareVersion
  have : TransCmp (fun (a b : Version) => compare a.2 b.2) :=
    inferInstanceAs (TransCmp (compareOn Prod.snd))
  infer_instance

private theorem compareVersion_eq (a b : Version) :
    compareVersion a b = .eq ↔ a = b := by
  simp [compareVersion, compareLex_eq_eq, compareOn, Prod.ext_iff]
  intro _
  exact eq_comm

private instance : LawfulBEqCmp compareVersion where
  compare_eq_iff_beq := by simp [compareVersion_eq]

private theorem compareUInt_lt (a b : UInt64) : compare a b = .lt ↔ a < b := by
  exact compareOfLessAndEq_eq_lt

private theorem compareVersion_lt (a b : Version) :
    compareVersion a b = .lt ↔ a.1 < b.1 ∨ a.1 = b.1 ∧ b.2 < a.2 := by
  simp [compareVersion, compareLex, compareOn, Ordering.then_eq_lt, compareUInt_lt]

private abbrev Slot := Version × Option UInt64

private def toRow (slot : Slot) : Entry (Option UInt64) :=
  ⟨slot.1.1, slot.1.2, slot.2⟩

private def version (row : Entry (Option UInt64)) : Version := (row.key, row.sequence)

private theorem slot_before (a b : Slot) : before (toRow a) (toRow b) = true ↔
    compareVersion a.1 b.1 = .lt := by
  simp [before_iff, compareVersion_lt, toRow]

/-- Store each version under an ascending key and descending sequence. -/
structure MemTableTree where
  private mk ::
  private entries : Std.TreeMap Version (Option UInt64) compareVersion

namespace MemTableTree

private def empty : MemTableTree := ⟨∅⟩

private def insert (tree : MemTableTree) (row : Entry (Option UInt64)) : MemTableTree :=
  ⟨tree.entries.insert (version row) row.payload⟩

private def history (tree : MemTableTree) : History UInt64 :=
  ⟨tree.entries.toList.map toRow, List.pairwise_map.mpr
    (tree.entries.ordered_keys_toList.imp (fun h => (slot_before _ _).mpr h))⟩

private theorem history_empty : history empty = .empty := rfl

private theorem distinct_of_before {a b : Entry (Option UInt64)}
    (ordered : before a b = true) : sameVersion a b = false := by
  apply Bool.eq_false_iff.mpr
  intro tie
  obtain ⟨key, seq⟩ := sameVersion_iff.mp tie
  rcases before_iff.mp ordered with lt | ⟨_, lt⟩
  · exact UInt64.lt_irrefl _ (key ▸ lt)
  · exact UInt64.lt_irrefl _ (seq ▸ lt)

private theorem sameVersion_symm (a b : Entry (Option UInt64)) :
    sameVersion a b = sameVersion b a := by
  apply Bool.eq_iff_iff.mpr
  constructor <;> intro h
  · obtain ⟨key, seq⟩ := sameVersion_iff.mp h
    exact sameVersion_iff.mpr ⟨key.symm, seq.symm⟩
  · obtain ⟨key, seq⟩ := sameVersion_iff.mp h
    exact sameVersion_iff.mpr ⟨key.symm, seq.symm⟩

private theorem filter_of_before (row : Entry (Option UInt64)) (rows : List (Entry (Option UInt64)))
    (earlier : ∀ other ∈ rows, before row other = true) :
    rows.filter (fun other => !sameVersion row other) = rows := by
  apply List.filter_eq_self.mpr
  intro other mem
  simp [distinct_of_before (earlier other mem)]

private theorem union_singleton_perm (rows : List (Entry (Option UInt64)))
    (ordered : Ordered rows) (row : Entry (Option UInt64)) :
    (union rows [row]).Perm (row :: rows.filter (fun item => !sameVersion row item)) := by
  induction rows with
  | nil => simp
  | cons head rest ih =>
    have orderedTail := (List.pairwise_cons.mp ordered).1
    by_cases first : before head row = true
    · have diff : sameVersion row head = false := by
        rw [sameVersion_symm]
        exact distinct_of_before first
      rw [List.filter_cons, union.eq_3]
      simp [first, diff]
      exact ((ih ordered.tail).cons head).trans (List.Perm.swap row head _)
    · by_cases tie : sameVersion head row = true
      · have test : sameVersion row head = true := by rwa [sameVersion_symm]
        have filter : rest.filter (fun other => !sameVersion row other) = rest := by
          apply filter_of_before
          obtain ⟨key, seq⟩ := sameVersion_iff.mp tie
          intro other mem
          simpa only [before_iff, ← key, ← seq] using orderedTail other mem
        rw [List.filter_cons, union.eq_3]
        simp [first, tie, test, filter]
      · have after := before_flip (Bool.eq_false_iff.mpr first) (Bool.eq_false_iff.mpr tie)
        have filter : (head :: rest).filter (fun other => !sameVersion row other) = head :: rest := by
          apply filter_of_before
          intro other mem
          rcases List.mem_cons.mp mem with rfl | mem
          · exact after
          · exact before_trans after (orderedTail other mem)
        rw [filter, union.eq_3]
        simp [first, tie]

private theorem history_insert (tree : MemTableTree) (row : Entry (Option UInt64)) :
    history (insert tree row) = (history tree).union (.singleton row) := by
  apply History.ext_rows
  have hp := (Std.TreeMap.toList_insert_perm (t := tree.entries) (k := version row)
    (v := row.payload)).map toRow
  have hp' := union_singleton_perm (history tree).rows (history tree).ordered row
  have perm : (history (insert tree row)).rows.Perm ((history tree).union (.singleton row)).rows := by
    apply List.Perm.trans _ hp'.symm
    have sameFilter : (fun slot : Slot => decide (¬(version row == slot.1) = true)) =
        (fun item => !sameVersion row item) ∘ toRow := by
      funext slot
      rw [Bool.eq_iff_iff]
      change decide (¬(version row == slot.1) = true) = true ↔ !sameVersion row (toRow slot) = true
      simp [version, toRow, Prod.ext_iff]
    rw [sameFilter] at hp
    simpa [history, insert, List.map_cons, ← List.filter_map, toRow, version] using hp
  apply List.Perm.eq_of_pairwise _ (history (insert tree row)).ordered
    ((history tree).union (.singleton row)).ordered perm
  intro a b _ _ ab ba
  have self := before_trans ab ba
  simp [before] at self

private def isEmpty (tree : MemTableTree) : Bool := tree.entries.isEmpty

private theorem isEmpty_spec (tree : MemTableTree) :
    isEmpty tree = (history tree).rows.isEmpty := by
  simp [isEmpty, history]

private theorem ge_iff (slot : Slot) (key snapshot : UInt64) :
    (compareVersion slot.1 (key, snapshot)).isGE = true ↔
      key < slot.1.1 ∨ slot.1.1 = key ∧ slot.1.2 ≤ snapshot := by
  rw [Ordering.isGE_iff_ne_lt, compareVersion_lt]
  simp only [not_or, not_and, UInt64.not_lt]
  constructor
  · rintro ⟨le, h⟩
    by_cases eq : slot.1.1 = key
    · exact Or.inr ⟨eq, h eq⟩
    · exact Or.inl (UInt64.lt_of_le_of_ne le (Ne.symm eq))
  · rintro (lt | ⟨rfl, le⟩)
    · exact ⟨UInt64.le_of_lt lt, fun eq => False.elim (UInt64.lt_irrefl _ (eq ▸ lt))⟩
    · exact ⟨UInt64.le_refl _, fun _ => le⟩

private theorem le_iff (slot : Slot) (key snapshot : UInt64) :
    (compareVersion slot.1 (key, snapshot)).isLE = true ↔
      slot.1.1 < key ∨ slot.1.1 = key ∧ snapshot ≤ slot.1.2 := by
  rw [OrientedCmp.eq_swap (cmp := compareVersion), Ordering.isLE_swap,
    Ordering.isGE_iff_ne_lt, compareVersion_lt]
  simp only [not_or, not_and, UInt64.not_lt]
  constructor
  · rintro ⟨le, h⟩
    by_cases eq : slot.1.1 = key
    · exact Or.inr ⟨eq, h eq.symm⟩
    · exact Or.inl (UInt64.lt_of_le_of_ne le eq)
  · rintro (lt | ⟨eq, le⟩)
    · exact ⟨UInt64.le_of_lt lt, fun eq => False.elim (UInt64.lt_irrefl _ (eq ▸ lt))⟩
    · exact ⟨eq ▸ UInt64.le_refl _, fun _ => le⟩

private def lookup (tree : MemTableTree) (key snapshot : UInt64) :
    Option (Entry (Option UInt64)) :=
  (tree.entries[(key, snapshot)...=(key, 0)].iter.first?).map toRow

private theorem lookup_spec (tree : MemTableTree) (key snapshot : UInt64) :
    lookup tree key snapshot = winner (history tree).rows key snapshot := by
  unfold lookup winner history
  rw [← Iter.head?_toList, Slice.toList_iter, Std.TreeMap.toList_rcc compareVersion,
    List.head?_filter, List.find?_map]
  congr 2
  funext slot
  rw [Bool.eq_iff_iff]
  change decide (_ ∧ _) = true ↔ eligible key snapshot (toRow slot) = true
  simp only [decide_eq_true_eq, ge_iff, le_iff, eligible, toRow, Bool.and_eq_true, beq_iff_eq,
    UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, ← UInt64.toNat_inj, UInt64.toNat_zero]
  omega

private def rangeRows (tree : MemTableTree) (start stop : UInt64) : List (Entry (Option UInt64)) :=
  (tree.entries[(start, UInt64.ofNat (UInt64.size - 1))...<(stop, UInt64.ofNat (UInt64.size - 1))].toList).map toRow

private theorem le_max (x : UInt64) : x ≤ UInt64.ofNat (UInt64.size - 1) := by
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt']
  · exact Nat.le_sub_one_of_lt x.toNat_lt
  · decide

private theorem rangeRows_eq (tree : MemTableTree) (start stop : UInt64) :
    rangeRows tree start stop = (MemTableContract.clip (history tree) start stop).rows := by
  unfold rangeRows
  rw [Std.TreeMap.toList_rco compareVersion]
  simp only [MemTableContract.clip, history, List.filter_map]
  congr 1
  congr 1
  funext slot
  rw [Bool.eq_iff_iff]
  change decide (_ ∧ _) = true ↔ (decide (start ≤ slot.1.1) && decide (slot.1.1 < stop)) = true
  simp only [decide_eq_true_eq, ge_iff, Ordering.isLT_iff_eq_lt, compareVersion_lt, le_max,
    UInt64.not_lt.mpr (le_max _), and_true, and_false, or_false, Bool.and_eq_true]
  rw [UInt64.le_iff_lt_or_eq]
  exact ⟨fun ⟨a, b⟩ => ⟨a.imp id Eq.symm, b⟩, fun ⟨a, b⟩ => ⟨a.imp id Eq.symm, b⟩⟩

private def range (tree : MemTableTree) (start stop : UInt64) : History UInt64 :=
  ⟨rangeRows tree start stop, rangeRows_eq tree start stop ▸
    (MemTableContract.clip (history tree) start stop).ordered⟩

private theorem range_spec (tree : MemTableTree) (start stop : UInt64) :
    range tree start stop = MemTableContract.clip (history tree) start stop :=
  History.ext_rows (rangeRows_eq tree start stop)

def backend : MemTableBackend MemTableTree where
  history := history
  empty := empty
  insert := insert
  isEmpty := isEmpty
  lookup := lookup
  range := range
  history_empty := history_empty
  history_insert := history_insert
  isEmpty_spec := isEmpty_spec
  lookup_spec := lookup_spec
  range_spec := range_spec

end MemTableTree
end Alvoki.Storage
