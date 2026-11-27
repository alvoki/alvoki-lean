import Alvoki.Experiments.SSTable.Proofs.UnifiedImage
import Alvoki.Experiments.SSTable.Proofs.UnifiedSearch

namespace ImmutableSSTable.Unified

/-- Row positions in an index advance by the sizes of its child groups. -/
def RowsAt (refOf : α → Ref) (rowsOf : α → List Entry) : Nat → List α → Prop
  | _, [] => True
  | first, group :: tail =>
    (refOf group).firstRow = first ∧
    (refOf group).count = (rowsOf group).length ∧
    0 < (rowsOf group).length ∧
    RowsAt refOf rowsOf (first + (rowsOf group).length) tail

theorem RowsAt.of_adjacent (groups : List α) (refOf : α → Ref) (rowsOf : α → List Entry)
    (adjacent : ValidRefsAfter previous (groups.map refOf))
    (counts : ∀ g ∈ groups, (refOf g).count = (rowsOf g).length)
    (head : ∀ g ∈ groups.head?, (refOf g).firstRow = first) :
    RowsAt refOf rowsOf first groups := by
  induction groups generalizing previous first with
  | nil => trivial
  | cons group rest ih =>
    obtain ⟨valid, _, later⟩ := adjacent
    have starts := head group rfl
    have count := counts group (by simp)
    refine ⟨starts, count, by have := valid.2.2.1; omega, ?_⟩
    apply ih later (fun g hg => counts g (by simp [hg]))
    intro next mem
    cases rest with
    | nil => cases mem
    | cons second tail =>
      have same : next = second := by simpa [eq_comm] using mem
      subst next
      have relation := later.2.1 (refOf group) rfl
      exact relation.2.1.symm.trans (by rw [starts, count])

theorem RowsAt.last_end (placed : RowsAt refOf rowsOf first groups)
    (last : groups.getLast? = some group) :
    (refOf group).firstRow + (refOf group).count = first + (groups.flatMap rowsOf).length := by
  induction groups generalizing first with
  | nil => simp at last
  | cons head tail ih =>
    obtain ⟨starts, count, _, later⟩ := placed
    cases tail with
    | nil =>
      simp at last
      subst group
      simp [starts, count]
    | cons next rest =>
      have endEq := ih later (by simpa using last)
      simpa [Nat.add_assoc] using endEq

theorem checkChildren_bounds {refs : Array Ref}
    (checked : checkChildren refs first count endAt = .ok ()) :
    ∃ start last, refs[0]? = some start ∧ refs.back? = some last ∧
      start.firstRow = first ∧ last.firstRow + last.count = first + count := by
  cases start : refs[0]? with
  | none => simp [checkChildren, start, throw] at checked
  | some startRef =>
    cases last : refs.back? with
    | none => simp [checkChildren, start, last, throw] at checked
    | some lastRef =>
      by_cases condition : startRef.firstRow = first ∧
          lastRef.firstRow + lastRef.count = first + count ∧ lastRef.offset + lastRef.size ≤ endAt
      · exact ⟨startRef, lastRef, rfl, rfl, condition.1, condition.2.1⟩
      · simp [checkChildren, start, last, condition, throw] at checked

theorem RowsAt.of_checked {groups : Array α} (refOf : α → Ref) (rowsOf : α → List Entry)
    (valid : ValidRefs (groups.map refOf))
    (checked : checkChildren (groups.map refOf) first count endAt = .ok ())
    (counts : ∀ g ∈ groups.toList, (refOf g).count = (rowsOf g).length) :
    RowsAt refOf rowsOf first groups.toList ∧
      (groups.toList.flatMap rowsOf).length = count := by
  obtain ⟨start, last, starts, ends, firstEq, endEq⟩ := checkChildren_bounds checked
  have headEq : groups.toList.head?.map refOf = some start := by
    simpa [List.head?_eq_getElem?] using starts
  have lastEq : groups.toList.getLast?.map refOf = some last := by
    simpa only [← Array.getLast?_toList, Array.toList_map, List.getLast?_map] using ends
  have adjacent : ValidRefsAfter none (groups.toList.map refOf) := by
    simpa only [Array.toList_map] using valid.adjacent
  have placed := RowsAt.of_adjacent groups.toList refOf rowsOf adjacent counts (first := first) (by
    intro g hg
    have matchHead : groups.toList.head? = some g := hg
    rw [matchHead] at headEq
    exact (congrArg Ref.firstRow (Option.some.inj headEq)).trans firstEq)
  cases lastMember : groups.toList.getLast? with
  | none => simp [lastMember] at lastEq
  | some group =>
    rw [lastMember] at lastEq
    have lastRef : refOf group = last := Option.some.inj lastEq
    have length := placed.last_end lastMember
    rw [lastRef, endEq] at length
    exact ⟨placed, by omega⟩

theorem rowsAt_position (placed : RowsAt refOf rowsOf first groups)
    (i : Nat) (inside : i < groups.length) :
    ∃ before after, groups.flatMap rowsOf = before ++ rowsOf groups[i] ++ after ∧
      (refOf groups[i]).firstRow = first + before.length ∧
      (refOf groups[i]).count = (rowsOf groups[i]).length ∧ 0 < (rowsOf groups[i]).length := by
  induction groups generalizing first i with
  | nil => simp at inside
  | cons group tail ih =>
    obtain ⟨start, count, positive, later⟩ := placed
    cases i with
    | zero => exact ⟨[], tail.flatMap rowsOf, by simp, by simpa using start, count, positive⟩
    | succ i =>
      have bound : i < tail.length := by simpa using inside
      obtain ⟨before, after, split, position, size, nonempty⟩ := ih later i bound
      refine ⟨rowsOf group ++ before, after, ?_, ?_, size, nonempty⟩
      · simp [split, List.append_assoc]
      · simpa [List.length_append, Nat.add_assoc] using position

private theorem rowsAt_separated (placed : RowsAt refOf rowsOf first groups)
    (i j : Nat) (hi : i < groups.length) (hj : j < groups.length) (before : i < j) :
    (refOf groups[i]).firstRow + (refOf groups[i]).count ≤ (refOf groups[j]).firstRow := by
  induction groups generalizing first i j with
  | nil => simp at hi
  | cons group tail ih =>
    obtain ⟨start, count, _, later⟩ := placed
    cases j with
    | zero => omega
    | succ j =>
      have bound : j < tail.length := by simpa using hj
      cases i with
      | zero =>
        obtain ⟨_, _, _, position, _, _⟩ := rowsAt_position later j bound
        simp only [List.getElem_cons_zero, List.getElem_cons_succ]
        omega
      | succ i =>
        exact ih later i j (by simpa using hi) bound (by omega)

private theorem rowsAt_covers (placed : RowsAt refOf rowsOf first groups)
    (index : Nat) (lo : first ≤ index) (hi : index < first + (groups.flatMap rowsOf).length) :
    ∃ (j : Nat) (hj : j < groups.length), let ref := refOf (getElem groups j hj);
      ref.firstRow ≤ index ∧ index < ref.firstRow + ref.count := by
  induction groups generalizing first with
  | nil => simp at hi; omega
  | cons group tail ih =>
    obtain ⟨start, count, _, later⟩ := placed
    by_cases inside : index < first + (rowsOf group).length
    · exact ⟨0, by simp, by simpa [start] using lo, by simpa [start, count] using inside⟩
    · have bound : index < first + (rowsOf group).length + (tail.flatMap rowsOf).length := by
        simpa [Nat.add_assoc] using hi
      obtain ⟨j, hj, found⟩ := ih later (by omega) bound
      exact ⟨j + 1, by simpa using hj, found⟩

private theorem rowAt_append (before middle after : List Entry) (i : Nat) (within : i < middle.length) :
    rowAt (before ++ middle ++ after) (before.length + i) = middle[i] := by
  unfold rowAt
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by omega),
    Nat.add_sub_cancel_left, List.getElem?_eq_getElem within]
  rfl

theorem RowsAt.read_eq {groups : Array α} {before : List Entry} (placed : RowsAt refOf rowsOf before.length groups.toList)
    (allRows : rows = before ++ groups.toList.flatMap rowsOf ++ after)
    (inside : j < groups.size) (within : i < (rowsOf groups[j]).length) :
    rowAt rows ((refOf groups[j]).firstRow + i) = (rowsOf groups[j])[i] := by
  have idx : j < groups.toList.length := by simpa using inside
  obtain ⟨earlierRows, laterRows, cut, position, _, _⟩ := rowsAt_position placed j idx
  simp only [Array.getElem_toList] at cut position
  rw [allRows, cut, position]
  simpa only [List.append_assoc, List.length_append, Nat.add_assoc] using
    rowAt_append (before ++ earlierRows) (rowsOf groups[j]) (laterRows ++ after) i within

theorem RowsAt.refCovers {groups : Array α} {before : List Entry} (placed : RowsAt refOf rowsOf before.length groups.toList)
    (allRows : rows = before ++ groups.toList.flatMap rowsOf ++ after)
    (fences : ∀ i (hi : i < groups.size), (rowsOf groups[i]).getLast?.map Entry.key = some (refOf groups[i]).lastKey) :
    RefCovers rows before.length (groups.toList.flatMap rowsOf).length (groups.map refOf) := by
  constructor
  · rw [allRows]; simp
  · intro i hi
    have gi : i < groups.size := by simpa using hi
    have idx : i < groups.toList.length := by simpa using gi
    obtain ⟨earlierRows, laterRows, cut, position, count, positive⟩ := rowsAt_position placed i idx
    simp only [Array.getElem_toList] at cut position count positive
    have span : (refOf groups[i]).firstRow + (refOf groups[i]).count ≤
        before.length + (groups.toList.flatMap rowsOf).length := by
      rw [cut, List.length_append, List.length_append, position, count]
      omega
    have last : (rowsOf groups[i]).length - 1 < (rowsOf groups[i]).length := by omega
    have matching := placed.read_eq allRows gi last
    have fence := fences i gi
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem last] at fence
    have endEq : (refOf groups[i]).firstRow + (refOf groups[i]).count - 1 =
        (refOf groups[i]).firstRow + ((rowsOf groups[i]).length - 1) := by omega
    simp only [Array.getElem_map]
    exact ⟨by omega, by omega, span, by rw [endEq, matching]; exact (Option.some.inj fence).symm⟩
  · intro i j hi hj earlier
    have bound := rowsAt_separated placed i j
      (by simpa using hi) (by simpa using hj) earlier
    rw [Array.getElem_toList, Array.getElem_toList] at bound
    simpa only [Array.getElem_map] using bound
  · intro index lo hi
    obtain ⟨j, hj, found⟩ := rowsAt_covers placed index lo hi
    exact ⟨j, by simpa using hj, by simpa using found⟩

end ImmutableSSTable.Unified
