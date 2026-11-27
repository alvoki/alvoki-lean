import Alvoki.Experiments.SSTable.Proofs.UnifiedGroups
import Alvoki.Experiments.SSTable.Proofs.UnifiedReads

namespace ImmutableSSTable.Unified

private theorem LeafGroup.InImage.placed {leaf : LeafGroup} (inImage : leaf.InImage layout crc image) :
    RowsAt DataGroup.ref (fun group => group.rows.toList) leaf.ref.firstRow leaf.blocks.toList ∧
      leaf.rows.length = leaf.ref.count := by
  exact RowsAt.of_checked DataGroup.ref (fun group => group.rows.toList)
    inImage.refs inImage.bounds (fun group member => by
      simpa only [Array.length_toList] using (inImage.blocks group member).count_eq)

private theorem LeafGroup.InImage.fence {leaf : LeafGroup} (inImage : leaf.InImage layout crc image) :
    leaf.rows.getLast?.map Entry.key = some leaf.ref.lastKey := by
  have seen : leaf.blocks.toList.getLast?.map (fun g => g.ref.lastKey) =
      some leaf.ref.lastKey := by
    simpa only [← Array.getLast?_toList, Array.toList_map, List.getLast?_map,
      Option.map_map, Function.comp_def] using inImage.lastKey
  cases ends : leaf.blocks.toList.getLast? with
  | none => simp [ends] at seen
  | some group =>
    rw [ends] at seen
    obtain ⟨earlier, split⟩ := List.getLast?_eq_some_iff.mp ends
    have member : group ∈ leaf.blocks.toList := by rw [split]; simp
    have fence := (inImage.blocks group member).lastKey
    have tail : group.rows.toList.getLast?.map Entry.key = some group.ref.lastKey := by
      simpa only [Array.getLast?_toList] using fence
    unfold LeafGroup.rows
    rw [split, List.flatMap_append, List.flatMap_singleton, List.getLast?_append]
    cases last : group.rows.toList.getLast? with
    | none => simp [last] at tail
    | some row =>
      have same : group.ref.lastKey = leaf.ref.lastKey := Option.some.inj seen
      simpa [last, same] using tail

/-- Successful opening consumes the exact image produced by the writer, and
provides all packet observations for the actual returned handle. -/
theorem Image.open_observed [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {source : Source m} (built : Image crc layout rows image) (served : source.Serves image) :
    ∃ handle, openChecked source crc layout.tableId = pure handle ∧ handle.Observes rows := by
  obtain ⟨footer, groups, layoutEq, count, flatten, footerFits, footerAt, footerWithin, leafImages, root⟩ :=
    built.exists_layout
  subst layout
  obtain ⟨handle, opened, rowCount, rootEq, retained, checksumEq, layoutEq⟩ :=
    openChecked_image crc served built.extent footerFits count footerAt footerWithin root
  have sourceServes : handle.source.Serves image := retained ▸ served
  have valid : handle.layout.Valid := layoutEq ▸ footerFits.1
  have leafImage (leaf : LeafGroup) (member : leaf ∈ groups.toList) :
      leaf.InImage handle.layout handle.crc image := by
    rw [layoutEq, checksumEq]
    exact leafImages leaf member
  by_cases empty : rows = []
  · simp only [empty, List.isEmpty_nil, ite_true] at root
    have groupsEmpty : groups = #[] := Array.size_eq_zero_iff.mp (Array.isEmpty_iff_size_eq_zero.mp root.1)
    refine ⟨handle, opened, ⟨rowCount, ?_, ?_⟩⟩
    · rw [rootEq, groupsEmpty, empty]
      exact ⟨by simp, by simp, by simp, by simp⟩
    · intro parent member
      simp [rootEq, groupsEmpty] at member
  · have nonempty : rows.isEmpty = false := by cases rows <;> simp_all
    simp only [nonempty, Bool.false_eq_true, ite_false] at root
    obtain ⟨placed, _⟩ := RowsAt.of_checked LeafGroup.ref LeafGroup.rows root.1 root.2.1
      (fun leaf member => (leafImage leaf member).placed.2.symm)
    have faces (i : Nat) (inside : i < groups.size) :
        groups[i].rows.getLast?.map Entry.key = some groups[i].ref.lastKey :=
      (leafImage groups[i] (by simp)).fence
    have rootPartition := RowsAt.refCovers (before := []) placed
      (show rows = [] ++ groups.toList.flatMap LeafGroup.rows ++ [] by simpa using flatten.symm)
      faces
    refine ⟨handle, opened, ⟨rowCount, ?_, ?_⟩⟩
    · simpa only [flatten, rootEq, List.length_nil] using rootPartition
    · intro parent member
      rw [rootEq, Array.toList_map] at member
      obtain ⟨leaf, leafMember, rfl⟩ := List.mem_map.mp member
      obtain ⟨j, insideList, atIndex⟩ := List.mem_iff_getElem.mp leafMember
      have jWithin : j < groups.size := by simpa using insideList
      obtain ⟨before, after, split, starts, _, _⟩ := rowsAt_position placed j insideList
      rw [atIndex] at split starts
      have allRows : rows = before ++ leaf.blocks.toList.flatMap (fun g => g.rows.toList) ++ after :=
        flatten.symm.trans split
      let inImage := leafImage leaf leafMember
      obtain ⟨leafPlaced, leafLength⟩ := inImage.placed
      have leafPlaced' : RowsAt DataGroup.ref (fun g => g.rows.toList) before.length leaf.blocks.toList := by
        simpa [starts] using leafPlaced
      have leafFaces (i : Nat) (hi : i < leaf.blocks.size) :
          leaf.blocks[i].rows.toList.getLast?.map Entry.key = some leaf.blocks[i].ref.lastKey := by
        rw [Array.getLast?_toList]
        exact (inImage.blocks leaf.blocks[i] (by simp)).lastKey
      have leafPartition := RowsAt.refCovers leafPlaced' allRows leafFaces
      refine ⟨leaf.blocks.map DataGroup.ref, inImage.read sourceServes built.extent,
        ?_, ?_⟩
      · change RefCovers rows before.length leaf.rows.length (leaf.blocks.map DataGroup.ref) at leafPartition
        simpa only [starts, Nat.zero_add, leafLength] using leafPartition
      · intro ref member
        have refBound := inImage.refs.ref_valid member
        rw [Array.toList_map] at member
        obtain ⟨group, groupMember, rfl⟩ := List.mem_map.mp member
        let dataImage := inImage.blocks group groupMember
        have limit : group.rows.size ≤ maxFileSize := by
          have bound := refBound.2.2.2
          rw [dataImage.count_eq] at bound
          omega
        obtain ⟨data, readData, _, readRow⟩ := dataImage.read sourceServes built.extent valid limit
        refine ⟨data, readData, ?_⟩
        intro i hi
        have within : i < group.rows.size := by rwa [← dataImage.count_eq]
        obtain ⟨k, kList, rowGroup⟩ := List.mem_iff_getElem.mp groupMember
        have kWithin : k < leaf.blocks.size := by simpa using kList
        rw [Array.getElem_toList] at rowGroup
        have rowMatch := leafPlaced'.read_eq allRows kWithin
          (show i < leaf.blocks[k].rows.toList.length by simpa [rowGroup] using within)
        rw [Array.getElem_toList] at rowMatch
        have same : rowAt rows (group.ref.firstRow + i) = group.rows[i] := by
          simpa [rowGroup] using rowMatch
        rw [readRow i within, same]

/-- Open the produced image through the fast reader and expose its actual
operations under the existing byte-table contract. -/
theorem Image.open_represents [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {source : Source m} (imageFacts : Image crc layout rows image) (served : source.Serves image) :
    ∃ table, openTableChecked source crc layout.tableId = pure table ∧ table.Represents rows := by
  obtain ⟨handle, opened, observed⟩ := imageFacts.open_observed served
  refine ⟨handle.table, by simp [openTableChecked, opened], ?_⟩
  exact ⟨imageFacts.ordered, observed.count,
    fun key => handle.lookup_observed observed imageFacts.ordered key,
    fun key => handle.seek_observed observed imageFacts.ordered key,
    fun index => handle.next_observed observed index⟩

end ImmutableSSTable.Unified
