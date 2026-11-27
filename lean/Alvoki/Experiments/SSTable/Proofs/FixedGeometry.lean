import Alvoki.Experiments.SSTable.Proofs.FixedBuilder
import Alvoki.Experiments.SSTable.Proofs.FixedFormat

namespace ImmutableSSTable.Fixed

private theorem length_flatten (full : List (List Entry))
    (groups : ∀ group ∈ full, group.length = width) :
    full.flatten.length = full.length * width := by
  induction full with
  | nil => simp
  | cons group rest ih =>
    simp [groups group (by simp), ih (fun g hg => groups g (by simp [hg])),
      Nat.succ_mul, Nat.add_comm]

private theorem size_blocks (layout : Layout) (first : Nat) (full : List (List Entry))
    (groups : ∀ group ∈ full, group.length = layout.rowsPerBlock)
    (fits : ∀ row ∈ full.flatten, layout.RowFits row) :
    (encodeBlocks layout first full).size = full.length * layout.blockSize := by
  induction full generalizing first with
  | nil => simp [encodeBlocks]
  | cons group rest ih =>
    have groupFits : ∀ row ∈ group, layout.RowFits row := fun row h => fits row (by simp [h])
    have restFits : ∀ row ∈ rest.flatten, layout.RowFits row := fun row h => fits row (by simp [h])
    simp only [encodeBlocks, ByteArray.size_append, encodeBlock_size, encodePayload_size group groupFits,
      groups group (by simp), ih _ (fun g hg => groups g (by simp [hg])) restFits,
      List.length_cons, Nat.succ_mul, Layout.blockSize]
    omega

private theorem size_last (layout : Layout) (block : Nat) (tail : List Entry)
    (fits : ∀ row ∈ tail, layout.RowFits row) :
    (encodeLast layout block tail).size =
      tail.length * layout.rowWidth + (if tail.length = 0 then 0 else 8) := by
  cases tail with
  | nil => simp [encodeLast]
  | cons row rest =>
    have n : (row :: rest).isEmpty = false := rfl
    simp only [encodeLast, n, Bool.false_eq_true, ite_false, encodeBlock_size,
      encodePayload_size _ fits, List.length_cons, Nat.add_one_ne_zero]

theorem encodeImage_extent (layout : Layout) (full : List (List Entry)) (tail : List Entry)
    (valid : layout.Valid) (groups : ∀ group ∈ full, group.length = layout.rowsPerBlock)
    (short : tail.length < layout.rowsPerBlock)
    (fits : ∀ row ∈ full.flatten ++ tail, layout.RowFits row) :
    (encodeImage layout full tail).size = layout.fileSize (full.flatten ++ tail).length := by
  have fullFits : ∀ row ∈ full.flatten, layout.RowFits row := fun row h => fits row (by simp [h])
  have tailFits : ∀ row ∈ tail, layout.RowFits row := fun row h => fits row (by simp [h])
  have count : (full.flatten ++ tail).length = layout.rowsPerBlock * full.length + tail.length := by
    simp [length_flatten full groups, Nat.mul_comm]
  have quotient : (full.flatten ++ tail).length / layout.rowsPerBlock = full.length := by
    rw [count, Nat.mul_add_div valid.1, Nat.div_eq_of_lt short, Nat.add_zero]
  have remainder : (full.flatten ++ tail).length % layout.rowsPerBlock = tail.length := by
    rw [count, Nat.mul_add_mod, Nat.mod_eq_of_lt short]
  simp only [encodeImage, ByteArray.size_append, encodeFooter_size, size_blocks layout 0 full groups fullFits,
    size_last layout full.length tail tailFits, Layout.fileSize, Layout.dataSize, Layout.blockCount,
    quotient, remainder]
  rw [count]
  simp only [Layout.blockSize, Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  split <;> simp_all <;> omega

theorem encodeImage_footer (layout : Layout) (full : List (List Entry)) (tail : List Entry) :
    let image := encodeImage layout full tail
    image.extract (image.size - footerSize) image.size =
      encodeFooter layout (full.flatten ++ tail).length := by
  dsimp only [encodeImage]
  apply ByteArray.extract_append_eq_right <;> simp

private theorem block_slice (layout : Layout) (first : Nat) (full : List (List Entry))
    (tail : List Entry) (suffix : ByteArray)
    (valid : layout.Valid) (groups : ∀ group ∈ full, group.length = layout.rowsPerBlock)
    (short : tail.length < layout.rowsPerBlock)
    (fits : ∀ row ∈ full.flatten ++ tail, layout.RowFits row)
    (i : Nat) (within : i < (full.flatten ++ tail).length) :
    let rows := full.flatten ++ tail
    let bytes := encodeBlocks layout first full ++ encodeLast layout (first + full.length) tail ++ suffix
    let block := i / layout.rowsPerBlock
    let localIndex := i % layout.rowsPerBlock
    let blockRows := layout.blockRows rows.length block
    let start := layout.blockOffset block
    let stop := start + layout.blockReadSize rows.length block
    ∃ payload, 0 < blockRows ∧ payload.size = blockRows * layout.rowWidth ∧
      stop ≤ bytes.size ∧ bytes.extract start stop = encodeBlock layout (first + block) payload ∧
      readRow layout payload localIndex = rows[i] := by
  induction full generalizing first i with
  | nil =>
    have iTail : i < tail.length := by simpa using within
    have iShort := Nat.lt_trans iTail short
    have div := Nat.div_eq_of_lt iShort
    have mod := Nat.mod_eq_of_lt iShort
    have positive : 0 < tail.length := by omega
    have nonempty : tail.isEmpty = false := by cases tail <;> simp_all
    have tailFits : ∀ row ∈ tail, layout.RowFits row := fun row h => fits row (by simp [h])
    have size := encodePayload_size tail tailFits
    simp only [List.flatten_nil, List.nil_append, List.length_nil, Nat.add_zero,
      encodeBlocks, ByteArray.empty_append, div, mod, encodeLast, nonempty, Bool.false_eq_true, ite_false,
      Layout.blockRows, Nat.zero_mul, Nat.sub_zero, Nat.min_eq_right (Nat.le_of_lt short),
      Layout.blockOffset, Layout.blockReadSize]
    refine ⟨encodePayload tail, positive, size, ?_, ?_, readRow_encodePayload tail tailFits iTail⟩
    · simp [size]
    · exact ByteArray.extract_append_eq_left (by simp [size])
  | cons group rest ih =>
    have width := groups group (by simp)
    have groupFits : ∀ row ∈ group, layout.RowFits row := fun row h => fits row (by simp [h])
    have otherGroups : ∀ group ∈ rest, group.length = layout.rowsPerBlock :=
      fun g h => groups g (by simp [h])
    have otherFits : ∀ row ∈ rest.flatten ++ tail, layout.RowFits row :=
      fun row h => fits row (by simpa [List.append_assoc] using List.mem_append_right group h)
    have extent : ((group :: rest).flatten ++ tail).length =
        layout.rowsPerBlock + (rest.flatten ++ tail).length := by simp [width, List.append_assoc]
    have fullSize : (encodeBlock layout first (encodePayload group)).size = layout.blockSize := by
      simp [encodePayload_size group groupFits, width, Layout.blockSize]
    have image : encodeBlocks layout first (group :: rest) ++
        encodeLast layout (first + (group :: rest).length) tail ++ suffix =
          encodeBlock layout first (encodePayload group) ++
            (encodeBlocks layout (first + 1) rest ++
              encodeLast layout (first + 1 + rest.length) tail ++ suffix) := by
      simp only [encodeBlocks, List.length_cons, ByteArray.append_assoc]
      congr 4 <;> omega
    by_cases early : i < layout.rowsPerBlock
    · have div := Nat.div_eq_of_lt early
      have mod := Nat.mod_eq_of_lt early
      have rowsInBlock : layout.blockRows ((group :: rest).flatten ++ tail).length 0 =
          layout.rowsPerBlock  := by
        rw [Layout.blockRows, extent, Nat.zero_mul, Nat.sub_zero, Nat.min_eq_left]
        omega
      have rowEq : readRow layout (encodePayload group) i = ((group :: rest).flatten ++ tail)[i] := by
        have w : i < group.length := width ▸ early
        rw [readRow_encodePayload group groupFits w]
        symm
        simpa [List.append_assoc] using
          (List.getElem_append_left (as := group) (bs := rest.flatten ++ tail) w)
      simp only [div, mod, image, rowsInBlock, Layout.blockOffset, Layout.blockReadSize,
        Nat.zero_mul, Nat.zero_add, Nat.add_zero]
      refine ⟨encodePayload group, valid.1, by simp [encodePayload_size group groupFits, width], ?_, ?_, rowEq⟩
      · rw [ByteArray.size_append, fullSize, Layout.blockSize]
        omega
      · exact ByteArray.extract_append_eq_left (by rw [fullSize, Layout.blockSize])
    · have shift : i = layout.rowsPerBlock + (i - layout.rowsPerBlock) := by omega
      have div : i / layout.rowsPerBlock = 1 + (i - layout.rowsPerBlock) / layout.rowsPerBlock := by
        have eq : i = layout.rowsPerBlock * 1 + (i - layout.rowsPerBlock) := by simpa using shift
        exact (congrArg (· / layout.rowsPerBlock) eq).trans (Nat.mul_add_div valid.1 _ _)
      have mod : i % layout.rowsPerBlock = (i - layout.rowsPerBlock) % layout.rowsPerBlock := by
        have eq : i = layout.rowsPerBlock * 1 + (i - layout.rowsPerBlock) := by simpa using shift
        exact (congrArg (· % layout.rowsPerBlock) eq).trans (Nat.mul_add_mod _ _ _)
      let j := i - layout.rowsPerBlock
      let block := j / layout.rowsPerBlock
      have jWithin : j < (rest.flatten ++ tail).length := by dsimp [j]; omega
      obtain ⟨payload, positive, size, fitsSlice, slice, row⟩ :=
        ih (first + 1) otherGroups otherFits j jWithin
      have countEq : layout.blockRows ((group :: rest).flatten ++ tail).length (1 + block) =
          layout.blockRows (rest.flatten ++ tail).length block := by
        rw [Layout.blockRows, Layout.blockRows, extent, Nat.add_mul, Nat.one_mul,
          Nat.add_sub_add_left]
      have startEq : layout.blockOffset (1 + block) =
          (encodeBlock layout first (encodePayload group)).size + layout.blockOffset block := by
        rw [fullSize]; simp [Layout.blockOffset, Nat.add_mul]
      have readSize : layout.blockReadSize ((group :: rest).flatten ++ tail).length (1 + block) =
          layout.blockReadSize (rest.flatten ++ tail).length block := by
        unfold Layout.blockReadSize
        rw [countEq]
      have div' : i / layout.rowsPerBlock = 1 + block := div
      have mod' : i % layout.rowsPerBlock = j % layout.rowsPerBlock := mod
      simp only [div', mod', image, countEq, startEq, readSize]
      refine ⟨payload, positive, size, ?_, ?_, ?_⟩
      · rw [ByteArray.size_append, Nat.add_assoc]
        exact Nat.add_le_add_left fitsSlice _
      · rw [Nat.add_assoc (encodeBlock layout first (encodePayload group)).size,
          ByteArray.extract_append_size_add]
        simpa only [Nat.add_assoc] using slice
      · rw [row]
        symm
        simpa [List.append_assoc, width, j] using
          (List.getElem_append_right (as := group) (bs := rest.flatten ++ tail)
            (show group.length ≤ i by omega))

theorem encodeImage_row_block (layout : Layout) (full : List (List Entry)) (tail : List Entry)
    (valid : layout.Valid) (groups : ∀ group ∈ full, group.length = layout.rowsPerBlock)
    (short : tail.length < layout.rowsPerBlock)
    (fits : ∀ row ∈ full.flatten ++ tail, layout.RowFits row)
    (i : Nat) (within : i < (full.flatten ++ tail).length) :
    let rows := full.flatten ++ tail
    let image := encodeImage layout full tail
    let block := i / layout.rowsPerBlock
    let blockRows := layout.blockRows rows.length block
    let start := layout.blockOffset block
    let stop := start + layout.blockReadSize rows.length block
    ∃ payload, 0 < blockRows ∧ payload.size = blockRows * layout.rowWidth ∧
      stop ≤ image.size ∧ image.extract start stop = encodeBlock layout block payload ∧
      readRow layout payload (i % layout.rowsPerBlock) = rows[i] := by
  simpa only [Nat.zero_add, encodeImage] using
    block_slice layout 0 full tail (encodeFooter layout (full.flatten ++ tail).length)
      valid groups short fits i within

end ImmutableSSTable.Fixed
