import Alvoki.Experiments.SSTable.UnifiedFormat
import Alvoki.Codec.ByteWords

namespace ImmutableSSTable.Unified

open Alvoki Alvoki.ByteWords

theorem appendEntry_eq (layout : Layout) (output : ByteArray) (row : Entry) :
    appendEntry layout output row = output ++ entryBytes layout row := by
  unfold appendEntry entryBytes
  unfold appendEntry
  split
  next => simp [ByteArray.append_assoc]
  next => simp only [ByteArray.append_assoc]
          rw [pushWordFast_append output, ByteArray.append_assoc]

@[simp] theorem entryBytes_size (layout : Layout) (row : Entry) :
    (entryBytes layout row).size = entrySize layout row := by
  unfold entryBytes appendEntry entrySize
  by_cases h : layout.keyLengthSize = 0 <;>
    simp [h, ByteArray.size_append, pushWordFast_size]
  have size : layout.keyLengthSize = 8 := by
    unfold Layout.keyLengthSize at *
    split at h <;> simp_all
  rw [size]

private def payload (layout : Layout) : List Entry → ByteArray
  | [] => ByteArray.empty
  | row :: rest => entryBytes layout row ++ payload layout rest

private def starts (layout : Layout) (start : Nat) : List Entry → List UInt64
  | [] => [start.toUInt64]
  | row :: rest => start.toUInt64 :: starts layout (start + entrySize layout row) rest

private def encodeDataSpec (layout : Layout) (rows : List Entry) : ByteArray :=
  payload layout rows ++
    if layout.hasOffsets then encodeWords (starts layout 0 rows) else ByteArray.empty

private def dataStep (layout : Layout) (state : ByteArray × ByteArray) (row : Entry) :
    ByteArray × ByteArray :=
  let (payload, offsets) := state
  let offsets :=
    if layout.hasOffsets then Alvoki.pushWordFast offsets payload.size.toUInt64 else offsets
  (appendEntry layout payload row, offsets)

private def finish (layout : Layout) (state : ByteArray × ByteArray) : ByteArray :=
  if layout.hasOffsets then state.1 ++ pushWordFast state.2 state.1.size.toUInt64 else state.1

private theorem fold_rows (layout : Layout) (rows : List Entry) (data offsets : ByteArray) :
    finish layout (rows.foldl (dataStep layout) (data, offsets)) =
      (data ++ payload layout rows) ++
        if layout.hasOffsets then offsets ++ encodeWords (starts layout data.size rows)
        else ByteArray.empty := by
  induction rows generalizing data offsets with
  | nil =>
    by_cases h : layout.hasOffsets = true <;>
      simp [finish, h, payload, starts, encodeWords, pushWordFast_append (bytes := offsets)]
  | cons row rest ih =>
    simp only [List.foldl_cons, dataStep, payload, starts]
    rw [ih, appendEntry_eq, ByteArray.size_append, entryBytes_size, ← ByteArray.append_assoc]
    split
    · simp only [encodeWords, pushWordFast_append (bytes := offsets), ByteArray.append_assoc]
    · simp

private theorem encodeData_eq (layout : Layout) (rows : Array Entry) :
    encodeData layout rows = encodeDataSpec layout rows.toList := by
  have stepEq :
      (fun row (s : ByteArray × ByteArray) =>
        if layout.hasOffsets then
          ForInStep.yield (appendEntry layout s.1 row, pushWordFast s.2 s.1.size.toUInt64)
        else ForInStep.yield (appendEntry layout s.1 row, s.2)) =
      (fun row s => ForInStep.yield (dataStep layout s row)) := by
    funext row s
    rcases s with ⟨payload, offsets⟩
    by_cases h : layout.hasOffsets = true <;> simp [dataStep, h]
  unfold encodeData
  dsimp only [Id.run, Bind.bind, Pure.pure]
  rw [stepEq, ← Array.forIn_toList]
  have folded : (forIn (m := Id) rows.toList (ByteArray.empty, ByteArray.empty) fun row s =>
      ForInStep.yield (dataStep layout s row)) =
      rows.toList.foldl (dataStep layout) (ByteArray.empty, ByteArray.empty) :=
    List.forIn_pure_yield_eq_foldl ..
  rw [folded]
  simpa [encodeDataSpec, finish] using fold_rows layout rows.toList ByteArray.empty ByteArray.empty

private theorem payload_size (layout : Layout) (rows : List Entry) :
    (payload layout rows).size = (rows.map (entrySize layout)).sum := by
  induction rows with
  | nil => simp [payload]
  | cons row rest ih => simp [payload, ih]

private theorem starts_length (layout : Layout) (start : Nat) (rows : List Entry) :
    (starts layout start rows).length = rows.length + 1 := by
  induction rows generalizing start with
  | nil => rfl
  | cons row rest ih => simp [starts, ih]

theorem encodeData_size (layout : Layout) (rows : Array Entry) :
    (encodeData layout rows).size = (rows.toList.map (entrySize layout)).sum +
      if layout.hasOffsets then 8 * (rows.size + 1) else 0 := by
  rw [encodeData_eq]
  by_cases h : layout.hasOffsets = true <;>
    simp [encodeDataSpec, h, payload_size, starts_length]

private def position (layout : Layout) (start : Nat) (rows : List Entry) (i : Nat) : Nat :=
  start + ((rows.take i).map (entrySize layout)).sum

@[simp] private theorem position_zero (layout : Layout) (start : Nat) (rows : List Entry) :
    position layout start rows 0 = start := by
  simp [position]

private theorem position_cons (layout : Layout) (start : Nat) (row : Entry)
    (rest : List Entry) (i : Nat) :
    position layout start (row :: rest) (i + 1) =
      position layout (start + entrySize layout row) rest i := by
  simp [position, Nat.add_assoc]

private theorem position_succ (layout : Layout) (start : Nat) (rows : List Entry)
    (within : i < rows.length) :
    position layout start rows (i + 1) = position layout start rows i + entrySize layout rows[i] := by
  induction rows generalizing start i with
  | nil => simp at within
  | cons row rest ih =>
    cases i with
    | zero => simp [position_cons]
    | succ i =>
      rw [position_cons, position_cons]
      exact ih _ (by simpa using within)

private theorem position_le_payload (layout : Layout) (start : Nat) (rows : List Entry) (i : Nat) :
    position layout start rows i ≤ start + (payload layout rows).size := by
  induction rows generalizing start i with
  | nil => simp [position, payload]
  | cons row rest ih =>
    cases i with
    | zero => simp
    | succ i =>
      rw [position_cons]
      simp only [payload, ByteArray.size_append, entryBytes_size, ← Nat.add_assoc]
      exact ih _ _

private theorem position_last (layout : Layout) (start : Nat) (rows : List Entry) :
    position layout start rows rows.length = start + (payload layout rows).size := by
  simp [position, payload_size]

private theorem starts_at (layout : Layout) (start : Nat) (rows : List Entry)
    (within : i ≤ rows.length) :
    (starts layout start rows)[i]'(by rw [starts_length]; omega) =
      (position layout start rows i).toUInt64 := by
  induction rows generalizing start i with
  | nil =>
    have : i = 0 := by simpa using within
    subst i
    simp [starts]
  | cons row rest ih =>
    cases i with
    | zero => simp [starts]
    | succ i =>
      rw [position_cons]
      exact ih _ (by simpa using within)

private theorem offset_word (layout : Layout) (rows : List Entry)
    (hasOffsets : layout.hasOffsets = true) (within : i ≤ rows.length) :
    word (encodeDataSpec layout rows) ((payload layout rows).size + 8 * i) =
      (position layout 0 rows i).toUInt64 := by
  simp only [encodeDataSpec, hasOffsets, ↓reduceIte]
  rw [word_right _ _ _ (by simp only [encodeWords_size, starts_length]; omega), word_encodeWords]
  exact starts_at layout 0 rows within

private theorem extract_append_left {a b : ByteArray} {i j : Nat} (within : j ≤ a.size) :
    (a ++ b).extract i j = a.extract i j := by
  rw [ByteArray.extract_append]
  have empty : b.extract (i - a.size) (j - a.size) = ByteArray.empty := by
    simp [Nat.sub_eq_zero_of_le within]
  rw [empty, ByteArray.append_empty]

private theorem payload_extract (layout : Layout) (rows : List Entry) (within : i < rows.length) :
    (payload layout rows).extract (position layout 0 rows i) (position layout 0 rows (i + 1)) =
      entryBytes layout rows[i] := by
  induction rows generalizing i with
  | nil => simp at within
  | cons row rest ih =>
    cases i with
    | zero =>
      rw [position_zero, position_cons, position_zero, Nat.zero_add, payload]
      exact ByteArray.extract_append_eq_left (entryBytes_size layout row).symm
    | succ i =>
      rw [payload, position_cons, position_cons, Nat.zero_add, ← entryBytes_size]
      simp only [position, Nat.zero_add] at ih ⊢
      rw [ByteArray.extract_append_size_add]
      exact ih (by simpa using within)

private theorem dataSpec_extract (layout : Layout) (rows : List Entry) (within : i < rows.length) :
    (encodeDataSpec layout rows).extract (position layout 0 rows i) (position layout 0 rows (i + 1)) =
      entryBytes layout rows[i] := by
  rw [encodeDataSpec, extract_append_left (by simpa using position_le_payload layout 0 rows (i + 1))]
  exact payload_extract layout rows within

private theorem word_toNat {n : Nat} (bound : n ≤ maxRowSize) : n.toUInt64.toNat = n :=
  UInt64.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt bound (by decide))

private theorem readRowInSpan_eq (layout : Layout) (row : Entry) (bytes : ByteArray) (start stop : Nat)
    (bounds : start ≤ stop ∧ stop ≤ bytes.size) (small : bytes.size ≤ maxRowSize)
    (fits : rowFits layout row = true)
    (slice : bytes.extract start stop = entryBytes layout row) :
    readRowInSpan layout bytes start stop = .ok row := by
  have spanSize : stop - start = entrySize layout row := by
    have size := congrArg ByteArray.size slice
    rwa [ByteArray.size_extract, Nat.min_eq_left bounds.2, entryBytes_size] at size
  have fields (i j : Nat) (hj : start + j ≤ stop) :
      (entryBytes layout row).extract i j = bytes.extract (start + i) (start + j) := by
    rw [← slice, ByteArray.extract_extract, Nat.min_eq_left hj]
  obtain ⟨kw, vw, id⟩ := layout
  have bound : row.key.size ≤ maxRowSize := by
    unfold entrySize at spanSize
    omega
  cases kw with
  | some k =>
    have keyWidth : k = row.key.size := by
      exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp fits).1
    have rowBytes : entryBytes ⟨some k, vw, id⟩ row = row.key ++ row.value := rfl
    have rowSize : entrySize ⟨some k, vw, id⟩ row = row.key.size + row.value.size := by
      simp [entrySize, Layout.keyLengthSize]
    have stopEq : stop = start + row.key.size + row.value.size := by omega
    have key : bytes.extract start (start + k) = row.key := by
      simpa only [Nat.add_zero] using
        ((fields 0 k (by omega)).symm.trans
          (by rw [rowBytes]; exact ByteArray.extract_append_eq_left keyWidth))
    have value : bytes.extract (start + k) stop = row.value := by
      rw [show stop = start + (row.key.size + row.value.size) by omega,
        ← fields k (row.key.size + row.value.size) (by omega), rowBytes]
      exact ByteArray.extract_append_eq_right keyWidth rfl
    simp [readRowInSpan, show k ≤ stop - start by omega, key, value, Pure.pure, Except.pure, Bind.bind, Except.bind]
  | none =>
    cases vw with
    | some v =>
      have valueWidth : v = row.value.size := by
        exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp fits).2
      have rowBytes : entryBytes ⟨none, some v, id⟩ row = row.key ++ row.value := rfl
      have rowSize : entrySize ⟨none, some v, id⟩ row = row.key.size + row.value.size := by
        simp [entrySize, Layout.keyLengthSize]
      have stopEq : stop = start + row.key.size + row.value.size := by omega
      have sep : stop - v = start + row.key.size := by omega
      have key : bytes.extract start (start + row.key.size) = row.key := by
        simpa only [Nat.add_zero] using
          ((fields 0 row.key.size (by omega)).symm.trans
            (by rw [rowBytes]; exact ByteArray.extract_append_eq_left rfl))
      have value : bytes.extract (start + row.key.size) stop = row.value := by
        rw [show stop = start + (row.key.size + row.value.size) by omega,
          ← fields row.key.size (row.key.size + row.value.size) (by omega), rowBytes]
        exact ByteArray.extract_append_eq_right rfl rfl
      simp [readRowInSpan, show v ≤ stop - start by omega, sep, key, value, Pure.pure, Except.pure, Bind.bind, Except.bind]
    | none =>
      have rowBytes : entryBytes ⟨none, none, id⟩ row =
          encodeOffset row.key.size ++ row.key ++ row.value := rfl
      have rowSize : entrySize ⟨none, none, id⟩ row = 8 + row.key.size + row.value.size := rfl
      have stopEq : stop = start + (8 + row.key.size + row.value.size) := by omega
      have lenSize : (encodeOffset row.key.size).size = 8 := pushWordFast_size _ _
      have lenWord : word bytes start = row.key.size.toUInt64 := by
        have extracted := word_extract bytes start stop 0 (by omega) bounds.2
        rw [slice, rowBytes, Nat.add_zero, word_left _ _ _ (by simp [lenSize]; omega),
          word_left _ _ _ (by rw [lenSize]; decide)] at extracted
        exact extracted.symm.trans (pushWordFast_roundtrip ByteArray.empty row.key.size.toUInt64)
      have key : bytes.extract (start + 8) (start + 8 + row.key.size) = row.key := by
        rw [Nat.add_assoc, ← fields 8 (8 + row.key.size) (by omega), rowBytes,
          extract_append_left (by simp [lenSize])]
        exact ByteArray.extract_append_eq_right lenSize.symm (by rw [lenSize])
      have value : bytes.extract (start + 8 + row.key.size) stop = row.value := by
        rw [Nat.add_assoc, stopEq, ← fields (8 + row.key.size) (8 + row.key.size + row.value.size)
          (by omega), rowBytes]
        exact ByteArray.extract_append_eq_right (by simp [lenSize]) (by simp [lenSize])
      simp [readRowInSpan, show start + 8 ≤ stop by omega, lenWord, word_toNat bound,
        show row.key.size ≤ stop - (start + 8) by omega, key, value, Pure.pure, Except.pure, Bind.bind, Except.bind]

private theorem fixed_entry_size (layout : Layout) (row : Entry)
    (fixed : layout.hasOffsets = false) (fits : rowFits layout row = true) :
    entrySize layout row = layout.keyWidth.getD 0 + layout.valueWidth.getD 0 := by
  cases layout with
  | mk keyWidth valueWidth tableId =>
    cases keyWidth <;> cases valueWidth <;> simp [Layout.hasOffsets] at fixed
    simp [rowFits] at fits
    simp [entrySize, Layout.keyLengthSize, fits.1, fits.2]

private theorem fixed_position (layout : Layout) (rows : List Entry) (start : Nat)
    (fixed : layout.hasOffsets = false) (fits : ∀ row ∈ rows, rowFits layout row = true)
    (within : i ≤ rows.length) :
    position layout start rows i = start + i * (layout.keyWidth.getD 0 + layout.valueWidth.getD 0) := by
  induction rows generalizing start i with
  | nil =>
    have : i = 0 := by simpa using within
    subst i
    simp
  | cons row rest ih =>
    cases i with
    | zero => simp
    | succ i =>
      have restFits : ∀ r ∈ rest, rowFits layout r = true := fun r h => fits r (List.mem_cons_of_mem _ h)
      rw [position_cons, ih _ restFits (by simpa using within),
        fixed_entry_size layout row fixed (fits row (by simp)), Nat.succ_mul]
      omega

/-- Reading an encoded data block returns its exact physical row count and
original rows for each valid cursor, for every supported width combination. -/
theorem openData_encodeData (layout : Layout) (rows : Array Entry)
    (valid : layout.Valid) (positive : 0 < rows.size) (countBound : rows.size ≤ maxFileSize)
    (sizeBound : (encodeData layout rows).size ≤ maxRowSize)
    (fits : ∀ i (hi : i < rows.size), rowFits layout rows[i] = true) :
    ∃ data, openData layout rows.size (encodeData layout rows) = .ok data ∧
      data.count = rows.size ∧ ∀ i (hi : i < rows.size), data.readRow i = .ok rows[i] := by
  rw [encodeData_eq] at sizeBound ⊢
  let bytes := encodeDataSpec layout rows.toList
  let dataSize := (payload layout rows.toList).size
  let pos := position layout 0 rows.toList
  have sizeEq : bytes.size = dataSize +
      if layout.hasOffsets then 8 * (rows.size + 1) else 0 := by
    by_cases h : layout.hasOffsets = true <;>
      simp [bytes, dataSize, encodeDataSpec, h, starts_length]
  have dataWithin : dataSize ≤ bytes.size := by omega
  have posWithin (i : Nat) : pos i ≤ dataSize := by
    simpa [pos, dataSize] using position_le_payload layout 0 rows.toList i
  have posOrder (i : Nat) (hi : i < rows.size) : pos i ≤ pos (i + 1) := by
    have within : i < rows.toList.length := by simpa using hi
    unfold pos
    rw [position_succ layout 0 rows.toList within]
    omega
  have posLast : pos rows.size = dataSize := by
    simpa [pos, dataSize] using position_last layout 0 rows.toList
  have read (i : Nat) (hi : i < rows.size) :
      readRowInSpan layout bytes (pos i) (pos (i + 1)) = .ok rows[i] := by
    apply readRowInSpan_eq _ _ _ _ _
      ⟨posOrder i hi, Nat.le_trans (posWithin (i + 1)) dataWithin⟩ sizeBound (fits i hi)
    simpa [bytes, pos] using dataSpec_extract layout rows.toList (show i < rows.toList.length by simpa using hi)
  have admitted : layout.Valid ∧ 0 < rows.size ∧ rows.size ≤ maxFileSize ∧
      bytes.size ≤ maxRowSize := ⟨valid, positive, countBound, sizeBound⟩
  change ∃ data, openData layout rows.size bytes = .ok data ∧
    data.count = rows.size ∧ ∀ i (hi : i < rows.size), data.readRow i = .ok rows[i]
  unfold openData
  simp only [ite_eq_left admitted]
  cases hasOffsets : layout.hasOffsets with
  | false =>
    have allFit (row : Entry) (hr : row ∈ rows.toList) : rowFits layout row = true := by
      obtain ⟨i, hi, eq⟩ := List.mem_iff_getElem.mp hr
      rw [← eq, Array.getElem_toList]
      exact fits i (by simpa using hi)
    have posFixed (i : Nat) (hi : i ≤ rows.size) :
        pos i = i * (layout.keyWidth.getD 0 + layout.valueWidth.getD 0) := by
      simpa [pos] using fixed_position layout rows.toList 0 hasOffsets allFit (by simpa using hi : i ≤ rows.toList.length)
    have sizeFixed : bytes.size = rows.size * (layout.keyWidth.getD 0 + layout.valueWidth.getD 0) := by
      simp only [hasOffsets, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at sizeEq
      rw [sizeEq, ← posLast, posFixed _ (by omega)]
    simp only [Bool.false_eq_true, ↓reduceIte, sizeFixed]
    simp only [Pure.pure, Except.pure, Except.ok.injEq, exists_eq_left']
    refine ⟨trivial, ?_⟩
    intro i hi
    simpa [Data.readRow, Data.rowSpan, hi, hasOffsets, Pure.pure, Except.pure, Bind.bind,
      Except.bind, posFixed i (by omega), posFixed (i + 1) (by omega)] using read i hi
  | true =>
    simp only [hasOffsets, ↓reduceIte] at sizeEq
    have offsetBound : 8 * (rows.size + 1) ≤ bytes.size := by omega
    have dataEq : bytes.size - 8 * (rows.size + 1) = dataSize := by omega
    have offsetWord (i : Nat) (hi : i ≤ rows.size) :
        word bytes (dataSize + 8 * i) = (pos i).toUInt64 := by
      simpa [bytes, dataSize, pos] using offset_word layout rows.toList hasOffsets
        (show i ≤ rows.toList.length by simpa using hi)
    have first : word bytes dataSize = 0 := by simpa [pos] using offsetWord 0 (by omega)
    have last : (word bytes (bytes.size - 8)).toNat = dataSize := by
      rw [show bytes.size - 8 = dataSize + 8 * rows.size by omega, offsetWord rows.size (by omega),
        posLast, word_toNat (Nat.le_trans dataWithin sizeBound)]
    simp only [↓reduceIte, offsetBound, dataEq, first, last, and_self]
    simp only [Pure.pure, Except.pure, Except.ok.injEq, exists_eq_left']
    refine ⟨trivial, ?_⟩
    intro i hi
    have startEq : (word bytes (dataSize + 8 * i)).toNat = pos i := by
      rw [offsetWord i (by omega), word_toNat (Nat.le_trans (posWithin i) (Nat.le_trans dataWithin sizeBound))]
    have endEq : (word bytes (dataSize + 8 * i + 8)).toNat = pos (i + 1) := by
      rw [show dataSize + 8 * i + 8 = dataSize + 8 * (i + 1) by omega,
        offsetWord (i + 1) (by omega),
        word_toNat (Nat.le_trans (posWithin (i + 1)) (Nat.le_trans dataWithin sizeBound))]
    simp only [Data.readRow, Data.rowSpan, hi, ↓reduceIte, hasOffsets, startEq, endEq,
      posOrder i hi, posWithin (i + 1), and_self, Pure.pure, Except.pure, Bind.bind, Except.bind]
    exact read i hi

end ImmutableSSTable.Unified
