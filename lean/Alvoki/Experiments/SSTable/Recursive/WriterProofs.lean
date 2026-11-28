import Alvoki.Experiments.SSTable.Recursive.WriterPages
import Alvoki.Experiments.SSTable.Proofs.UnifiedBuilder

namespace ImmutableSSTable.Recursive

open Unified (Layout Checksum Ref ModelM ModelFile modelSink modelNext encodeData encodeIndex
  encodePacket encodePacket_size checksumSize indexEntrySize)

def modelBuild (crc : Checksum) (layout : Layout) (rows : List Entry)
    (options : BuildOptions := {}) : Except String (Nat × ByteArray) := do
  let (count, file) ← (buildStream crc layout modelSink modelNext id options).run { rows }
  return (count, file.bytes)

private def modelWriter (crc : Checksum) (layout : Layout) (options : BuildOptions) :
    Writer ModelM String := ⟨crc, layout, modelSink, id, options⟩

private theorem bind_ok {a : ModelM α} {b : α → ModelM β}
    {file out : ModelFile} {result : β}
    (run : (a >>= b).run file = .ok (result, out)) :
    ∃ value mid, a.run file = .ok (value, mid) ∧ (b value).run mid = .ok (result, out) := by
  change (a.run file).bind _ = _ at run
  cases step : a.run file with
  | error error => rw [step] at run; cases run
  | ok value =>
    obtain ⟨value, mid⟩ := value
    rw [step] at run
    exact ⟨value, mid, rfl, run⟩

private theorem pure_ok {value result : α} {file out : ModelFile}
    (run : (pure value : ModelM α).run file = .ok (result, out)) :
    result = value ∧ out = file := by
  change Except.ok (value, file) = .ok (result, out) at run
  cases run
  exact ⟨rfl, rfl⟩

private theorem ordered_take_prefix {rows : List Entry} {m n : Nat} (ordered : Ordered (rows.take n)) (le : m ≤ n) :
    Ordered (rows.take m) :=
  ordered.sublist (List.take_sublist_take_left le)

private theorem append_atEnd (base : ByteArray) (crc : Checksum) (tableId kind : UInt64)
    (body : ByteArray) :
    (base ++ encodePacket crc tableId kind base.size body).extract
      base.size (base.size + (body.size + checksumSize)) =
      encodePacket crc tableId kind base.size body :=
  ByteArray.extract_append_eq_right rfl (by rw [encodePacket_size])

private theorem writePacket_ok {layout : Layout} {crc : Checksum} {options : BuildOptions}
    {file out : ModelFile} {kind : UInt64} {limit stop : Nat} {body : ByteArray}
    (run : ((modelWriter crc layout options).writePacket kind limit file.bytes.size body).run file =
      .ok (stop, out)) :
    out = { file with bytes := file.bytes ++ encodePacket crc layout.tableId kind file.bytes.size body } ∧
    stop = out.bytes.size ∧ body.size + checksumSize ≤ limit ∧ stop + footerPacketSize ≤ maxFileSize := by
  by_cases packet : body.size + checksumSize ≤ limit
  · by_cases extent : file.bytes.size + (body.size + checksumSize) + footerPacketSize ≤ maxFileSize
    · simp only [Writer.writePacket, packet, extent, ↓reduceIte] at run
      change Except.ok (file.bytes.size + (body.size + checksumSize), { file with
        bytes := file.bytes ++ encodePacket crc layout.tableId kind file.bytes.size body }) =
          .ok (stop, out) at run
      cases run
      exact ⟨rfl, by simp, packet, extent⟩
    · simp only [Writer.writePacket, packet, extent, ↓reduceIte] at run
      change Except.error "SSTable file exceeds signed offset limit" = .ok (stop, out) at run
      cases run
  · simp only [Writer.writePacket, packet, ↓reduceIte] at run
    change Except.error "SSTable packet exceeds size limit" = .ok (stop, out) at run
    cases run

private structure Appended (file out : ModelFile) (offset : Nat) : Prop where
  remaining : out.rows = file.rows
  position : offset = out.bytes.size
  extended : ∃ suffix, out.bytes = file.bytes ++ suffix
  room : offset + footerPacketSize ≤ maxFileSize

private theorem Appended.same (file : ModelFile) (room : file.bytes.size + footerPacketSize ≤ maxFileSize) :
    Appended file file file.bytes.size := ⟨rfl, rfl, .intro .empty (by simp), room⟩

private theorem Appended.trans (a : Appended file middle mid) (b : Appended middle out stop) :
    Appended file out stop := by
  refine ⟨b.remaining.trans a.remaining, b.position, ?_, b.room⟩
  obtain ⟨first, h₁⟩ := a.extended
  obtain ⟨second, h₂⟩ := b.extended
  exact ⟨first ++ second, by rw [h₂, h₁, ByteArray.append_assoc]⟩

private theorem writePage_ok {layout : Layout} {crc : Checksum} {options : BuildOptions}
    {file out : ModelFile} {ref : Ref}
    (pageOK : PendingPage layout crc file.bytes rows previous childHeight first stop page)
    (previousWithin : previous ≤ file.bytes.size) (rowLimit : stop ≤ maxFileSize)
    (run : ((modelWriter crc layout options).writePage (childHeight + 1) file.bytes.size page).run file =
      .ok ((ref, next), out)) :
    Appended file out next ∧ ref.offset = file.bytes.size ∧ ref.offset + ref.size = next ∧
    ref.firstRow = first ∧ ref.count = stop - first ∧
    WrittenChild layout crc out.bytes rows out.bytes.size (childHeight + 1) ref := by
  cases firstEq : page.refs[0]? with
  | none =>
    simp only [Writer.writePage, firstEq] at run
    cases run
  | some head =>
    cases lastEq : page.refs.back? with
    | none =>
      simp only [Writer.writePage, firstEq, lastEq] at run
      cases run
    | some last =>
      simp only [Writer.writePage, firstEq, lastEq] at run
      obtain ⟨written, mid, writeRan, pureRan⟩ := bind_ok run
      obtain ⟨ret, outEq⟩ := pure_ok pureRan
      injection ret with refEq nextEq
      subst ref next out
      obtain ⟨outEq, pos, limit, space⟩ := writePacket_ok writeRan
      have headStart := pageOK.start head firstEq
      have lastStop := pageOK.finish last lastEq
      have start := pageOK.first_le
      have covered := pageOK.coverage.extent
      have rowEnd : stop ≤ rows.length := by omega
      have lastChild := pageOK.children last (array_back_mem lastEq)
      have lastPositive := lastChild.valid.2.2.1
      have span : first < stop := by
        have headSpan := pageOK.coverage.span 0 pageOK.nonempty
        have eq : page.refs[0]'pageOK.nonempty = head := by simpa [Array.getElem?_eq_getElem pageOK.nonempty] using firstEq
        rw [eq] at headSpan
        have := headSpan.1
        have := headSpan.2.2.1
        omega
      subst mid
      simp only [ByteArray.size_append, encodePacket_size] at pos
      let payload := encodePacket crc layout.tableId (indexKind (childHeight + 1)) file.bytes.size
        (encodeIndex page.refs)
      have sizeEq : written - file.bytes.size = (encodeIndex page.refs).size + checksumSize := by omega
      have ends : file.bytes.size + (written - file.bytes.size) = written := by omega
      have positivePacket : 0 < (encodeIndex page.refs).size + checksumSize := by
        have : 0 < checksumSize := by decide
        omega
      refine ⟨⟨rfl, by simpa using pos, ⟨payload, rfl⟩, space⟩, rfl, ends,
        headStart, by dsimp; omega, ?_⟩
      refine ⟨?_, ⟨by dsimp; omega, by dsimp; omega, by dsimp; omega, by dsimp; omega⟩,
        by simpa [ends] using Nat.le_of_eq pos, by dsimp; omega, ?_, lastChild.keyFits⟩
      · refine ⟨page.refs, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
        · refine ⟨pageOK.pageValid, ?_, Nat.le_refl _, sizeEq, ?_⟩
          · change file.bytes.size + (written - file.bytes.size) ≤ (file.bytes ++ payload).size
            rw [ends, ByteArray.size_append, encodePacket_size]
            exact Nat.le_of_eq pos
          · change (file.bytes ++ payload).extract file.bytes.size
              (file.bytes.size + (written - file.bytes.size)) = payload
            rw [sizeEq]
            exact append_atEnd _ _ _ _ _
        · simpa [headStart, lastStop] using pageOK.coverage
        · have disk := lastChild.ends
          have spanEq : head.firstRow + (last.firstRow + last.count - head.firstRow) =
            last.firstRow + last.count := by omega
          simp [Unified.checkChildren, firstEq, lastEq, spanEq, Nat.le_trans disk previousWithin,
            Pure.pure, Except.pure]
        · intro _
          simp [lastEq]
        · intro child member
          exact (pageOK.children child member).tree.extend payload previousWithin (by simp)
      · change last.lastKey = (rowAt rows (head.firstRow +
          (last.firstRow + last.count - head.firstRow) - 1)).key
        have eq : head.firstRow + (last.firstRow + last.count - head.firstRow) =
            last.firstRow + last.count := by omega
        rw [eq]
        exact lastChild.fence

private theorem push_ok {layout : Layout} {crc : Checksum} {options : BuildOptions}
    {file out : ModelFile} {ref : Ref}
    (pagesOK : PendingPages layout crc file.bytes rows previous h stop pages)
    (newChild : WrittenChild layout crc file.bytes rows file.bytes.size h ref)
    (previousBefore : previous ≤ ref.offset) (starts : ref.firstRow = stop)
    (ordered : Ordered (rows.take (stop + ref.count))) (target : options.indexTarget ≤ maxRowSize)
    (room : file.bytes.size + footerPacketSize ≤ maxFileSize)
    (run : ((modelWriter crc layout options).push (h + 1) file.bytes.size ref pages fuel).run file =
      .ok ((next, pending), out)) :
    Appended file out next ∧
    PendingPages layout crc out.bytes rows out.bytes.size h (stop + ref.count) pending := by
  induction fuel generalizing file out ref previous h stop pages next pending with
  | zero =>
    simp only [Writer.push] at run
    cases run
  | succ fuel ih =>
    have previousWithin : previous ≤ file.bytes.size := by have := newChild.ends; omega
    cases pagesOK with
    | nil =>
      simp only [Writer.push] at run
      obtain ⟨eq, rfl⟩ := pure_ok run
      cases eq
      exact ⟨Appended.same _ room, .cons .nil (by simpa [starts] using PendingPage.singleton newChild)⟩
    | cons upper current =>
      simp only [Writer.push] at run
      split at run
      · obtain ⟨⟨promoted, written⟩, mid, pageRan, rest⟩ := bind_ok run
        obtain ⟨put, atEnd, endEq, firstEq, countEq, promotedChild⟩ :=
          writePage_ok current previousWithin (by have := newChild.valid.2.2.2; omega) pageRan
        obtain ⟨⟨finished, upperPages⟩, last, recRan, done⟩ := bind_ok rest
        obtain ⟨eq, rfl⟩ := pure_ok done
        cases eq
        obtain ⟨packet, disk⟩ := put.extended
        have lifted := upper.extend packet (Nat.le_refl _) (by simp; omega)
        rw [← disk] at lifted
        rw [put.position] at recRan
        have start := current.first_le
        have upperOrdered := ordered_take_prefix ordered
          (show promoted.firstRow + promoted.count ≤ stop + ref.count by omega)
        rw [firstEq] at upperOrdered
        obtain ⟨raised, result⟩ := ih lifted promotedChild (by omega) firstEq upperOrdered
          (by simpa [put.position] using put.room) recRan
        have appended := put.trans raised
        obtain ⟨all, exactBytes⟩ := appended.extended
        have kept := newChild.extend all (show file.bytes.size ≤ (file.bytes ++ all).size by simp)
          (Nat.le_refl _)
        rw [← exactBytes] at kept
        have bound : promoted.firstRow + promoted.count = stop := by omega
        rw [firstEq] at bound
        rw [bound] at result
        exact ⟨appended, .cons result (by simpa only [starts] using PendingPage.singleton kept)⟩
      · obtain ⟨eq, rfl⟩ := pure_ok run
        cases eq
        have higher := upper.extend .empty previousWithin (by simp)
        simp only [ByteArray.append_empty] at higher
        exact ⟨Appended.same _ room, .cons higher
          (current.add newChild previousBefore previousWithin (Nat.le_refl _) starts target
            (Bool.eq_false_of_ne_true (by assumption)) ordered)⟩


private theorem PendingPages.zero_start (p : PendingPages layout crc bytes rows endAt h stop []) :
    stop = 0 := by cases p; rfl

private theorem ordered_append {rows : List Entry} {row : Entry} (ordered : Ordered rows)
    (last : ∀ old ∈ rows.getLast?, old.key < row.key) : Ordered (rows ++ [row]) := by
  apply List.pairwise_append.mpr
  refine ⟨ordered, by simp, ?_⟩
  intro entry member tail one
  have same : tail = row := by simpa using one
  subst tail
  cases back : rows.getLast? with
  | none => simp [List.getLast?_eq_none_iff.mp back] at member
  | some old =>
    have next := last old back
    obtain ⟨earlier, eq⟩ := List.getLast?_eq_some_iff.mp back
    rw [eq, List.mem_append, List.mem_singleton] at member
    rcases member with first | rfl
    · rw [eq] at ordered
      exact Std.lt_trans ((List.pairwise_append.mp ordered).2.2 entry first old (by simp)) next
    · exact next

private theorem finishPages_ok {layout : Layout} {crc : Checksum} {options : BuildOptions}
    {file out : ModelFile} {rootHeight rootOffset rootSize : Nat}
    (pagesOK : PendingPages layout crc file.bytes rows file.bytes.size h stop pages)
    (ordered : Ordered (rows.take stop)) (rowLimit : stop ≤ maxFileSize)
    (target : options.indexTarget ≤ maxRowSize) (cap : h + fuel ≤ maxHeight)
    (room : file.bytes.size + footerPacketSize ≤ maxFileSize)
    (run : ((modelWriter crc layout options).finishPages (h + 1) file.bytes.size pages fuel).run file =
      .ok ((rootHeight, rootOffset, rootSize), out)) :
    Appended file out out.bytes.size ∧ rootHeight ≤ maxHeight ∧
    (if stop = 0 then rootHeight = 0 ∧ rootOffset = 0 ∧ rootSize = 0 ∧ out = file
    else 0 < rootHeight ∧ ∃ ref, ref.offset = rootOffset ∧ ref.size = rootSize ∧
      ref.firstRow = 0 ∧ ref.count = stop ∧ ref.offset + ref.size = out.bytes.size ∧
      WrittenChild layout crc out.bytes rows out.bytes.size rootHeight ref) := by
  induction fuel generalizing file out h stop pages rootHeight rootOffset rootSize with
  | zero =>
    simp only [Writer.finishPages] at run
    cases run
  | succ fuel ih =>
    cases pagesOK with
    | nil =>
      simp only [Writer.finishPages] at run
      obtain ⟨eq, rfl⟩ := pure_ok run
      cases eq
      exact ⟨Appended.same _ room, Nat.zero_le _, by simp⟩
    | @cons h first upper stop page higher current =>
      simp only [Writer.finishPages] at run
      obtain ⟨⟨promoted, written⟩, mid, pageRan, step⟩ := bind_ok run
      obtain ⟨put, atEnd, endEq, firstEq, countEq, child⟩ :=
        writePage_ok current (Nat.le_refl _) rowLimit pageRan
      have lo := current.first_le
      have pos := child.valid.2.2.1
      have nonzero : stop ≠ 0 := by omega
      split at step
      · rename_i empty
        have upperEmpty := List.isEmpty_iff.mp empty
        subst upper
        have firstZero := higher.zero_start
        have startsAtZero := firstEq.trans firstZero
        obtain ⟨eq, rfl⟩ := pure_ok step
        cases eq
        refine ⟨by simpa only [put.position] using put, by omega, ?_⟩
        rw [ite_eq_right nonzero]
        exact ⟨by omega, promoted, rfl, rfl, startsAtZero, by omega, endEq.trans put.position, child⟩
      · obtain ⟨⟨middle, upperPages⟩, afterPush, pushRan, finishRan⟩ := bind_ok step
        obtain ⟨packet, disk⟩ := put.extended
        have lifted := higher.extend packet (Nat.le_refl _) (by simp)
        rw [← disk] at lifted
        rw [put.position] at pushRan
        have promotedStop : first + promoted.count = stop := by omega
        have upperOrdered : Ordered (rows.take (first + promoted.count)) := by
          rw [promotedStop]
          exact ordered
        obtain ⟨raised, covers⟩ := push_ok lifted child (by omega) firstEq upperOrdered target
          (by simpa [put.position] using put.room) pushRan
        rw [promotedStop] at covers
        rw [raised.position] at finishRan
        obtain ⟨finished, height, result⟩ := ih covers ordered rowLimit (by omega)
          (by simpa [raised.position] using raised.room) finishRan
        exact ⟨put.trans (raised.trans finished), height, by simpa [nonzero] using result⟩


private structure StateAt (layout : Layout) (crc : Checksum) (rows : List Entry)
    (file : ModelFile) (state : BuilderState) : Prop where
  offset : state.offset = file.bytes.size
  room : state.offset + footerPacketSize ≤ maxFileSize
  count : state.count ≤ rows.length
  countLimit : state.count ≤ maxFileSize
  ordered : Ordered (rows.take state.count)
  lastKey : state.lastKey = (rows.take state.count).getLast?.map Entry.key
  data : ∃ earlier, earlier ++ state.data.toList = rows.take state.count
  dataFits : ∀ row ∈ state.data.toList, Unified.rowFits layout row = true
  keyFits : ∀ row ∈ state.data.toList, indexEntrySize row.key + checksumSize ≤ maxRowSize
  pages : PendingPages layout crc file.bytes rows state.offset 0
    (state.count - state.data.size) state.pages
  empty : state.count = 0 → file.bytes = .empty

private theorem StateAt.initial (layout : Layout) (crc : Checksum) (rows : List Entry) :
    StateAt layout crc rows { rows } {} := by
  refine ⟨rfl, by decide, Nat.zero_le _, Nat.zero_le _, ?_, rfl, ⟨[], rfl⟩,
    by simp, by simp, .nil, by simp⟩
  simp [Ordered]

private theorem StateAt.dataSize (inv : StateAt layout crc rows file state) :
    state.data.size ≤ state.count := by
  obtain ⟨earlier, cut⟩ := inv.data
  have lengths := congrArg List.length cut
  simp only [List.length_append, Array.length_toList, List.length_take] at lengths
  omega

private theorem StateAt.dataRow (inv : StateAt layout crc rows file state)
    (i : Nat) (inside : i < state.data.size) :
    state.data[i] = rowAt rows (state.count - state.data.size + i) := by
  obtain ⟨earlier, cut⟩ := inv.data
  have lengths := congrArg List.length cut
  have count := inv.count
  have prior : earlier.length = state.count - state.data.size := by
    simp only [List.length_append, Array.length_toList, List.length_take, Nat.min_eq_left count] at lengths
    omega
  unfold rowAt
  have idx : state.count - state.data.size + i < state.count := by have := inv.dataSize; omega
  have same : rows[state.count - state.data.size + i]? =
      (rows.take state.count)[state.count - state.data.size + i]? :=
    (List.getElem?_take_of_lt idx).symm
  rw [same, ← cut, List.getElem?_append_right (by omega), show
    state.count - state.data.size + i - earlier.length = i by omega]
  simp [Array.getElem?_eq_getElem inside]

private theorem flushData_ok {layout : Layout} {crc : Checksum} {options : BuildOptions}
    {file out : ModelFile} {state next : BuilderState}
    (inv : StateAt layout crc rows file state) (target : options.indexTarget ≤ maxRowSize)
    (run : ((modelWriter crc layout options).flushData state).run file = .ok (next, out)) :
    StateAt layout crc rows out next ∧ Appended file out next.offset ∧
    next.data = #[] ∧ next.count = state.count ∧ next.lastKey = state.lastKey := by
  cases back : state.data.back? with
  | none =>
    simp only [Writer.flushData, back] at run
    obtain ⟨rfl, rfl⟩ := pure_ok run
    exact ⟨inv, inv.offset ▸ Appended.same _ (by simpa [inv.offset] using inv.room),
      Array.back?_eq_none_iff.mp back, rfl, rfl⟩
  | some last =>
    simp only [Writer.flushData, back] at run
    obtain ⟨position, mid, writeRan, remaining⟩ := bind_ok run
    rw [inv.offset] at writeRan
    obtain ⟨disk, pos, bounded, space⟩ := writePacket_ok writeRan
    let payload := encodePacket crc layout.tableId dataKind file.bytes.size (encodeData layout state.data)
    have payloadEq : mid.bytes = file.bytes ++ payload := congrArg ModelFile.bytes disk
    let ref : Ref := ⟨last.key, state.offset, position - state.offset,
      state.count - state.data.size, state.data.size⟩
    have endEq : position = state.offset + ((encodeData layout state.data).size + checksumSize) := by
      rw [pos, payloadEq, ByteArray.size_append, encodePacket_size, inv.offset]
    have len : ref.size = (encodeData layout state.data).size + checksumSize := by
      change position - state.offset = _
      omega
    have abuts : ref.offset + ref.size = mid.bytes.size := by
      change state.offset + (position - state.offset) = _
      omega
    have capacity := inv.countLimit
    have sourceRange := inv.count
    have dataFits := inv.dataSize
    have rowEnd : ref.firstRow + ref.count = state.count := by
      change state.count - state.data.size + state.data.size = _
      omega
    have dataPos : 0 < state.data.size := by
      have nz : state.data.size ≠ 0 := by
        intro sizeZero
        simp [Array.size_eq_zero_iff.mp sizeZero] at back
      omega
    have packetPos : 0 < ref.size := by
      rw [len]
      have : 0 < checksumSize := by decide
      omega
    have lastInside : state.data.size - 1 < state.data.size := by omega
    have lastRow : state.data[state.data.size - 1] = last := by
      rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem lastInside] at back
      exact Option.some.inj back
    have fence : ref.lastKey = (rowAt rows (ref.firstRow + ref.count - 1)).key := by
      rw [rowEnd]
      have eq := inv.dataRow (state.data.size - 1) lastInside
      rw [lastRow, show state.count - state.data.size + (state.data.size - 1) =
        state.count - 1 by omega] at eq
      exact congrArg Entry.key eq
    have packetSlice : mid.bytes.extract ref.offset (ref.offset + ref.size) = payload := by
      rw [payloadEq]
      change (file.bytes ++ payload).extract state.offset (state.offset + ref.size) = _
      rw [inv.offset, len]
      exact append_atEnd _ _ _ _ _
    have child : WrittenChild layout crc mid.bytes rows mid.bytes.size 0 ref := by
      refine ⟨?_, ⟨packetPos, ?_, dataPos, by omega⟩, Nat.le_of_eq abuts,
        by omega, fence, inv.keyFits _ (array_back_mem back)⟩
      · refine ⟨Nat.le_of_eq abuts, dataPos, by omega, fence, state.data, rfl,
          by change state.data.size ≤ maxFileSize; omega, inv.dataRow, ?_,
          ⟨len, by rwa [len], Nat.le_of_eq abuts, ?_⟩⟩
        · intro i hi
          exact inv.dataFits _ (by simp)
        · simpa only [payload, show ref.offset = file.bytes.size from inv.offset] using packetSlice
      · omega
    have oldPages := inv.pages.extend payload (Nat.le_refl _) (by simp [inv.offset])
    rw [← payloadEq] at oldPages
    obtain ⟨⟨off, pages⟩, afterPush, pushRan, done⟩ := bind_ok remaining
    change ((modelWriter crc layout options).push 1 position ref state.pages maxHeight).run mid =
      .ok ((off, pages), afterPush) at pushRan
    rw [pos] at pushRan
    obtain ⟨put, newPages⟩ := push_ok oldPages child (Nat.le_refl _) rfl
      (by change Ordered (rows.take (ref.firstRow + ref.count)); rw [rowEnd]; exact inv.ordered) target (by omega) pushRan
    obtain ⟨rfl, rfl⟩ := pure_ok done
    have beforePush : Appended file mid position :=
      ⟨by rw [disk], pos, ⟨payload, payloadEq⟩, space⟩
    refine ⟨⟨put.position, put.room, inv.count, capacity, inv.ordered, inv.lastKey,
      ⟨rows.take state.count, by simp⟩, by simp, by simp, ?_, ?_⟩,
      beforePush.trans put, rfl, rfl, rfl⟩
    · simpa [ref, put.position, Nat.sub_add_cancel dataFits] using newPages
    · intro zero
      change state.count = 0 at zero
      omega

private theorem checkRow_facts {row : Entry} {layout : Layout} {lastKey : Option ByteArray}
    (checked : (Unified.BuilderState.mk 0 0 lastKey #[] 0 #[] 0 #[] 0).checkRow layout row = .ok ()) :
    Unified.rowFits layout row = true ∧
      (∀ prev ∈ lastKey, prev < row.key) ∧
      indexEntrySize row.key + checksumSize ≤ maxRowSize := by
  unfold Unified.BuilderState.checkRow at checked
  dsimp at checked
  split at checked
  · cases checked
  · rename_i fits
    split at checked
    · cases checked
    · rename_i ordered
      split at checked
      · cases checked
      · split at checked
        · cases checked
        · rename_i keyFits
          refine ⟨by simpa using fits, ?_, Nat.le_of_not_gt keyFits⟩
          have all : lastKey.all (fun prev => decide (prev < row.key)) = true := by simpa using ordered
          simpa [Option.all_eq_true] using all

private theorem accept_ok {layout : Layout} {crc : Checksum} {options : BuildOptions}
    {file out : ModelFile} {state next : BuilderState} {row : Entry}
    (inv : StateAt layout crc rows file state)
    (taken : rows[state.count]? = some row) (room : state.count + 1 ≤ maxFileSize)
    (target : options.indexTarget ≤ maxRowSize)
    (run : ((modelWriter crc layout options).accept state row).run file = .ok (next, out)) :
    StateAt layout crc rows out next ∧ next.count = state.count + 1 ∧ out.rows = file.rows := by
  cases checked : ({ lastKey := state.lastKey } : Unified.BuilderState).checkRow layout row with
  | error error =>
    simp only [Writer.accept, modelWriter, checked] at run
    cases run
  | ok result =>
    cases result
    obtain ⟨fits, sorted, keyWidth⟩ := checkRow_facts checked
    simp only [Writer.accept, modelWriter, checked] at run
    have splitRun : ∃ ready mid, StateAt layout crc rows mid ready ∧ ready.count = state.count ∧
        mid.rows = file.rows ∧ ready.lastKey = state.lastKey ∧
        (pure { ready with
          count := ready.count + 1
          lastKey := some row.key
          data := ready.data.push row
          payloadBytes := ready.payloadBytes + Unified.entrySize layout row } : ModelM BuilderState).run mid =
          .ok (next, out) := by
      split at run
      · obtain ⟨ready, mid, prepared, returned⟩ := bind_ok run
        obtain ⟨post, put, _, count, key⟩ := flushData_ok (options := options) inv target prepared
        exact ⟨ready, mid, post, count, put.remaining, key, returned⟩
      · obtain ⟨ready, mid, prepared, returned⟩ := bind_ok run
        obtain ⟨rfl, rfl⟩ := pure_ok prepared
        exact ⟨_, _, inv, rfl, rfl, rfl, returned⟩
    obtain ⟨ready, mid, post, size, supplier, oldKey, returned⟩ := splitRun
    obtain ⟨rfl, rfl⟩ := pure_ok returned
    obtain ⟨rowIndex, got⟩ := List.getElem?_eq_some_iff.mp taken
    have takenPlus : rows.take (ready.count + 1) = rows.take ready.count ++ [row] := by
      rw [size, List.take_succ_eq_append_getElem rowIndex, got]
    have bufferSize := post.dataSize
    have consumed := post.ordered
    have orderNext : Ordered (rows.take (ready.count + 1)) := by
      rw [takenPlus]
      apply ordered_append consumed
      intro old last
      apply sorted old.key
      rw [← oldKey, post.lastKey, show (rows.take ready.count).getLast? = some old from last]
      rfl
    refine ⟨⟨post.offset, post.room, by dsimp; omega, by simpa [size] using room,
      orderNext, ?_, ?_, ?_, ?_, ?_, by simp⟩, by simp [size], supplier⟩
    · simp [takenPlus]
    · obtain ⟨earlier, cut⟩ := post.data
      refine ⟨earlier, ?_⟩
      simp only [Array.toList_push, ← List.append_assoc, cut, takenPlus]
    · intro entry member
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
      rcases member with old | rfl
      · exact post.dataFits entry old
      · exact fits
    · intro entry member
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
      rcases member with old | rfl
      · exact post.keyFits entry old
      · exact keyWidth
    · simpa only [Array.size_push, show ready.count + 1 - (ready.data.size + 1) =
        ready.count - ready.data.size by omega] using post.pages


private theorem streamRows_ok {layout : Layout} {crc : Checksum} {options : BuildOptions}
    {file out : ModelFile} {state next : BuilderState}
    (inv : StateAt layout crc rows file state) (supplier : file.rows = rows.drop state.count)
    (target : options.indexTarget ≤ maxRowSize) (room : state.count + fuel ≤ maxFileSize)
    (run : ((modelWriter crc layout options).streamRows modelNext state fuel).run file =
      .ok (next, out)) :
    StateAt layout crc rows out next ∧ next.count = rows.length ∧ out.rows = [] := by
  induction fuel generalizing file out state next with
  | zero =>
    obtain ⟨available, bytes⟩ := file
    cases available with
    | nil =>
      have result := Except.ok.inj run
      cases result
      have endAt := List.drop_eq_nil_iff.mp supplier.symm
      exact ⟨inv, Nat.le_antisymm inv.count endAt, rfl⟩
    | cons row rest => cases run
  | succ fuel ih =>
    obtain ⟨available, bytes⟩ := file
    cases available with
    | nil =>
      have result := Except.ok.inj run
      cases result
      have endAt := List.drop_eq_nil_iff.mp supplier.symm
      exact ⟨inv, Nat.le_antisymm inv.count endAt, rfl⟩
    | cons row rest =>
      simp only [Writer.streamRows] at run
      obtain ⟨item, consumed, readRan, continuation⟩ := bind_ok run
      change Except.ok (some row, (⟨rest, bytes⟩ : ModelFile)) = .ok (item, consumed) at readRan
      cases readRan
      obtain ⟨ready, mid, one, loop⟩ := bind_ok continuation
      have actual := congrArg List.head? supplier
      change some row = (rows.drop state.count).head? at actual
      rw [List.head?_drop] at actual
      have consumedInv : StateAt layout crc rows ⟨rest, bytes⟩ state :=
        ⟨inv.offset, inv.room, inv.count, inv.countLimit, inv.ordered, inv.lastKey,
         inv.data, inv.dataFits, inv.keyFits, inv.pages, inv.empty⟩
      obtain ⟨post, count, tail⟩ := accept_ok consumedInv actual.symm (by omega) target one
      have remaining : mid.rows = rows.drop ready.count := by
        have eq := congrArg List.tail supplier
        change rest = (rows.drop state.count).tail at eq
        rw [List.tail_drop] at eq
        exact tail.trans (eq.trans (by rw [count]))
      exact ih post remaining (by omega) loop

private theorem finishImage_ok {layout : Layout} {crc : Checksum} {options : BuildOptions}
    {file out : ModelFile} {state : BuilderState}
    (valid : layout.Valid) (target : options.indexTarget ≤ maxRowSize)
    (inv : StateAt layout crc rows file state) (all : state.count = rows.length)
    (run : (do
      let state ← (modelWriter crc layout options).flushData state
      let (height, offset, size) ←
        (modelWriter crc layout options).finishPages 1 state.offset state.pages maxHeight
      let footer : Footer := ⟨⟨layout, state.count, offset, size⟩, height⟩
      modelSink.write (encodePacket crc 0 footerKind 0 (encodeFooter footer))
      modelSink.flush
      return state.count : ModelM Nat).run file = .ok (count, out)) :
    count = rows.length ∧ Image layout crc out.bytes rows := by
  obtain ⟨complete, mid, dataRan, continuation⟩ := bind_ok run
  obtain ⟨closed, _, emptyData, countEq, _⟩ := flushData_ok inv target dataRan
  have total := countEq.trans all
  obtain ⟨⟨height, offset, size⟩, body, pagesRan, lastRan⟩ := bind_ok continuation
  rw [closed.offset] at pagesRan
  have pages := closed.pages
  rw [emptyData] at pages
  simp only [Array.size_empty, Nat.sub_zero] at pages
  rw [closed.offset] at pages
  obtain ⟨written, depth, result⟩ := finishPages_ok pages closed.ordered closed.countLimit target
    (by simp) (by simpa [closed.offset] using closed.room) pagesRan
  let footer : Footer := ⟨⟨layout, complete.count, offset, size⟩, height⟩
  let suffix := encodePacket crc 0 footerKind 0 (encodeFooter footer)
  change Except.ok (complete.count, { body with bytes := body.bytes ++ suffix }) =
    .ok (count, out) at lastRan
  cases lastRan
  have len : suffix.size = footerPacketSize := by simp [suffix, footerPacketSize]
  have sizeEq : (body.bytes ++ suffix).size = body.bytes.size + footerPacketSize := by simp [len]
  have endAt : (body.bytes ++ suffix).size - footerPacketSize = body.bytes.size := by omega
  have enough : footerPacketSize ≤ (body.bytes ++ suffix).size := by omega
  have exactFooter : (body.bytes ++ suffix).extract
      ((body.bytes ++ suffix).size - footerPacketSize) (body.bytes ++ suffix).size = suffix := by
    rw [endAt]
    exact ByteArray.extract_append_eq_right rfl (by simp)
  have ordered : Ordered rows := by simpa [total] using closed.ordered
  refine ⟨total, ordered, sizeEq ▸ written.room, footer, ?_, rfl, total, enough, exactFooter, ?_⟩
  · have bound : Unified.footerBodySize ≤ footerPacketSize := by decide
    have countLimit := closed.countLimit
    by_cases empty : complete.count = 0
    · simp only [empty, ↓reduceIte] at result
      obtain ⟨zero, off, len, _⟩ := result
      refine ⟨⟨valid, countLimit, ?_, ?_⟩, depth, ?_⟩
      · change offset + size + Unified.footerBodySize ≤ maxFileSize
        have := written.room
        omega
      · simp [footer, empty, off, len]
      · simp [footer, zero, empty]
    · simp only [empty, ↓reduceIte] at result
      obtain ⟨pos, ref, off, len, _, _, ends, root⟩ := result
      have sizePositive := root.valid.1
      refine ⟨⟨valid, countLimit, ?_, ?_⟩, depth, ?_⟩
      · change offset + size + Unified.footerBodySize ≤ maxFileSize
        have := written.room
        omega
      · simp [footer, empty, ← len, sizePositive]
      · simp [footer, empty, Nat.ne_of_gt pos]
  · by_cases empty : complete.count = 0
    · simp only [empty, ↓reduceIte] at result
      obtain ⟨_, _, _, same⟩ := result
      have noBytes := closed.empty empty
      have emptyRows : rows = [] := List.length_eq_zero_iff.mp (total.symm.trans empty)
      simp [emptyRows, same, noBytes, len]
    · have rowsNonempty : rows.isEmpty = false := by
        cases rows with
        | nil => exact False.elim (empty total)
        | cons => rfl
      simp only [rowsNonempty, Bool.false_eq_true, ↓reduceIte, endAt]
      simp only [empty, ↓reduceIte] at result
      obtain ⟨pos, r, off, len, first, count, ends, root⟩ := result
      refine ⟨by change offset + size = _; omega, ?_⟩
      have rootEq : footer.rootRef = { r with lastKey := ByteArray.empty } := by
        cases r
        simp_all [footer, Footer.rootRef]
      rw [rootEq]
      have continued := root.tree.extend suffix (Nat.le_refl _) (by simp)
      change TreeInImage layout crc (body.bytes ++ suffix) rows { r with lastKey := .empty }
        body.bytes.size false height
      cases height with
      | zero => omega
      | succ level =>
        obtain ⟨refs, node, below⟩ := continued
        refine ⟨refs, ⟨⟨node.packet.shape, node.packet.extent, node.packet.within,
          node.packet.length, node.packet.slice⟩, node.coverage, node.bounds, ?_⟩, below⟩
        intro impossible
        cases impossible

/-- Successful runs of the executable streaming writer produce the exact
recursive image for the supplier they consumed. Packet and count limits are
properties of that successful run. Healthy progress has a separate contract. -/
theorem modelBuild_ok {crc : Checksum} {layout : Layout} {options : BuildOptions}
    {rows : List Entry} {count : Nat} {bytes : ByteArray}
    (built : modelBuild crc layout rows options = .ok (count, bytes)) :
    count = rows.length ∧ Image layout crc bytes rows := by
  unfold modelBuild at built
  cases run : (buildStream crc layout modelSink modelNext id options).run { rows } with
  | error error => simp [run, Bind.bind, Except.bind] at built
  | ok result =>
    obtain ⟨n, out⟩ := result
    have resultEq : (n, out.bytes) = (count, bytes) := by
      simpa [run, Bind.bind, Except.bind, Pure.pure, Except.pure] using built
    cases resultEq
    by_cases layoutValid : layout.Valid
    · by_cases targets : 0 < options.dataTarget ∧ options.dataTarget ≤ maxRowSize ∧
          0 < options.indexTarget ∧ options.indexTarget ≤ maxRowSize
      · simp only [buildStream, layoutValid, targets, ↓reduceIte] at run
        obtain ⟨last, file, body, done⟩ := bind_ok run
        change ((modelWriter crc layout options).streamRows modelNext {} maxFileSize).run
          ⟨rows, .empty⟩ = .ok (last, file) at body
        obtain ⟨image, count, _⟩ := streamRows_ok (StateAt.initial layout crc rows) rfl
          targets.2.2.2 (by simp) body
        exact finishImage_ok layoutValid targets.2.2.2 image count done
      · simp only [buildStream, layoutValid, targets, ↓reduceIte] at run
        cases run
    · simp only [buildStream, layoutValid, ↓reduceIte] at run
      cases run

end ImmutableSSTable.Recursive
