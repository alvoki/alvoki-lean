import Alvoki.Experiments.SSTable.Recursive.WriterProofs
import Alvoki.Experiments.SSTable.Recursive.WriterProgress

namespace ImmutableSSTable.Recursive

open Unified (Layout Checksum ModelM ModelFile modelNext checksumSize encodeData dataSize
  entrySize indexEntrySize)

structure AdmittedRows (layout : Layout) (rows : List Entry) : Prop where
  ordered : Ordered rows
  fits : ∀ row ∈ rows, Unified.rowFits layout row = true ∧
    dataSize layout 1 (entrySize layout row) ≤ maxRowSize ∧
    indexEntrySize row.key + checksumSize ≤ maxRowSize

/-- One data packet and a promotion flush at each index level. This reserve is
charged once per accepted row and once for the terminal data flush. -/
def rowStepBytes : Nat := maxRowSize + maxIndexSize * maxHeight

structure Buffered (layout : Layout) (state : BuilderState) : Prop where
  payload : state.payloadBytes = (state.data.toList.map (entrySize layout)).sum
  fits : dataSize layout state.data.size state.payloadBytes ≤ maxRowSize

theorem Buffered.empty (data : state.data = #[]) (payload : state.payloadBytes = 0) :
    Buffered layout state := by
  refine ⟨by simp [data, payload], ?_⟩
  simp only [data, Array.size_empty, payload, dataSize, Nat.zero_add]
  cases layout.hasOffsets <;> decide

theorem Buffered.initial (layout : Layout) : Buffered layout {} := Buffered.empty rfl rfl

private theorem Buffered.packet (buffer : Buffered layout state) :
    (encodeData layout state.data).size + checksumSize ≤ maxRowSize := by
  rw [Unified.encodeData_size, ← buffer.payload]
  exact buffer.fits

private def addRow (layout : Layout) (state : BuilderState) (row : Entry) : BuilderState :=
  { state with
    count := state.count + 1
    lastKey := some row.key
    data := state.data.push row
    payloadBytes := state.payloadBytes + entrySize layout row }

private theorem Buffered.add (buffer : Buffered layout state)
    (fits : dataSize layout (state.data.size + 1) (state.payloadBytes + entrySize layout row) ≤
      maxRowSize) :
    Buffered layout (addRow layout state row) := by
  exact ⟨by simp [addRow, buffer.payload], by simpa only [addRow, Array.size_push] using fits⟩

private theorem Buffered.empty_add (buffer : Buffered layout state) (empty : state.data = #[])
    (fits : dataSize layout 1 (entrySize layout row) ≤ maxRowSize) :
    Buffered layout (addRow layout state row) := by
  apply buffer.add
  have payload : state.payloadBytes = 0 := by simp [buffer.payload, empty]
  simpa [empty, payload] using fits

theorem Writer.flushData_healthy (crc : Checksum) (layout : Layout) (options : BuildOptions)
    {rows : List Entry} {file : ModelFile} {state : BuilderState}
    (inv : StateAt layout crc rows file state) (buffer : Buffered layout state)
    (cap : rows.length < 2 ^ (maxHeight - 1))
    (space : file.bytes.size + rowStepBytes + footerPacketSize ≤ maxFileSize) :
    ∃ ready out, ((modelWriter crc layout options).flushData state).run file = .ok (ready, out) ∧
      out.bytes.size ≤ file.bytes.size + rowStepBytes ∧ out.rows = file.rows ∧
      ready.data = #[] ∧ Buffered layout ready := by
  have rooms : state.pages.length < maxHeight := by
    apply inv.ranked.length_lt
    · decide
    · simp only [Nat.zero_add]
      have := inv.count
      omega
  have pending := inv.pages.pendingPacketBytes_le
  have stackBound := Nat.mul_le_mul_left maxIndexSize (Nat.le_of_lt rooms)
  have packet := buffer.packet
  have combined : (encodeData layout state.data).size + checksumSize +
      pendingPacketBytes state.pages ≤ rowStepBytes := by
    unfold rowStepBytes
    omega
  have pages := inv.pages
  rw [inv.offset] at pages
  obtain ⟨ready, out, ran, pos, _, empty, supplier, maxPosition, payloadZero⟩ :=
    Writer.flushData_progress crc layout options inv.offset pages packet rooms (by omega)
  have payload : ready.payloadBytes = 0 := by
    by_cases nonempty : state.data ≠ #[]
    · exact payloadZero nonempty
    · have dataEmpty := Classical.not_not.mp nonempty
      simp only [Writer.flushData, dataEmpty, Array.back?_empty] at ran
      obtain ⟨eq, _⟩ := pure_ok ran
      rw [eq, buffer.payload, dataEmpty]
      rfl
  exact ⟨ready, out, ran, by omega, supplier, empty, Buffered.empty empty payload⟩

private theorem rowCheck (inv : StateAt layout crc rows file state)
    (admitted : AdmittedRows layout rows) (taken : rows[state.count]? = some row) :
    ({ lastKey := state.lastKey } : Unified.BuilderState).checkRow layout row = .ok () := by
  obtain ⟨inside, atIndex⟩ := List.getElem?_eq_some_iff.mp taken
  have next : rows.take (state.count + 1) = rows.take state.count ++ [row] := by
    rw [List.take_succ_eq_append_getElem inside, atIndex]
  have sortedPrefix : Ordered (rows.take state.count ++ [row]) := next ▸ admitted.ordered.take
  have allowed := admitted.fits row (by rw [← atIndex]; exact List.getElem_mem inside)
  have increasing : state.lastKey.all (fun prev => decide (prev < row.key)) = true := by
    rw [inv.lastKey, Option.all_eq_true]
    intro prev member
    cases back : (rows.take state.count).getLast? with
    | none => simp [back] at member
    | some last =>
      have old : last ∈ rows.take state.count := List.mem_of_getLast? back
      have eq : last.key = prev := by simpa [back, Option.mem_def, eq_comm] using member
      rw [← eq]
      exact decide_eq_true ((List.pairwise_append.mp sortedPrefix).2.2 last old row (by simp))
  simp [Unified.BuilderState.checkRow, allowed.1, increasing, Nat.not_lt_of_ge allowed.2.1,
    Nat.not_lt_of_ge allowed.2.2]

private theorem accept_healthy {rows : List Entry} {file : ModelFile} {state : BuilderState}
    (inv : StateAt layout crc rows file state) (buffer : Buffered layout state)
    (admitted : AdmittedRows layout rows) (taken : rows[state.count]? = some row)
    (dataTarget : options.dataTarget ≤ maxRowSize) (cap : rows.length < 2 ^ (maxHeight - 1))
    (space : file.bytes.size + rowStepBytes + footerPacketSize ≤ maxFileSize) :
    ∃ next out, ((modelWriter crc layout options).accept state row).run file = .ok (next, out) ∧
      out.bytes.size ≤ file.bytes.size + rowStepBytes ∧ Buffered layout next := by
  have validated := rowCheck inv admitted taken
  obtain ⟨index, val⟩ := List.getElem?_eq_some_iff.mp taken
  have single := (admitted.fits row (by rw [← val]; exact List.getElem_mem index)).2.1
  let mustFlush := !state.data.isEmpty &&
    decide (dataSize layout (state.data.size + 1) (state.payloadBytes + entrySize layout row) >
      options.dataTarget)
  by_cases flush : mustFlush = true
  · obtain ⟨ready, out, ran, pos, _, empty, readyBuffer⟩ :=
      Writer.flushData_healthy crc layout options inv buffer cap space
    refine ⟨addRow layout ready row, out, ?_, pos, readyBuffer.empty_add empty single⟩
    simp only [mustFlush] at flush
    simp only [Writer.accept, modelWriter, validated]
    change StateT.run (if mustFlush then _ else _) file = _
    rw [ite_eq_left flush]
    change (((modelWriter crc layout options).flushData state).run file).bind _ = _
    rw [ran]
    rfl
  · refine ⟨addRow layout state row, file, ?_, by omega, ?_⟩
    · simp only [mustFlush] at flush
      simp only [Writer.accept, modelWriter, validated]
      change StateT.run (if mustFlush then _ else _) file = _
      rw [ite_eq_right flush]
      rfl
    · by_cases empty : state.data = #[]
      · exact buffer.empty_add empty single
      · apply buffer.add
        have nonempty : state.data.isEmpty = false :=
          Bool.eq_false_of_ne_true (fun e => empty (Array.isEmpty_iff.mp e))
        have bound : dataSize layout (state.data.size + 1) (state.payloadBytes + entrySize layout row) ≤
            options.dataTarget := by
          simpa [mustFlush, nonempty] using flush
        exact Nat.le_trans bound dataTarget

/-- The executable supplier loop reaches EOF with its actual pending pages.
Only the consumed prefix and a positional upper bound are tracked here. -/
theorem streamRows_progress {rows : List Entry} {file : ModelFile} {state : BuilderState}
    (inv : StateAt layout crc rows file state) (buffer : Buffered layout state)
    (available : file.rows = rows.drop state.count)
    (admitted : AdmittedRows layout rows)
    (dataTarget : options.dataTarget ≤ maxRowSize) (indexTarget : options.indexTarget ≤ maxRowSize)
    (cap : rows.length < 2 ^ (maxHeight - 1))
    (fuel : Nat) (enough : rows.length ≤ state.count + fuel)
    (rowLimit : state.count + fuel ≤ maxFileSize)
    (spent : file.bytes.size ≤ state.count * rowStepBytes)
    (budget : (rows.length + 1) * rowStepBytes + footerPacketSize ≤ maxFileSize) :
    ∃ last out, ((modelWriter crc layout options).streamRows modelNext state fuel).run file =
        .ok (last, out) ∧
      StateAt layout crc rows out last ∧ Buffered layout last ∧ last.count = rows.length ∧
      out.rows = [] ∧ out.bytes.size ≤ last.count * rowStepBytes := by
  induction fuel generalizing file state with
  | zero =>
    have endAt : state.count = rows.length := by have := inv.count; omega
    have empty : file.rows = [] := by simp [available, endAt]
    obtain ⟨supply, bytes⟩ := file
    change supply = [] at empty
    subst supply
    exact ⟨state, _, rfl, inv, buffer, endAt, rfl, spent⟩
  | succ fuel ih =>
    obtain ⟨supply, bytes⟩ := file
    cases supply with
    | nil =>
      have reaches := List.drop_eq_nil_iff.mp available.symm
      have endAt : state.count = rows.length := Nat.le_antisymm inv.count reaches
      exact ⟨state, _, rfl, inv, buffer, endAt, rfl, spent⟩
    | cons row rest =>
      let consumed : ModelFile := ⟨rest, bytes⟩
      have consumedInv : StateAt layout crc rows consumed state :=
        ⟨inv.offset, inv.room, inv.count, inv.countLimit, inv.ordered, inv.lastKey,
          inv.data, inv.dataFits, inv.keyFits, inv.pages, inv.ranked, inv.empty⟩
      have nextInput := congrArg List.head? available
      change some row = (rows.drop state.count).head? at nextInput
      rw [List.head?_drop] at nextInput
      have space : consumed.bytes.size + rowStepBytes + footerPacketSize ≤ maxFileSize := by
        have counts : state.count + 1 ≤ rows.length + 1 := by have := inv.count; omega
        have cost := Nat.mul_le_mul_right rowStepBytes counts
        rw [Nat.add_mul] at cost
        simp only [Nat.one_mul] at cost
        change bytes.size ≤ _ at spent
        change bytes.size + rowStepBytes + footerPacketSize ≤ _
        omega
      obtain ⟨ready, mid, accepted, costs, readyBuffer⟩ :=
        accept_healthy consumedInv buffer admitted nextInput.symm dataTarget cap space
      obtain ⟨readyInv, count, restEq⟩ :=
        accept_ok consumedInv nextInput.symm (by omega) indexTarget accepted
      have remaining : mid.rows = rows.drop ready.count := by
        have tailEq := congrArg List.tail available
        change rest = (rows.drop state.count).tail at tailEq
        rw [List.tail_drop] at tailEq
        exact restEq.trans (tailEq.trans (by rw [count]))
      have readySpent : mid.bytes.size ≤ ready.count * rowStepBytes := by
        rw [count, Nat.succ_mul]
        change mid.bytes.size ≤ bytes.size + rowStepBytes at costs
        change bytes.size ≤ _ at spent
        omega
      obtain ⟨last, out, readRest, post, finalBuffer, total, eof, finalSpent⟩ :=
        ih readyInv readyBuffer remaining (by omega) (by omega) readySpent
      refine ⟨last, out, ?_, post, finalBuffer, total, eof, finalSpent⟩
      simp only [Writer.streamRows]
      change (((modelWriter crc layout options).accept state row).run consumed).bind _ = _
      rw [accepted]
      exact readRest

end ImmutableSSTable.Recursive
