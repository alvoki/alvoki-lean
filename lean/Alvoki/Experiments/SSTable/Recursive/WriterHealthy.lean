import Alvoki.Experiments.SSTable.Recursive.WriterStreamingProgress
import Alvoki.Experiments.SSTable.Recursive.WriterFinalProgress
import Alvoki.Experiments.SSTable.Recursive.WriterEffectsProgress

namespace ImmutableSSTable.Recursive

open Unified (Layout Checksum ModelM ModelFile modelNext modelSink encodePacket
  NativeWriteEffects NativeWriteM NativeWriteState)

/-- A proof-only budget computed from the input count, without running the writer
or estimating its output from a successful execution. -/
def healthyByteBudget (rows : Nat) : Nat :=
  (rows + 1) * rowStepBytes + finalizationReserve maxHeight + footerPacketSize

private theorem healthyByteBudget_spare (budget : healthyByteBudget rows ≤ maxFileSize) :
    rows < 2 ^ (maxHeight - 1) := by
  have factor : 2 ≤ rowStepBytes := by decide
  have scaled := Nat.mul_le_mul_left (rows + 1) factor
  rw [Nat.mul_comm (rows + 1) 2] at scaled
  have limit : maxFileSize < 2 * 2 ^ (maxHeight - 1) := by decide
  unfold healthyByteBudget at budget
  omega

private theorem healthyByteBudget_count (budget : healthyByteBudget rows ≤ maxFileSize) :
    rows ≤ maxFileSize :=
  Nat.le_trans (Nat.le_of_lt (healthyByteBudget_spare budget)) (by decide)

private theorem finish_healthy {crc : Checksum} {layout : Layout} {options : BuildOptions}
    {rows : List Entry} {last : BuilderState} {file : ModelFile}
    (inv : StateAt layout crc rows file last) (buffer : Buffered layout last)
    (count : last.count = rows.length) (eof : file.rows = [])
    (spent : file.bytes.size ≤ last.count * rowStepBytes)
    (target : options.indexTarget ≤ maxRowSize)
    (budget : healthyByteBudget rows.length ≤ maxFileSize) :
    ∃ out, (do
      let state ← (modelWriter crc layout options).flushData last
      let (height, offset, size) ←
        (modelWriter crc layout options).finishPages 1 state.offset state.pages maxHeight
      let footer : Footer := ⟨⟨layout, state.count, offset, size⟩, height⟩
      modelSink.write (encodePacket crc 0 footerKind 0 (encodeFooter footer))
      modelSink.flush
      return state.count : ModelM Nat).run file = .ok (rows.length, out) ∧ out.rows = [] := by
  have spare := healthyByteBudget_spare budget
  unfold healthyByteBudget at budget
  rw [Nat.add_mul, Nat.one_mul] at budget
  rw [count] at spent
  obtain ⟨ready, mid, flushed, flushCost, supply, empty, _⟩ :=
    Writer.flushData_healthy crc layout options inv buffer spare (by omega)
  obtain ⟨readyAt, _, _, readyCount, _⟩ := flushData_ok inv target flushed
  have total := readyCount.trans count
  have pages := readyAt.pages
  have ranked := readyAt.ranked
  simp only [empty, Array.size_empty, Nat.sub_zero] at pages ranked
  rw [readyAt.offset] at pages
  obtain ⟨height, offset, size, body, finished, appended⟩ :=
    Writer.finishPages_progress crc layout options pages ranked readyAt.ordered readyAt.countLimit
      target (by omega) (by omega)
  rw [← readyAt.offset] at finished
  change ((modelWriter crc layout options).finishPages 1 ready.offset ready.pages maxHeight).run
    mid = _ at finished
  let footer : Footer := ⟨⟨layout, ready.count, offset, size⟩, height⟩
  let suffix := encodePacket crc 0 footerKind 0 (encodeFooter footer)
  refine ⟨{ body with bytes := body.bytes ++ suffix }, ?_, ?_⟩
  · change (((modelWriter crc layout options).flushData last).run file).bind _ = _
    rw [flushed]
    change (((modelWriter crc layout options).finishPages 1 ready.offset ready.pages
      maxHeight).run mid).bind _ = _
    rw [finished]
    change Except.ok (ready.count, { body with bytes := body.bytes ++ suffix }) = _
    rw [total]
  · exact appended.remaining.trans (supply.trans eof)

private theorem bind_progress {first : ModelM α} {rest : α → ModelM β}
    {start mid out : ModelFile} {value : α} {result : β}
    (ran : first.run start = .ok (value, mid)) (next : (rest value).run mid = .ok (result, out)) :
    (first >>= rest).run start = .ok (result, out) := by
  change (first.run start).bind _ = _
  rw [ran]
  exact next

private theorem modelBuild_of_run {crc : Checksum} {layout : Layout} {rows : List Entry}
    {options : BuildOptions} {count : Nat} {out : ModelFile}
    (run : (buildStream crc layout modelSink modelNext id options).run { rows } = .ok (count, out)) :
    modelBuild crc layout rows options = .ok (count, out.bytes) := by
  unfold modelBuild
  rw [run]
  rfl

/-- For valid layouts, targets and ordered representable input under the
conservative byte budget, the executable writer reaches EOF and writes its
footer. This follows the same schedule as the successful-build refinement. -/
theorem modelBuild_progress {crc : Checksum} {layout : Layout} {rows : List Entry}
    {options : BuildOptions} (valid : layout.Valid)
    (targets : 0 < options.dataTarget ∧ options.dataTarget ≤ maxRowSize ∧
      0 < options.indexTarget ∧ options.indexTarget ≤ maxRowSize)
    (admitted : AdmittedRows layout rows) (budget : healthyByteBudget rows.length ≤ maxFileSize) :
    ∃ bytes, modelBuild crc layout rows options = .ok (rows.length, bytes) := by
  have cap := healthyByteBudget_spare budget
  have enough := healthyByteBudget_count budget
  have rowBudget : (rows.length + 1) * rowStepBytes + footerPacketSize ≤ maxFileSize := by
    unfold healthyByteBudget at budget
    omega
  obtain ⟨last, file, streamed, inv, buffer, count, eof, spent⟩ :=
    streamRows_progress (StateAt.initial layout crc rows) (Buffered.initial layout)
      (by simp) admitted targets.2.1 targets.2.2.2 cap maxFileSize (by simpa using enough)
      (by simp) (by simp) rowBudget
  obtain ⟨out, final, _⟩ := finish_healthy inv buffer count eof spent targets.2.2.2 budget
  have run : (buildStream crc layout modelSink modelNext id options).run { rows } =
      .ok (rows.length, out) := by
    simp only [buildStream, valid, targets, ↓reduceIte]
    exact bind_progress streamed final
  exact ⟨out.bytes, modelBuild_of_run run⟩

/-- Under the local healthy native effect contracts and the input-only
capacity bound, exclusive create, the full streaming schedule and sync
succeed on the exact newly created inode. -/
theorem buildFileWith_progress {ops : OutputOps (NativeWriteM handle inode) handle}
    {path : System.FilePath} {nextRow : NativeWriteM handle inode (Option Entry)}
    {crc : Checksum} {layout : Layout} {options : BuildOptions}
    {before : NativeWriteState handle inode}
    (effects : NativeWriteEffects ops path nextRow)
    (available : HealthyNativeWrite ops path nextRow) (fresh : before.binding = none)
    (valid : layout.Valid)
    (targets : 0 < options.dataTarget ∧ options.dataTarget ≤ maxRowSize ∧
      0 < options.indexTarget ∧ options.indexTarget ≤ maxRowSize)
    (admitted : AdmittedRows layout before.rows)
    (budget : healthyByteBudget before.rows.length ≤ maxFileSize) :
    ∃ bytes, Image layout crc bytes before.rows ∧
      ∃ after,
        (buildFileWith ops crc path layout nextRow id options).run before =
          .ok before.rows.length after ∧
        after.rows = [] ∧ after.appended = bytes ∧ after.flushed = true ∧
        ∃ output identity created, (ops.openFile path .writeNew).run before = .ok output created ∧
          after.BoundTo path output identity ∧ after.durable = some (identity, bytes) := by
  obtain ⟨bytes, ran⟩ := modelBuild_progress (crc := crc) valid targets admitted budget
  obtain ⟨_, image, native⟩ := buildFileWith_healthy effects available fresh ran
  exact ⟨bytes, image, native⟩

end ImmutableSSTable.Recursive
