import Alvoki.Experiments.SSTable.FixedBuilder
import Alvoki.Experiments.SSTable.Proofs.FixedFormat

namespace ImmutableSSTable.Fixed

open Std

/-- The consecutive full blocks, numbered starting at `first`. -/
def encodeBlocks (layout : Layout) (first : Nat) : List (List Entry) → ByteArray
  | [] => .empty
  | group :: rest =>
    encodeBlock layout first (encodePayload group) ++ encodeBlocks layout (first + 1) rest

def encodeLast (layout : Layout) (block : Nat) (rows : List Entry) : ByteArray :=
  if rows.isEmpty then .empty else encodeBlock layout block (encodePayload rows)

/-- A complete wire image from the full groups and optional short final group. -/
def encodeImage (layout : Layout) (full : List (List Entry)) (tail : List Entry) : ByteArray :=
  encodeBlocks layout 0 full ++ encodeLast layout full.length tail ++
    encodeFooter layout (full.flatten ++ tail).length

private structure BuildState where
  rows : List Entry
  data : ByteArray := .empty

private abbrev BuildM := StateT BuildState (Except String)

private def modelSink : Sink BuildM where
  write bytes := fun s => .ok ((), {s with data := s.data ++ bytes})
  flush := pure ()

private def modelNext : BuildM (Option Entry) := fun s =>
  match s.rows with
  | [] => .ok (none, s)
  | row :: tail => .ok (some row, {s with rows := tail})

/-- Interpret the executable streaming schedule over a fresh, healthy sink. -/
def modelBuild (layout : Layout) (rows : List Entry) : Except String (Nat × ByteArray) := do
  let (count, file) ← (buildStream layout modelSink modelNext id).run {rows}
  return (count, file.data)

private def After (rows : List Entry) (prev : Option ByteArray) : Prop :=
  ∀ row ∈ rows, ∀ key ∈ prev, key < row.key

private theorem checkRow_ok {state : BuilderState} {layout : Layout} {row : Entry}
    (checked : state.checkRow layout row = .ok ()) :
    layout.RowFits row ∧ After [row] state.lastKey ∧ layout.Fits (state.count + 1) := by
  unfold BuilderState.checkRow at checked
  split at checked
  next width =>
    split at checked
    next order =>
      split at checked
      next fits =>
        have test := (Option.all_eq_true _ _).mp order
        refine ⟨width, ?_, fits⟩
        intro r member key previous
        have same : r = row := by simpa using member
        subst r
        exact of_decide_eq_true (test key previous)
      next rejected => cases checked
    next rejected => cases checked
  next rejected => cases checked

private theorem ordered_cons {prev : Option ByteArray} {row : Entry} {rows : List Entry}
    (before : After [row] prev) (ordered : Ordered rows) (after : After rows (some row.key)) :
    Ordered (row :: rows) ∧ After (row :: rows) prev := by
  have related : ∀ r ∈ rows, row.key < r.key := fun r member => after r member row.key rfl
  refine ⟨List.pairwise_cons.mpr ⟨related, ordered⟩, ?_⟩
  intro r member key previous
  rcases List.mem_cons.mp member with rfl | inside
  · exact before r (by simp) key previous
  · exact Std.lt_trans (before row (by simp) key previous) (related r inside)

private structure Buffered (layout : Layout) (state : BuilderState) (pending : List Entry) : Prop where
  fits : layout.Fits state.count
  count : state.pendingRows = pending.length
  payload : state.pending = encodePayload pending
  short : pending.length < layout.rowsPerBlock

private structure StreamResult (layout : Layout) (state last : BuilderState)
    (pending rows : List Entry) (written : ByteArray) (file : BuildState)
    (groups : List (List Entry)) (tail : List Entry) : Prop where
  ordered : Ordered rows
  after : After rows state.lastKey
  widths : ∀ row ∈ rows, layout.RowFits row
  combined : groups.flatten ++ tail = pending ++ rows
  full : ∀ group ∈ groups, group.length = layout.rowsPerBlock
  short : tail.length < layout.rowsPerBlock
  count : last.count = state.count + rows.length
  blockCount : last.blocks = state.blocks + groups.length
  tailCount : last.pendingRows = tail.length
  buffered : last.pending = encodePayload tail
  data : file.data = written ++ encodeBlocks layout state.blocks groups
  fits : layout.Fits last.count

private theorem streamRows_ok (layout : Layout) (rows : List Entry) (state : BuilderState)
    (pending : List Entry) (buffered : Buffered layout state pending)
    (room : Nat) (written : ByteArray) (last : BuilderState) (file : BuildState)
    (run : (streamRows layout modelSink modelNext id state room).run ⟨rows, written⟩ =
      .ok (last, file)) :
    ∃ groups tail, StreamResult layout state last pending rows written file groups tail := by
  induction rows generalizing pending state room written last file with
  | nil =>
    have same : (state, (⟨[], written⟩ : BuildState)) = (last, file) := by
      cases room <;> simpa [streamRows, modelNext, StateT.run, Bind.bind, StateT.bind,
        Except.bind, Pure.pure, StateT.pure, Except.pure] using run
    cases same
    refine ⟨[], pending, ⟨?_, ?_, ?_, ?_, ?_, buffered.short, ?_, ?_, buffered.count,
      buffered.payload, ?_, buffered.fits⟩⟩ <;> simp [Ordered, After, encodeBlocks]

  | cons row rest ih =>
    cases room with
    | zero => cases run
    | succ room =>
      cases checked : state.checkRow layout row with
      | error error =>
        simp only [streamRows, modelNext, checked, StateT.run, Bind.bind, StateT.bind, Except.bind] at run
        change (Except.error error : Except String (BuilderState × BuildState)) = .ok (last, file) at run
        cases run
      | ok accepted =>
        cases accepted
        obtain ⟨width, before, fits⟩ := checkRow_ok checked
        let updated := state.buffer row
        let nextPending := pending ++ [row]
        have amount : updated.pendingRows = nextPending.length := by
          simp [updated, BuilderState.buffer, nextPending, buffered.count]
        have payload : updated.pending = encodePayload nextPending := by
          simp [updated, BuilderState.buffer, nextPending, buffered.payload, encodePayload_append, encodePayload]
        by_cases full : updated.pendingRows = layout.rowsPerBlock
        · have nextRun :
              (streamRows layout modelSink modelNext id updated.advance room).run
                ⟨rest, written ++ encodeBlock layout updated.blocks updated.pending⟩ = .ok (last, file) := by
            simpa [streamRows, modelNext, checked, StateT.run, Bind.bind, StateT.bind, Except.bind,
              modelSink, updated, show (state.buffer row).pendingRows = layout.rowsPerBlock from full] using run
          have nextBuffered : Buffered layout updated.advance [] :=
            ⟨fits, rfl, rfl, fits.1.1⟩
          obtain ⟨groups, tail, result⟩ := ih _ [] nextBuffered _ _ _ _ nextRun
          obtain ⟨ordered, after⟩ := ordered_cons before result.ordered result.after
          refine ⟨nextPending :: groups, tail, ⟨ordered, after, ?_, ?_, ?_, result.short,
            ?_, ?_, result.tailCount, result.buffered, ?_, result.fits⟩⟩
          · intro r member
            rcases List.mem_cons.mp member with rfl | inside
            · exact width
            · exact result.widths r inside
          · simpa [nextPending, List.append_assoc] using congrArg (nextPending ++ ·) result.combined
          · intro group member
            rcases List.mem_cons.mp member with rfl | inside
            · exact amount.symm.trans full
            · exact result.full group inside
          · simpa [updated, BuilderState.buffer, BuilderState.advance, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using result.count
          · simpa [updated, BuilderState.buffer, BuilderState.advance, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using result.blockCount
          · simpa [updated, BuilderState.buffer, BuilderState.advance, encodeBlocks,
              ByteArray.append_assoc, ← payload] using result.data
        · have short : nextPending.length < layout.rowsPerBlock := by
            have previous := buffered.short
            simp [nextPending] at amount ⊢
            omega
          have nextRun :
              (streamRows layout modelSink modelNext id updated room).run ⟨rest, written⟩ =
                .ok (last, file) := by
            simpa [streamRows, modelNext, checked, StateT.run, Bind.bind, StateT.bind, Except.bind,
              updated, show (state.buffer row).pendingRows ≠ layout.rowsPerBlock from full] using run
          have nextBuffered : Buffered layout updated nextPending := ⟨fits, amount, payload, short⟩
          obtain ⟨groups, tail, result⟩ := ih _ _ nextBuffered _ _ _ _ nextRun
          obtain ⟨ordered, after⟩ := ordered_cons before result.ordered result.after
          refine ⟨groups, tail, ⟨ordered, after, ?_, ?_, result.full, result.short,
            ?_, result.blockCount, result.tailCount, result.buffered, result.data, result.fits⟩⟩
          · intro r member
            rcases List.mem_cons.mp member with rfl | inside
            · exact width
            · exact result.widths r inside
          · simpa [nextPending, List.append_assoc] using result.combined
          · simpa [updated, BuilderState.buffer, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using result.count

/-- A successful run of the actual builder produces complete fixed-width groups,
an optional shorter tail, and the exact image of those ordered input rows. -/
theorem modelBuild_ok {layout : Layout} {rows : List Entry} {count : Nat} {bytes : ByteArray}
    (built : modelBuild layout rows = .ok (count, bytes)) :
    layout.Fits rows.length ∧ Ordered rows ∧ (∀ row ∈ rows, layout.RowFits row) ∧
      count = rows.length ∧
      ∃ full tail, full.flatten ++ tail = rows ∧
        (∀ group ∈ full, group.length = layout.rowsPerBlock) ∧
        tail.length < layout.rowsPerBlock ∧ bytes = encodeImage layout full tail := by
  by_cases initial : layout.Fits 0
  · have start : Buffered layout {} [] := ⟨initial, rfl, rfl, initial.1.1⟩
    cases body : (streamRows layout modelSink modelNext id {} maxFileSize).run {rows} with
    | error error =>
      have failed : modelBuild layout rows = .error error := by
        simp only [modelBuild, buildStream, initial, ↓reduceIte, Bind.bind, StateT.bind, StateT.run]
        rw [show streamRows layout modelSink modelNext id {} maxFileSize {rows} = .error error from body]
        rfl
      rw [failed] at built
      cases built
    | ok out =>
      obtain ⟨last, file⟩ := out
      obtain ⟨full, tail, result⟩ := streamRows_ok layout rows {} [] start maxFileSize
        .empty last file body
      have joined : full.flatten ++ tail = rows := by simpa using result.combined
      have length : last.count = rows.length := by simpa using result.count
      have ordinal : last.blocks = full.length := by simpa using result.blockCount
      have resultEq : modelBuild layout rows = .ok (rows.length, encodeImage layout full tail) := by
        simp only [modelBuild, buildStream, initial, ↓reduceIte, Bind.bind, StateT.bind, StateT.run]
        rw [show streamRows layout modelSink modelNext id {} maxFileSize {rows} = .ok (last, file) from body]
        cases tail <;> simp [Sink.finish, modelSink, Bind.bind, StateT.bind, Except.bind, Pure.pure,
          StateT.pure, Except.pure, result.tailCount, result.buffered, result.data, length, ordinal,
          encodeImage, encodeLast, joined]
      rw [resultEq, Except.ok.injEq, Prod.mk.injEq] at built
      exact ⟨by simpa [length] using result.fits, result.ordered, result.widths, built.1.symm,
        full, tail, joined, result.full, result.short, built.2.symm⟩
  · have failed : modelBuild layout rows = .error "invalid SSTable fixed layout" := by
      simp [modelBuild, buildStream, initial, throw]
      rfl
    rw [failed] at built
    cases built

end ImmutableSSTable.Fixed
