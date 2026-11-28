import Alvoki.Experiments.SortedRun.IOEffects
import Alvoki.Experiments.SortedRun.SSTableProofs
import Alvoki.Experiments.SSTable.Proofs.UnifiedReadSafety

namespace SortedRun

open ImmutableSSTable ImmutableSSTable.Unified

def effectSlotIO (slot : Slot (EIO ε) α) : Slot (EStateM ε World) α :=
  ⟨effect slot.get, fun value => effect (slot.set value)⟩

private theorem effect_fill (front : Front cursor row) (pull : Pull (EIO ε) cursor row) :
    effect (front.fill pull) = front.fill (effect ∘ pull) := by
  cases front <;> rfl

private theorem effect_next [LT key] [DecidableLT key] (keyOf : row → key)
    (newer : Pull (EIO ε) left row) (older : Pull (EIO ε) right row)
    (slot : Slot (EIO ε) (Frontier left right row)) :
    effect (next keyOf newer older slot) =
      next keyOf (effect ∘ newer) (effect ∘ older) (effectSlotIO slot) := by
  simp [next, effect_fill, effectSlotIO]

/-- Frame local effects against a logical observation. Neither outcome
rolls back the actual world. -/
def Frames (observe : σ → φ) (action : EStateM ε σ α) : Prop :=
  ∀ start, match action start with
    | .ok _ reached | .error _ reached => observe reached = observe start

/-- The local laws for the fresh private reference. The world may change,
but get leaves its content in place and set replaces it exactly. Both
operations preserve the caller-owned input and writer observations. -/
structure RefEffects (ref : IO.Ref α) (contents : World → α) (observe : World → φ) : Prop where
  get : ∀ start, ∃ reached, effect (nativeSlot ref).get start = .ok (contents start) reached ∧
    contents reached = contents start ∧ observe reached = observe start
  set : ∀ value start, ∃ reached, effect ((nativeSlot ref).set value) start = .ok () reached ∧
    contents reached = value ∧ observe reached = observe start

private theorem fill_frames {observe : σ → φ} {pull : Pull (EStateM ε σ) cursor row}
    (kept : ∀ index, Frames observe (pull index)) (front : Front cursor row) :
    Frames observe (front.fill pull) := by
  cases front with
  | unread index => exact kept index
  | buffered item => intro start; rfl

/-- A fallible pull is exact on success. Either outcome preserves the
input, writer and frontier observations chosen by the caller. -/
structure CursorEffects (table : Table (EIO String)) (observe : World → φ)
    (rows : List Entry) : Prop where
  exactSuffix : Pull.Exact ((fun i => effect (tablePullIO table i))) rows.drop
  frame : ∀ index, Frames observe (effect (tablePullIO table index))

theorem checkedCursorEffects {table : Table (EIO String)} {source : Source (EIO String)}
    {crc : Checksum} {layout : Layout} {rows : List Entry} {image : ByteArray}
    (observe : World → φ)
    (built : Image crc layout rows image)
    (reads : ∀ start, ScopedRead (fun t => observe t = observe start) source image)
    (opened : openTableChecked source crc layout.tableId start = .ok table ready) :
    CursorEffects table observe rows := by
  have handoff := built.checkedOpenTable_next_scoped (reads start) start rfl
  rw [opened] at handoff
  have nextPost := handoff.2
  constructor
  · intro index before item reached ran
    have pulled := nextPost _ (reads before) index before rfl
    cases call : table.next index before with
    | error error after =>
      simp [tablePullIO, effect, EIO.adapt, call] at ran
    | ok value after =>
      rw [call] at pulled
      simp [tablePullIO, effect, EIO.adapt, call] at ran
      obtain ⟨rfl, rfl⟩ := ran
      rw [pulled.2]
      by_cases inside : index < rows.length
      · simp only [Contents.next, dite_eq_left inside, Front.remaining]
        exact (List.drop_eq_getElem_cons inside).symm
      · simp only [Contents.next, dite_eq_right inside, Front.remaining]
        exact (List.drop_eq_nil_of_le (Nat.le_of_not_gt inside)).symm
  · intro index before
    have pulled := nextPost _ (reads before) index before rfl
    cases call : table.next index before <;>
      simp [tablePullIO, effect, EIO.adapt, call] at pulled ⊢
    · exact pulled.1
    · exact pulled

private abbrev ByteFrontier := Frontier Nat Nat Entry

/-- The required newer fill returns its error without executing a slot
write or an older pull. -/
theorem nativeNext_newerError {ref : IO.Ref ByteFrontier}
    {newer older : Table (EIO String)} {front : ByteFrontier}
    (loaded : effect (nativeSlot ref).get start = .ok front readAt)
    (failed : front.newer.fill (fun i => effect (tablePullIO newer i)) readAt =
      .error error reached) :
    effect (next Entry.key (tablePullIO newer) (tablePullIO older) (nativeSlot ref)) start =
      .error error reached := by
  rw [effect_next]
  simp only [next, effectSlotIO, Bind.bind, EStateM.bind, loaded, Function.comp_def, failed]

/-- The required older fill starts after the successful newer head was
stored. Its original error and reached world terminate this callback. -/
theorem nativeNext_olderError {ref : IO.Ref ByteFrontier}
    {newer older : Table (EIO String)} {front : ByteFrontier}
    (loaded : effect (nativeSlot ref).get start = .ok front readAt)
    (newerRead : front.newer.fill (fun i => effect (tablePullIO newer i)) readAt =
      .ok head observed)
    (stored : effect ((nativeSlot ref).set { front with newer := .buffered head }) observed =
      .ok () oldReadAt)
    (failed : front.older.fill (fun i => effect (tablePullIO older i)) oldReadAt =
      .error error reached) :
    effect (next Entry.key (tablePullIO newer) (tablePullIO older) (nativeSlot ref)) start =
      .error error reached := by
  rw [effect_next]
  simp only [next, effectSlotIO, Bind.bind, EStateM.bind, loaded, Function.comp_def,
    newerRead, stored, failed]

/-- Interpret the actual native callback, including both reference updates.
A failed older pull keeps the newer head already stored. The physical
observation is framed on both outcomes. -/
theorem nativeNext_refines {ref : IO.Ref ByteFrontier} {front : World → ByteFrontier}
    {observe : World → φ} {newer older : Table (EIO String)} {newRows oldRows : List Entry}
    (cell : RefEffects ref front observe)
    (newRead : CursorEffects newer (fun w => (front w, observe w)) newRows)
    (oldRead : CursorEffects older (fun w => (front w, observe w)) oldRows)
    (start : World) :
    match effect (next Entry.key (tablePullIO newer) (tablePullIO older) (nativeSlot ref)) start with
    | .error error reached => observe reached = observe start ∧
      ((∃ probed, (front start).newer.fill (fun i => effect (tablePullIO newer i)) probed =
          .error error reached ∧ front reached = front start) ∨
       (∃ newHead probed, (front start).older.fill (fun i => effect (tablePullIO older i)) probed =
          .error error reached ∧ front reached = { front start with newer := .buffered newHead }))
    | .ok item reached =>
      observe reached = observe start ∧
      item = ((front start).remaining Entry.key newRows.drop oldRows.drop).head? ∧
      (front reached).remaining Entry.key newRows.drop oldRows.drop =
        ((front start).remaining Entry.key newRows.drop oldRows.drop).tail ∧
      (item = none → (front start).newer.remaining newRows.drop = [] ∧
        (front start).older.remaining oldRows.drop = []) := by
  obtain ⟨readAt, readSlot, frontRead, keptRead⟩ := cell.get start
  rw [effect_next]
  simp only [next, effectSlotIO, Bind.bind, EStateM.bind, readSlot, Function.comp_def]
  have firstFrame := fill_frames newRead.frame (front start).newer readAt
  cases first : (front start).newer.fill (fun i => effect (tablePullIO newer i)) readAt with
  | error error reached =>
    simp only [first] at firstFrame ⊢
    exact ⟨(congrArg Prod.snd firstFrame).trans keptRead,
      Or.inl ⟨readAt, first, (congrArg Prod.fst firstFrame).trans frontRead⟩⟩
  | ok itemA afterNew =>
    simp only [first] at firstFrame ⊢
    have firstExact := fill_exact newRead.exactSuffix first
    obtain ⟨afterSet, setSlot, frontSet, keptSet⟩ :=
      cell.set { front start with newer := .buffered itemA } afterNew
    rw [setSlot]
    have kept := keptSet.trans ((congrArg Prod.snd firstFrame).trans keptRead)
    have oldFrame := fill_frames oldRead.frame (front start).older afterSet
    cases second : (front start).older.fill (fun i => effect (tablePullIO older i)) afterSet with
    | error error reached =>
      simp only [second] at oldFrame ⊢
      exact ⟨(congrArg Prod.snd oldFrame).trans kept,
        Or.inr ⟨itemA, afterSet, second, (congrArg Prod.fst oldFrame).trans frontSet⟩⟩
    | ok itemB afterOld =>
      simp only [second] at oldFrame ⊢
      have oldExact := fill_exact oldRead.exactSuffix second
      obtain ⟨completed, stored, final, keptFinal⟩ :=
        cell.set (choose Entry.key itemA itemB).2 afterOld
      simp only [stored, EStateM.pure, Pure.pure, final]
      have exactMerge := choose_exact Entry.key newRows.drop oldRows.drop itemA itemB
      simp only [Frontier.remaining] at exactMerge ⊢
      rw [← firstExact, ← oldExact]
      exact ⟨keptFinal.trans ((congrArg Prod.snd oldFrame).trans kept),
        exactMerge.1.1, exactMerge.1.2, exactMerge.2.1⟩

end SortedRun
