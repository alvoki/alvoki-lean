import Alvoki.Storage.Table.SequentialPurge

namespace Alvoki.Sequential
open Compaction.Model

theorem Table.write_winner_before {table : Table α} (row : Entry (Option α))
    (key snapshot : UInt64) (early : snapshot < row.sequence) :
    across key snapshot (table.write row).histories = across key snapshot table.histories := by
  have invisible : winner [row] key snapshot = none := by
    simp [winner, eligible, UInt64.not_le.mpr early]
  have unchanged : winner (table.memory.union (.singleton row)).rows key snapshot =
      winner table.memory.rows key snapshot := by
    change winner (Compaction.Model.union table.memory.rows (History.singleton row).rows) key snapshot = _
    rw [winner_union table.memory.ordered (History.singleton row).ordered]
    change newest (winner table.memory.rows key snapshot) (winner [row] key snapshot) = _
    rw [invisible]
    cases winner table.memory.rows key snapshot <;> rfl
  have append (runs : List (History α)) :
      across key snapshot (runs ++ [table.memory.union (.singleton row)]) =
        across key snapshot (runs ++ [table.memory]) := by
    induction runs with
    | nil => simp only [List.nil_append, across, unchanged]
    | cons run runs ih => simp only [List.cons_append, across, ih]
  exact append table.runs

/-- Sequential table operations share one write clock, retention floor, and pin registry. -/
structure SnapshotTable (α : Type) where
  private mk ::
  table : Table α
  committed : UInt64
  pins : SnapshotPins
  floor_committed : pins.floor ≤ committed
  pins_committed : ∀ pin ∈ pins.active, pin.sequence ≤ committed

def SnapshotTable.empty : SnapshotTable α :=
  ⟨⟨[], .empty⟩, 0, .empty, UInt64.le_refl _, by simp [SnapshotPins.empty]⟩

/-- A session's pin registry can be attached to the same abstract data and retention floor. -/
theorem SnapshotTable.exists_reboundPins (state : SnapshotTable α) (pins : SnapshotPins)
    (floor : pins.floor = state.pins.floor)
    (committed : ∀ pin ∈ pins.active, pin.sequence ≤ state.committed) :
    ∃ rebound : SnapshotTable α, rebound.table = state.table ∧
      rebound.committed = state.committed ∧ rebound.pins = pins :=
  ⟨⟨state.table, state.committed, pins, floor.symm ▸ state.floor_committed, committed⟩, rfl, rfl, rfl⟩

/-- Replace the immutable runs while keeping the memtable, clock and pins. -/
theorem SnapshotTable.exists_replaceRuns (state : SnapshotTable α) (runs : List (History α)) :
    ∃ result : SnapshotTable α, result.table = ⟨runs, state.table.memory⟩ ∧
      result.committed = state.committed ∧ result.pins = state.pins :=
  ⟨{ state with table := { state.table with runs } }, rfl, rfl, rfl⟩

def SnapshotTable.acquireAt (state : SnapshotTable α) (snapshot : UInt64) :
    Option (SnapshotPin × SnapshotTable α) :=
  match h : state.pins.acquire state.committed snapshot with
  | none => none
  | some (pin, pins) =>
    have ⟨_, bound, seq, _, active, _, floor⟩ := SnapshotPins.acquire_spec h
    some (pin, ⟨state.table, state.committed, pins, floor ▸ state.floor_committed,
      fun p mem => by
        rw [active] at mem
        rcases List.mem_cons.mp mem with rfl | old
        · exact seq ▸ bound
        · exact state.pins_committed p old⟩)

/-- Acquire the latest committed snapshot. -/
def SnapshotTable.acquire (state : SnapshotTable α) : Option (SnapshotPin × SnapshotTable α) :=
  state.acquireAt state.committed

theorem SnapshotTable.acquireAt_iff (state : SnapshotTable α) (snapshot : UInt64) :
    (state.acquireAt snapshot).isSome = true ↔
      state.pins.floor ≤ snapshot ∧ snapshot ≤ state.committed := by
  rw [← state.pins.acquire_iff state.committed snapshot]
  unfold SnapshotTable.acquireAt
  split <;> simp_all

theorem SnapshotTable.acquire_latest (state : SnapshotTable α) :
    state.acquire.isSome = true :=
  (state.acquireAt_iff _).mpr ⟨state.floor_committed, UInt64.le_refl _⟩

def SnapshotTable.release (state : SnapshotTable α) (handle : SnapshotHandle) : SnapshotTable α :=
  { state with
    pins := state.pins.release handle
    floor_committed := state.floor_committed
    pins_committed := fun p mem => state.pins_committed p ((state.pins.mem_release handle p).mp mem).1 }

theorem SnapshotTable.release_idempotent (state : SnapshotTable α) (handle : SnapshotHandle) :
    (state.release handle).release handle = state.release handle := by
  cases state
  unfold SnapshotTable.release
  congr 1
  exact SnapshotPins.release_idempotent ..

@[simp] theorem SnapshotTable.mem_release (state : SnapshotTable α) (handle : SnapshotHandle)
    (pin : SnapshotPin) :
    pin ∈ (state.release handle).pins.active ↔ pin ∈ state.pins.active ∧ pin.handle ≠ handle :=
  state.pins.mem_release handle pin

def SnapshotTable.advanceFloor (state : SnapshotTable α) (floor : UInt64) : Option (SnapshotTable α) :=
  if committed : floor ≤ state.committed then
    match h : state.pins.advance floor with
    | none => none
    | some pins =>
      let spec := SnapshotPins.advance_spec h
      some ⟨state.table, state.committed, pins, spec.2.1 ▸ committed,
        fun p mem => state.pins_committed p (spec.2.2.1 ▸ mem)⟩
  else none

theorem SnapshotTable.advanceFloor_iff (state : SnapshotTable α) (floor : UInt64) :
    (state.advanceFloor floor).isSome = true ↔ floor ≤ state.committed ∧
      state.pins.floor ≤ floor ∧ ∀ pin ∈ state.pins.active, floor ≤ pin.sequence := by
  rw [← state.pins.advance_iff floor]
  unfold SnapshotTable.advanceFloor
  split
  · split <;> simp_all
  · rename_i exceeds
    simp [exceeds]

private theorem nextSequence_gt (committed : UInt64) (fits : committed.toNat + 1 < UInt64.size) :
    committed < UInt64.ofNat (committed.toNat + 1) := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' fits]
  omega

/-- Assign the next sequence, with exhaustion at the unsigned 64-bit endpoint. -/
def SnapshotTable.write (state : SnapshotTable α) (key : UInt64) (value : Option α) :
    Option (SnapshotTable α) :=
  if fits : state.committed.toNat + 1 < UInt64.size then
    let sequence := UInt64.ofNat (state.committed.toNat + 1)
    let advances := UInt64.le_of_lt (nextSequence_gt state.committed fits)
    some ⟨state.table.write ⟨key, sequence, value⟩, sequence, state.pins,
      UInt64.le_trans state.floor_committed advances,
      fun p mem => UInt64.le_trans (state.pins_committed p mem) advances⟩
  else none

theorem SnapshotTable.write_iff (state : SnapshotTable α) (key : UInt64) (value : Option α) :
    (state.write key value).isSome = true ↔ state.committed.toNat + 1 < UInt64.size := by
  unfold SnapshotTable.write
  split <;> simp_all

theorem SnapshotTable.write_spec {before after : SnapshotTable α} {key : UInt64} {value : Option α}
    (changed : before.write key value = some after) :
    after.committed.toNat = before.committed.toNat + 1 ∧ after.pins = before.pins ∧
      after.table = before.table.write ⟨key, after.committed, value⟩ := by
  unfold SnapshotTable.write at changed
  split at changed
  · rename_i fits
    cases changed
    exact ⟨UInt64.toNat_ofNat_of_lt' fits, rfl, rfl⟩
  · contradiction

def SnapshotTable.flush (state : SnapshotTable α) : SnapshotTable α :=
  { state with table := state.table.flush }

def SnapshotTable.compact (state : SnapshotTable α) (index : Nat) : Option (SnapshotTable α) :=
  (state.table.compactAt index state.pins.floor).map fun table => { state with table }

def SnapshotTable.purge [DecidableEq α] (state : SnapshotTable α) (index : Nat)
    (key sequence : UInt64) : Option (SnapshotTable α) :=
  (state.table.purgeAt index key sequence state.pins.floor).map fun table => { state with table }

private def pinAt (pins : List SnapshotPin) (handle : SnapshotHandle) : Option SnapshotPin :=
  pins.find? (fun pin => decide (pin.handle = handle))

def SnapshotPins.find (pins : SnapshotPins) (handle : SnapshotHandle) : Option SnapshotPin :=
  pinAt pins.active handle

private theorem pinAt_mem {pins : List SnapshotPin} {pin : SnapshotPin}
    (unique : (pins.map SnapshotPin.handle).Nodup) (mem : pin ∈ pins) :
    pinAt pins pin.handle = some pin := by
  induction pins with
  | nil => contradiction
  | cons head rest ih =>
    have h := List.nodup_cons.mp unique
    rcases List.mem_cons.mp mem with rfl | tail
    · simp [pinAt]
    · have other : head.handle ≠ pin.handle := by
        intro eq
        exact h.1 (List.mem_map.mpr ⟨pin, tail, eq.symm⟩)
      simpa [pinAt, other] using ih h.2 tail

theorem SnapshotPins.find_of_mem (pins : SnapshotPins) {pin : SnapshotPin}
    (active : pin ∈ pins.active) : pins.find pin.handle = some pin :=
  pinAt_mem pins.unique active

theorem SnapshotPins.find_released (pins : SnapshotPins) (handle : SnapshotHandle) :
    (pins.release handle).find handle = none := by
  apply List.find?_eq_none.mpr
  intro pin active matched
  exact ((pins.mem_release handle pin).mp active).2 (of_decide_eq_true matched)

/-- Outer absence means the handle is inactive. Inner absence means the key is absent. -/
def SnapshotTable.lookup (state : SnapshotTable α) (handle : SnapshotHandle)
    (key : UInt64) : Option (Option α) :=
  (state.pins.find handle).map fun pin => state.table.lookup key pin.sequence

def SnapshotTable.range (state : SnapshotTable α) (handle : SnapshotHandle)
    (start stop : UInt64) : Option (List (Entry (Option α))) :=
  (state.pins.find handle).map fun pin => state.table.range start stop pin.sequence

theorem SnapshotTable.lookup_pinned (state : SnapshotTable α) {pin : SnapshotPin}
    (mem : pin ∈ state.pins.active) (key : UInt64) :
    state.lookup pin.handle key = some (state.table.lookup key pin.sequence) := by
  rw [SnapshotTable.lookup, state.pins.find_of_mem mem]
  rfl

theorem SnapshotTable.range_pinned (state : SnapshotTable α) {pin : SnapshotPin}
    (mem : pin ∈ state.pins.active) (start stop : UInt64) :
    state.range pin.handle start stop = some (state.table.range start stop pin.sequence) := by
  rw [SnapshotTable.range, state.pins.find_of_mem mem]
  rfl

/-- The relation only admits states obtained by the operations above. -/
inductive SnapshotTable.Step (α : Type) : SnapshotTable α → SnapshotTable α → Prop
  | acquire {before after : SnapshotTable α} {snapshot : UInt64} {pin : SnapshotPin} :
      before.acquireAt snapshot = some (pin, after) → Step α before after
  | release (state : SnapshotTable α) (handle : SnapshotHandle) : Step α state (state.release handle)
  | advance {before after : SnapshotTable α} {floor : UInt64} :
      before.advanceFloor floor = some after → Step α before after
  | write {before after : SnapshotTable α} {key : UInt64} {value : Option α} :
      before.write key value = some after → Step α before after
  | flush (state : SnapshotTable α) : Step α state state.flush
  | compact {before after : SnapshotTable α} {index : Nat} :
      before.compact index = some after → Step α before after
  | purge [DecidableEq α] {before after : SnapshotTable α} {index : Nat} {key sequence : UInt64} :
      before.purge index key sequence = some after → Step α before after

/-- Previously allocated handles can only remain active or be removed.
Every active read is preserved at its original sequence. -/
theorem SnapshotTable.Step.snapshot_frame {before after : SnapshotTable α} (step : Step α before after) :
    before.pins.nextHandle ≤ after.pins.nextHandle ∧
      (∀ pin ∈ after.pins.active, pin.handle.id < before.pins.nextHandle → pin ∈ before.pins.active) ∧
      ∀ pin ∈ before.pins.active, ∀ key,
        after.table.visibleEntry key pin.sequence = before.table.visibleEntry key pin.sequence := by
  cases step with
  | acquire h =>
    unfold SnapshotTable.acquireAt at h
    split at h
    · contradiction
    · rename_i found
      have ⟨_, _, _, issued, active, next, _⟩ := SnapshotPins.acquire_spec found
      cases h
      refine ⟨next ▸ Nat.le_succ _, ?_, fun _ _ _ => rfl⟩
      intro pin mem old
      rw [active] at mem
      rcases List.mem_cons.mp mem with rfl | previous
      · omega
      · exact previous
  | release state handle =>
    exact ⟨Nat.le_refl _, fun pin mem _ => ((SnapshotTable.mem_release _ _ pin).mp mem).1,
      fun _ _ _ => rfl⟩
  | advance h =>
    unfold SnapshotTable.advanceFloor at h
    split at h
    · split at h
      · contradiction
      · rename_i changed
        have spec := SnapshotPins.advance_spec changed
        cases h
        exact ⟨spec.2.2.2.1 ▸ Nat.le_refl _, fun pin mem _ => spec.2.2.1 ▸ mem, fun _ _ _ => rfl⟩
    · contradiction
  | write h =>
    have ⟨next, pins, table⟩ := SnapshotTable.write_spec h
    refine ⟨by rw [pins]; exact Nat.le_refl _, fun _ mem _ => pins ▸ mem, ?_⟩
    intro pin mem key
    have fresh : before.committed < after.committed := by
      rw [UInt64.lt_iff_toNat_lt, next]
      omega
    rw [table, Table.visibleEntry, Table.visibleEntry,
      Table.write_winner_before _ _ _ (UInt64.lt_of_le_of_lt (before.pins_committed pin mem) fresh)]
  | flush state =>
    refine ⟨Nat.le_refl _, fun _ mem _ => mem, ?_⟩
    intro pin _ key
    simp only [SnapshotTable.flush, Table.visibleEntry, Table.flush, Table.histories]
    rw [across_append_empty]
  | compact h =>
    unfold SnapshotTable.compact at h
    obtain ⟨_, compacted, rfl⟩ := Option.map_eq_some_iff.mp h
    refine ⟨Nat.le_refl _, fun _ mem _ => mem, ?_⟩
    intro pin mem key
    simp only [Table.visibleEntry]
    rw [Table.compactAt_winner compacted (before.pins.safe pin mem) key]
  | purge h =>
    unfold SnapshotTable.purge at h
    obtain ⟨_, purged, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨Nat.le_refl _, fun _ mem _ => mem, fun pin mem key =>
      Table.purgeAt_visibleEntry purged (before.pins.safe pin mem) key⟩

inductive SnapshotTable.Steps (α : Type) : SnapshotTable α → SnapshotTable α → Prop
  | refl (state : SnapshotTable α) : Steps α state state
  | tail {first prior last : SnapshotTable α} :
      Steps α first prior → Step α prior last → Steps α first last

theorem SnapshotTable.Steps.handles_monotone {before after : SnapshotTable α}
    (steps : Steps α before after) : before.pins.nextHandle ≤ after.pins.nextHandle := by
  induction steps with
  | refl => exact Nat.le_refl _
  | tail _ step ih => exact Nat.le_trans ih step.snapshot_frame.1

/-- An issued handle cannot reappear after its acquisition has been released. -/
theorem SnapshotTable.Steps.previously_issued {before after : SnapshotTable α}
    (steps : Steps α before after) {pin : SnapshotPin} (final : pin ∈ after.pins.active)
    (issued : pin.handle.id < before.pins.nextHandle) : pin ∈ before.pins.active := by
  induction steps with
  | refl => exact final
  | tail earlier step ih =>
    exact ih (step.snapshot_frame.2.1 pin final
      (Nat.lt_of_lt_of_le issued earlier.handles_monotone))

theorem SnapshotTable.Steps.same_acquisition {before after : SnapshotTable α}
    (steps : Steps α before after) {first last : SnapshotPin}
    (initial : first ∈ before.pins.active) (final : last ∈ after.pins.active)
    (handle : first.handle = last.handle) : first = last := by
  have issued : last.handle.id < before.pins.nextHandle :=
    handle ▸ before.pins.issued first initial
  have old := steps.previously_issued final issued
  have initialPin := pinAt_mem before.pins.unique initial
  rw [handle, pinAt_mem before.pins.unique old] at initialPin
  exact (Option.some.inj initialPin).symm

theorem SnapshotTable.Steps.visibleEntry_stable {before after : SnapshotTable α}
    (steps : Steps α before after) {pin : SnapshotPin} (initial : pin ∈ before.pins.active)
    (final : pin ∈ after.pins.active) (key : UInt64) :
    after.table.visibleEntry key pin.sequence = before.table.visibleEntry key pin.sequence := by
  induction steps with
  | refl => rfl
  | tail earlier step ih =>
    have old := Nat.lt_of_lt_of_le (before.pins.issued pin initial) earlier.handles_monotone
    have prior := step.snapshot_frame.2.1 pin final old
    exact (step.snapshot_frame.2.2 pin prior key).trans (ih prior)

/-- Once released, an issued handle stays inactive in all later states. -/
theorem SnapshotTable.Steps.retired_reads {before after : SnapshotTable α} {pin : SnapshotPin}
    (steps : Steps α (before.release pin.handle) after) (initial : pin ∈ before.pins.active)
    (key start stop : UInt64) :
    after.lookup pin.handle key = none ∧ after.range pin.handle start stop = none := by
  have missing : pinAt after.pins.active pin.handle = none := by
    apply List.find?_eq_none.mpr
    intro candidate mem matched
    have same := of_decide_eq_true matched
    have issued : candidate.handle.id < (before.release pin.handle).pins.nextHandle := by
      change candidate.handle.id < before.pins.nextHandle
      rw [same]
      exact before.pins.issued pin initial
    have released := steps.previously_issued mem issued
    exact ((before.mem_release pin.handle candidate).mp released).2 same
  simp [SnapshotTable.lookup, SnapshotTable.range, SnapshotPins.find, missing]

/-- A handle active at both ends of a trace denotes the same acquisition and sees the same reads. -/
theorem SnapshotTable.Steps.reads_stable {before after : SnapshotTable α}
    (steps : Steps α before after) {pin result : SnapshotPin} (initial : pin ∈ before.pins.active)
    (final : result ∈ after.pins.active) (handle : pin.handle = result.handle)
    (key start stop : UInt64) :
    after.lookup pin.handle key = before.lookup pin.handle key ∧
      after.range pin.handle start stop = before.range pin.handle start stop := by
  have same := steps.same_acquisition initial final handle
  subst result
  have visible := steps.visibleEntry_stable initial final
  constructor
  · rw [after.lookup_pinned final, before.lookup_pinned initial,
      Table.lookup_eq_visibleEntry, Table.lookup_eq_visibleEntry, visible key]
  · rw [after.range_pinned final, before.range_pinned initial,
      Table.range_of_visibleEntry_eq start stop pin.sequence visible]

end Alvoki.Sequential
