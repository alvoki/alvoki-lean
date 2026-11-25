namespace Alvoki.WAL.OrderedTwoSlot

inductive Slot where
  | first | second
  deriving DecidableEq

def Slot.other : Slot → Slot
  | .first => .second
  | .second => .first

structure Record (Frontier : Type) where
  epoch : Nat
  frontier : Frontier

-- A missing or invalid slot has already been rejected by the slot decoder.
abbrev Slots (Frontier : Type) := Slot → Option (Record Frontier)

def writeTarget (before : Slots Frontier) (active : Slot)
    (target : Option (Record Frontier)) : Slots Frontier :=
  fun slot => if slot = active then before slot else target

theorem writeTarget_keepsActive (before : Slots Frontier) (active : Slot)
    (target : Option (Record Frontier)) :
    writeTarget before active target active = before active := by
  simp [writeTarget]

theorem writeTarget_updatesOther (before : Slots Frontier) (active : Slot)
    (target : Option (Record Frontier)) :
    writeTarget before active target active.other = target := by
  cases active <;> simp [writeTarget, Slot.other]

inductive SelectionError where
  | noValidSlot | ambiguousEpoch | invalidFrontier
  deriving DecidableEq

def selectNewest (left right : Option (Record Frontier)) :
    Except SelectionError (Record Frontier) :=
  match left, right with
  | none, none => .error .noValidSlot
  | some record, none | none, some record => .ok record
  | some a, some b =>
    if a.epoch < b.epoch then .ok b
    else if b.epoch < a.epoch then .ok a
    else .error .ambiguousEpoch

/-- Check the selected frontier once. In particular, failure at the newer
frontier cannot turn into successful recovery at the older frontier. -/
def recover (valid : Frontier → Bool) (slots : Slots Frontier) :
    Except SelectionError (Record Frontier) := do
  let record ← selectNewest (slots .first) (slots .second)
  if valid record.frontier then return record
  else throw .invalidFrontier

private theorem selectNewest_comm (left right : Option (Record Frontier)) :
    selectNewest left right = selectNewest right left := by
  cases left <;> cases right <;> simp only [selectNewest]
  split <;> split <;> rename_i h₁ h₂
  all_goals try (exfalso; omega)
  all_goals simp [h₁, h₂] at *
  all_goals split <;> simp_all
  all_goals omega

private theorem select_written (before : Slots Frontier) (active : Slot)
    {old : Record Frontier} (present : before active = some old)
    (target : Option (Record Frontier)) :
    selectNewest (writeTarget before active target .first)
      (writeTarget before active target .second) = selectNewest (some old) target := by
  cases active
  · simpa [writeTarget, Slot.other] using congrArg (fun record => selectNewest record target) present
  · simpa [writeTarget, Slot.other, present] using selectNewest_comm target (some old)

private theorem select_older (active : Record Frontier) (inactive : Option (Record Frontier))
    (older : ∀ stale, inactive = some stale → stale.epoch < active.epoch) :
    selectNewest (some active) inactive = .ok active := by
  cases inactive with
  | none => rfl
  | some stale =>
    have lt := older stale rfl
    have notLt : ¬active.epoch < stale.epoch := by omega
    simp [selectNewest, lt, notLt]

inductive Phase where
  | beforeWalSync
  | beforeSlotWrite
  | slotWriteUncertain
  | slotSynced

/-- Primitive crash reports for one attempt. The active slot is modeled as a
distinct failure unit throughout. Before targeting the inactive slot, the WAL
barrier must succeed. Only its uncertain write/sync allows an invalid slot. -/
inductive Survivor (before : Slots Frontier) (active : Slot) (next : Record Frontier) :
    Phase → Slots Frontier → Prop where
  | beforeWalSync : Survivor before active next .beforeWalSync
      (writeTarget before active (before active.other))
  | beforeSlotWrite : Survivor before active next .beforeSlotWrite
      (writeTarget before active (before active.other))
  | uncertainOld : Survivor before active next .slotWriteUncertain
      (writeTarget before active (before active.other))
  | uncertainInvalid : Survivor before active next .slotWriteUncertain
      (writeTarget before active none)
  | uncertainNew : Survivor before active next .slotWriteUncertain
      (writeTarget before active (some next))
  | synced : Survivor before active next .slotSynced
      (writeTarget before active (some next))

/-- WAL validation is required even for a slot whose record decodes correctly. -/
theorem recover_selected {valid : Frontier → Bool} {slots : Slots Frontier}
    {record : Record Frontier}
    (selected : selectNewest (slots .first) (slots .second) = .ok record) :
    recover valid slots = if valid record.frontier then .ok record else .error .invalidFrontier := by
  simp only [recover, selected, Bind.bind, Except.bind, Pure.pure, Except.pure]
  split <;> rfl

theorem recover_targetNew (before : Slots Frontier) (active : Slot)
    {old next : Record Frontier} (valid : Frontier → Bool)
    (present : before active = some old) (newer : old.epoch < next.epoch) :
    recover valid (writeTarget before active (some next)) =
      if valid next.frontier then .ok next else .error .invalidFrontier := by
  apply recover_selected
  rw [select_written before active present]
  simp [selectNewest, newer]

/-- A decodable newer record with an invalid frontier fails closed even
when the previous active frontier still validates. -/
theorem recover_targetNew_invalid (before : Slots Frontier) (active : Slot)
    {old next : Record Frontier} (valid : Frontier → Bool)
    (present : before active = some old) (newer : old.epoch < next.epoch)
    (invalid : valid next.frontier = false) :
    recover valid (writeTarget before active (some next)) = .error .invalidFrontier := by
  simpa [invalid] using recover_targetNew before active valid present newer

theorem recover_targetOld (before : Slots Frontier) (active : Slot)
    {old : Record Frontier} (valid : Frontier → Bool)
    (present : before active = some old) (intact : valid old.frontier = true)
    (older : ∀ stale, before active.other = some stale → stale.epoch < old.epoch) :
    recover valid (writeTarget before active (before active.other)) = .ok old := by
  have chosen := select_written before active present (before active.other)
  rw [select_older old (before active.other) older] at chosen
  simpa [intact] using recover_selected (valid := valid) chosen

theorem recover_targetInvalid (before : Slots Frontier) (active : Slot)
    {old : Record Frontier} (valid : Frontier → Bool)
    (present : before active = some old) (intact : valid old.frontier = true) :
    recover valid (writeTarget before active none) = .ok old := by
  have chosen := select_written before active present none
  simpa [selectNewest, intact] using recover_selected (valid := valid) (chosen.trans rfl)

theorem Survivor.keepsActive {before after : Slots Frontier} {active : Slot}
    {next : Record Frontier} {phase : Phase}
    (report : Survivor before active next phase after) :
    after active = before active := by
  cases report <;> apply writeTarget_keepsActive

/-- Before a slot write is dispatched, its previous bytes still select the
old frontier. During the uncertain phase either the old or complete new
frontier can be recovered. The report for a durable slot sync selects new.
The WAL-side premises require the corresponding frontier to validate in
this very crash image. -/
theorem Survivor.recovery {before after : Slots Frontier} {active : Slot}
    {old next : Record Frontier} {phase : Phase} (valid : Frontier → Bool)
    (report : Survivor before active next phase after)
    (present : before active = some old)
    (older : ∀ stale, before active.other = some stale → stale.epoch < old.epoch)
    (newer : old.epoch < next.epoch)
    (intact : valid old.frontier = true)
    (walOrdered : phase = .slotWriteUncertain ∨ phase = .slotSynced →
      valid next.frontier = true) :
    match phase with
    | .beforeWalSync | .beforeSlotWrite => recover valid after = .ok old
    | .slotWriteUncertain => recover valid after = .ok old ∨ recover valid after = .ok next
    | .slotSynced => recover valid after = .ok next := by
  cases report with
  | beforeWalSync | beforeSlotWrite => exact recover_targetOld before active valid present intact older
  | uncertainOld => exact Or.inl (recover_targetOld before active valid present intact older)
  | uncertainInvalid => exact Or.inl (recover_targetInvalid before active valid present intact)
  | uncertainNew =>
    exact Or.inr (by simpa [walOrdered (Or.inl rfl)] using
      recover_targetNew before active valid present newer)
  | synced =>
    simpa [walOrdered (Or.inr rfl)] using recover_targetNew before active valid present newer

/-- Acknowledgment is recorded only after the target sync succeeds. It binds
the exact durable update, as well as the next frontier's admissibility. -/
theorem acknowledged_exact {before after : Slots Frontier} {active : Slot}
    {old next : Record Frontier} (valid : Frontier → Bool)
    (report : Survivor before active next .slotSynced after)
    (present : before active = some old) (newer : old.epoch < next.epoch)
    (walSynced : valid next.frontier = true) :
    after active = some old ∧ after active.other = some next ∧ recover valid after = .ok next := by
  cases report
  exact ⟨(writeTarget_keepsActive ..).trans present, writeTarget_updatesOther ..,
    by simpa [walSynced] using recover_targetNew before active valid present newer⟩

end Alvoki.WAL.OrderedTwoSlot
