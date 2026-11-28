import Alvoki.Experiments.SortedRun.SSTableProofs

namespace SortedRun.EffectsCheck

open ImmutableSSTable ImmutableSSTable.Unified

private abbrev SourceM := EStateM String Nat

private def newer (index : Nat) : SourceM (Option (Entry × Nat)) := fun reached =>
  if index == 0 then .ok (some (⟨⟨#[1]⟩, ⟨#[7]⟩⟩, 1)) (reached + 1)
  else .error "required read failed" (reached + 100)

private def older (_ : Nat) : SourceM (Option (Entry × Nat)) := fun reached =>
  .ok (some (⟨⟨#[2]⟩, ⟨#[8]⟩⟩, 1)) (reached + 10)

private def ops : OutputOps SourceM Unit :=
  { openFile := fun _ _ reached => .ok () (reached + 1)
    append := fun _ _ reached => .ok () (reached + 10000)
    flush := fun _ reached => .ok () (reached + 20000)
    sync := fun _ reached => .ok () (reached + 30000)
    remove := fun _ reached => .error "cleanup also failed" (reached + 1000) }

private def front : Frontier Nat Nat Entry := Frontier.start 0 0

private def issued : Frontier Nat Nat Entry :=
  ⟨.unread 1, .buffered (some (⟨⟨#[2]⟩, ⟨#[8]⟩⟩, 1))⟩

/-- The checked callback schedule emits a row before the failing cursor
step. This also fixes which unread cursor and buffered loser reach the error. -/
theorem first_row :
    next Entry.key (liftPull newer) (liftPull older) effectSlot (front, 1) =
      .ok (some ⟨⟨#[1]⟩, ⟨#[7]⟩⟩) (issued, 12) := by
  rw [next_effect]
  rfl

/-- The real build runs cleanup at the read's reached state, keeps the
primary error even if cleanup fails and performs no finish or sync. -/
theorem read_error_after_row :
    buildMergedWith Entry.key id (liftPull newer) (liftPull older) effectSlot
        (liftOutput ops) (fun _ bytes => bytes.size.toUInt32) "fresh"
        ⟨none, none, 31⟩ id {} (front, 0) =
      .error "required read failed" (issued, 1112) := by
  rfl

end SortedRun.EffectsCheck
