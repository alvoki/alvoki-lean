import Alvoki.Experiments.WAL.Segmented.Proofs.Publication
import Alvoki.Experiments.WAL.Segmented.Proofs.Invariant

namespace WalRecoverySlice.Segmented

open Model

/-- A selected file stays named in both directories even when unrelated
files have different live and durable bindings. -/
theorem Model.RotationCut.keepsNamed {d ss after} (cut : RotationCut d ss after)
    (id : Nat) (old : id ≠ (successor ss).active)
    (named : id ∈ d.liveNames ∧ id ∈ d.durableNames) :
    after.segment id = d.segment id ∧ after.cursor id = d.cursor id ∧
      id ∈ after.liveNames ∧ id ∈ after.durableNames := by
  cases cut with
  | before => exact ⟨rfl, rfl, named⟩
  | prepared persist =>
    cases persist <;> simp [Disk.prepare, Disk.setSegment, named.1, named.2, old]
  | publishing cut =>
    obtain ⟨seg, cur, live, durable, _⟩ := cut.frames
    rw [seg, cur, live]
    rcases durable with eqn | eqn <;> rw [eqn] <;>
      simp [Disk.preparedSuccessor, Disk.syncRoot, Disk.prepare, Disk.setSegment, old, named.1]

theorem Model.RotationCut.controlChoices {d ss after} (cut : RotationCut d ss after)
    (live : d.liveControl = some ss.control) (durable : d.durableControl = some ss.control) :
    (after.liveControl = some ss.control ∧ after.durableControl = some ss.control) ∨
    (after.liveControl = some (successor ss) ∧
      (after.durableControl = some ss.control ∨ after.durableControl = some (successor ss))) := by
  cases cut with
  | before => exact .inl ⟨live, durable⟩
  | prepared _ => exact .inl ⟨live, durable⟩
  | publishing cut =>
    simpa [Disk.preparedSuccessor, Disk.syncRoot, Disk.prepare, Disk.setSegment, live] using cut.frames.2.2.2.2

private theorem oldLayout {d c history after} (entry : ReadyLayout c history d)
    (cut : RotationCut d (sessionOf c history) after) : ReadyLayout c history after := by
  have kept (id : Nat) (selected : c.selects id) :=
    cut.keepsNamed id (by
      change id ≠ c.active + 1
      have := selected.2; omega) (entry.layout.names id selected)
  exact entry.frame (fun id sel => (kept id sel).2.2) (fun id sel => (kept id sel).1)
    (kept c.active c.selectsActive).2.1

private theorem newLayout {d c history after} (entry : ReadyLayout c history d)
    (live : d.liveControl = some c) (durable : d.durableControl = some c)
    (full : (segmentHistory c.capacity c.active history).length = c.capacity)
    (cut : RotationCut d (sessionOf c history) after)
    (chosen : after.liveControl = some (successor (sessionOf c history)) ∨
      after.durableControl = some (successor (sessionOf c history))) :
    ReadyLayout (successor (sessionOf c history)) history after := by
  have ready := oldLayout entry cut
  obtain ⟨ln, dn, empty, cursor⟩ := cut.successor_ready live durable chosen
  exact ready.rotate full ready.layout.names (fun _ _ => rfl) ⟨ln, dn⟩ empty cursor

private theorem rotationStopped {s : State} {c history after} (batch : Bytes)
    (entry : ReadyLayout c history s.disk) (live : s.disk.liveControl = some c)
    (durable : s.disk.durableControl = some c) (full : (segmentHistory c.capacity c.active history).length = c.capacity)
    (cut : RotationCut s.disk (sessionOf c history) after) :
    Recoverable (historyView c history) (some (.append batch)) after := by
  have old := (oldLayout entry cut).choice (request := some (.append batch)) (.inl rfl)
  rcases cut.controlChoices live durable with ⟨a,b⟩ | ⟨a,b⟩
  · exact ⟨⟨_, a, old⟩, ⟨_, b, old⟩⟩
  · have next := (newLayout entry live durable full cut (.inl a)).choice
        (known := historyView c history) (request := some (.append batch)) (.inl rfl)
    exact ⟨⟨_, a, next⟩, b.elim (fun h => ⟨_, h, old⟩) (fun h => ⟨_, h, next⟩)⟩

/-- The child append starts with room at the returned active ID. If rotation
stops first, both admissible controls still explain the original client view. -/
theorem rotateIfFull_refines (e : Effects) (c : Control) (history : List Bytes) (p : Bytes) (s : State)
    (entry : ReadyLayout c history s.disk) (live : s.disk.liveControl = some c) (durable : s.disk.durableControl = some c) :
    DiskPost (fun pair d => ReadyLayout pair.1 history d ∧ d.liveControl = some pair.1 ∧
      d.durableControl = some pair.1 ∧ pair.2 = (segmentHistory pair.1.capacity pair.1.active history).length ∧
      historyView pair.1 history = historyView c history ∧ history.length < (pair.1.active+1)*pair.1.capacity)
      (Recoverable (historyView c history) (some (.append p))) ((rotateIfFull (ops e) (sessionOf c history)).run s) := by
  let ss := sessionOf c history
  by_cases full : ss.activeCount = ss.control.capacity
  · have classified := rotateIfFull_cases e ss s
    simp only [full, ↓reduceIte] at classified
    change DiskPost _ _ ((rotateIfFull (ops e) ss).run s)
    generalize hr : (rotateIfFull (ops e) ss).run s = r at classified ⊢
    cases r with
    | error _ t => exact rotationStopped p entry live durable full classified
    | ok result t => cases result with
      | error _ => exact rotationStopped p entry live durable full classified
      | ok pair =>
        obtain ⟨rfl, after⟩ := classified
        have cut : RotationCut s.disk ss t.disk := after ▸ .publishing .settled
        have chosen : t.disk.liveControl = some (successor ss) := by rw [after]; rfl
        have ready := newLayout entry live durable full cut (.inl chosen)
        refine ⟨ready, chosen, by rw [after]; rfl, ?_, rfl, ?_⟩
        · change 0 = (segmentHistory c.capacity (c.active + 1) history).length
          rw [segmentHistory_next_empty entry.layout.upper]; rfl
        · change history.length < (c.active + 1 + 1) * c.capacity
          rw [Nat.add_mul, Nat.one_mul]
          have := entry.layout.upper
          have := entry.layout.capacityPositive
          omega
  · change DiskPost _ _ ((rotateIfFull (ops e) ss).run s)
    simp only [rotateIfFull, full, ↓reduceIte]
    refine ⟨entry, live, durable, rfl, rfl, ?_⟩
    change (segmentHistory c.capacity c.active history).length ≠ c.capacity at full
    rw [segmentHistory_active_length entry.layout.upper] at full
    have hi := entry.layout.upper
    have lo := entry.layout.lower
    change history.length < (c.active + 1) * c.capacity
    rw [Nat.add_mul, Nat.one_mul] at hi ⊢
    omega

end WalRecoverySlice.Segmented
