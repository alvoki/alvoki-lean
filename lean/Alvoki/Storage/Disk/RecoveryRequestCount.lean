namespace Alvoki.Storage.RecoveryRequestCount

/-- Charge an adapter request even when its report is an error. -/
noncomputable def issued (report : Except IO.Error α) : EStateM IO.Error Nat α :=
  fun before => match report with
    | .ok value => .ok value (before + 1)
    | .error cause => .error cause (before + 1)

/-- Both success and failure retain the number of issued requests. -/
noncomputable def reached : EStateM.Result IO.Error Nat α → Nat
  | .ok _ count | .error _ count => count

theorem reached_issued (report : Except IO.Error α) (before : Nat) :
    reached (issued report before) = before + 1 := by
  cases report <;> rfl

theorem bind_bound {run : EStateM IO.Error Nat α} {next : α → EStateM IO.Error Nat β}
    {before first second : Nat} (start : reached (run before) ≤ before + first)
    (later : ∀ value after, run before = .ok value after → reached (next value after) ≤ after + second) :
    reached ((run >>= next) before) ≤ before + (first + second) := by
  cases outcome : run before with
  | error cause after =>
    simp only [outcome, reached] at start
    simp only [Bind.bind, EStateM.bind, outcome, reached]
    omega
  | ok value after =>
    have remains := later value after outcome
    simp only [outcome, reached] at start
    simp only [Bind.bind, EStateM.bind, outcome]
    omega

theorem bind_pure_reached (run : EStateM IO.Error Nat α) (transform : α → β) (before : Nat) :
    reached ((run >>= fun value => pure (transform value)) before) = reached (run before) := by
  cases outcome : run before <;> simp [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, outcome, reached]

/-- Sum item-specific budgets along the ordered loop. If an action
fails, the remaining actions perform no work. -/
theorem mapM_weightedBound (run : α → EStateM IO.Error Nat β) (items : List α)
    (cost : α → Nat) (before : Nat)
    (each : ∀ item count, reached (run item count) ≤ count + cost item) :
    reached ((items.mapM run) before) ≤ before + (items.map cost).sum := by
  induction items generalizing before with
  | nil => simp [Pure.pure, EStateM.pure, reached]
  | cons item rest ih =>
    simp only [List.mapM_cons, List.map_cons, List.sum_cons]
    apply bind_bound (each item before)
    intro value after _
    rw [bind_pure_reached]
    exact ih after

theorem mapM_bound (run : α → EStateM IO.Error Nat β) (items : List α) (before budget : Nat)
    (each : ∀ item count, reached (run item count) ≤ count + budget) :
    reached ((items.mapM run) before) ≤ before + budget * items.length := by
  simpa [List.map_const', List.sum_replicate_nat, Nat.mul_comm] using mapM_weightedBound run items (fun _ => budget) before each

theorem forM_bound (run : α → EStateM IO.Error Nat Unit) (items : List α) (before budget : Nat)
    (each : ∀ item count, reached (run item count) ≤ count + budget) :
    reached ((items.forM run) before) ≤ before + budget * items.length := by
  induction items generalizing before with
  | nil => simp [List.forM, Pure.pure, EStateM.pure, reached]
  | cons item rest ih =>
    simp only [List.forM, List.length_cons, Nat.mul_succ]
    rw [Nat.add_comm (budget * rest.length) budget]
    exact bind_bound (each item before) (fun _ after _ => ih after)

end Alvoki.Storage.RecoveryRequestCount
