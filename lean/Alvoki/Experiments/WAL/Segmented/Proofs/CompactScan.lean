import Alvoki.Experiments.WAL.Segmented.Native
import Alvoki.Experiments.WAL.Segmented.Proofs.Invariant

namespace WalRecoverySlice.Segmented.Native

/-- The disk, ready state and owned resources can all be included in `σ`.
Only a successful scan contributes a history observation to the client trace. -/
def ReadOutcome (healthy : Prop) (before : σ) (value : α) : EStateM.Result ε σ α → Prop
  | .ok seen after => seen = value ∧ after = before
  | .error _ after => after = before ∧ ¬healthy

private theorem ReadOutcome.bind
    {a : EStateM ε σ α} {k : α → EStateM ε σ β} {before : σ} {value : α} {expected : β}
    (source : ReadOutcome healthy before value (a before))
    (rest : ReadOutcome healthy before expected (k value before)) :
    ReadOutcome healthy before expected ((a >>= k) before) := by
  cases ran : a before with
  | error error after =>
    simpa [Bind.bind, EStateM.bind, ran, ReadOutcome] using source
  | ok seen after =>
    have same : seen = value ∧ after = before := by simpa [ran, ReadOutcome] using source
    obtain ⟨rfl, rfl⟩ := same
    simpa [Bind.bind, EStateM.bind, ran] using rest

theorem foldSealedWith_read
    (read : Nat → α → EStateM ε σ α) (expected : Nat → α → α)
    (before : σ) (healthy : Prop)
    (reads : ∀ id acc, ReadOutcome healthy before (expected id acc) (read id acc before))
    (first count : Nat) (seed : α) :
    ReadOutcome healthy before (foldSealedWith (m := Id) expected first count seed)
      (foldSealedWith read first count seed before) := by
  induction count generalizing first seed with
  | zero => exact ⟨rfl, rfl⟩
  | succ count ih =>
    exact ReadOutcome.bind (reads first seed) (ih (first + 1) (expected first seed))

/-- Composition for the shared scan schedule. Its primitive premises account
for scoped acquisition/close and exact bytes. Healthy progress is conditional
on the reads at this installed snapshot, independently of error framing. -/
theorem scanReadyWith_read
    (session : CompactSession) (seed : α) (readSealed : Nat → α → EStateM ε σ α)
    (readActive : α → EStateM ε σ α) (sealed : Nat → α → α) (active : α → α)
    (before : σ) (healthy : Prop)
    (sealedReads : ∀ id acc, ReadOutcome healthy before (sealed id acc) (readSealed id acc before))
    (activeRead : ∀ acc, ReadOutcome healthy before (active acc) (readActive acc before)) :
    ReadOutcome healthy before (scanReadyWith (m := Id) session seed sealed active)
      (scanReadyWith session seed readSealed readActive before) := by
  apply ReadOutcome.bind (foldSealedWith_read readSealed sealed before healthy sealedReads _ _ _)
  exact ReadOutcome.bind (activeRead _) ⟨rfl, rfl⟩

theorem ReadOutcome.healthy
    {result : EStateM.Result ε σ α} (h : ReadOutcome available before expected result)
    (progress : available) : result = .ok expected before := by
  cases result with
  | error _ _ => exact False.elim (h.2 progress)
  | ok _ _ => obtain ⟨rfl, rfl⟩ := h; rfl

open SingleFile (foldBatchesFrom foldBatches)

private theorem fold_append (step : α → Nat → Bytes → α) (base : Nat) (seed : α)
    (left right : List Bytes) :
    foldBatchesFrom step base seed (left ++ right) =
      foldBatchesFrom step (base + left.length) (foldBatchesFrom step base seed left) right := by
  induction left generalizing base seed with
  | nil => simp [foldBatchesFrom]
  | cons batch rest ih =>
    simp only [List.cons_append, foldBatchesFrom, List.length_cons, ih]
    congr 1
    omega

private theorem fold_offset (step : α → Nat → Bytes → α) (offset base : Nat)
    (seed : α) (batches : List Bytes) :
    foldBatchesFrom (fun acc pos batch => step acc (offset + pos) batch) base seed batches =
      foldBatchesFrom step (offset + base) seed batches := by
  induction batches generalizing base seed with
  | nil => rfl
  | cons batch rest ih => rw [foldBatchesFrom, foldBatchesFrom, ih, Nat.add_assoc]

private def after (cut : Nat) (step : α → Nat → Bytes → α) (acc : α)
    (position : Nat) (batch : Bytes) : α :=
  if cut < position then step acc position batch else acc

def foldChild (c : Control) (history : List Bytes) (step : α → Nat → Bytes → α)
    (id : Nat) (seed : α) : α :=
  foldBatches (segmentHistory c.capacity id history) seed (retainedStep c id step)

private theorem foldChild_eq (c : Control) (history : List Bytes)
    (step : α → Nat → Bytes → α) (id : Nat) (seed : α) :
    foldChild c history step id seed = foldBatchesFrom (after c.discarded step)
      (id * c.capacity) seed (segmentHistory c.capacity id history) := by
  have stepEq : retainedStep c id step = fun acc pos batch =>
      after c.discarded step acc (id * c.capacity + pos) batch := by
    funext acc pos batch
    rfl
  rw [foldChild, foldBatches, stepEq, fold_offset, Nat.add_zero]

private theorem fold_window (c : Control) (history : List Bytes)
    (step : α → Nat → Bytes → α) (first count : Nat) (seed : α)
    (full : (first + count) * c.capacity ≤ history.length) :
    foldSealedWith (m := Id) (foldChild c history step) first count seed =
      foldBatchesFrom (after c.discarded step) (first * c.capacity) seed
        (segmentWindow c.capacity first count history) := by
  induction count generalizing first seed with
  | zero => rfl
  | succ n ih =>
    have enough : (first + 1) * c.capacity ≤ history.length :=
      Nat.le_trans (Nat.mul_le_mul_right c.capacity (by omega)) full
    have rest : (first + 1 + n) * c.capacity ≤ history.length := by
      rwa [show first + 1 + n = first + (n + 1) by omega]
    change foldSealedWith (m := Id) (foldChild c history step) (first + 1) n
      (foldChild c history step first seed) = _
    rw [ih _ _ rest, segmentWindow, fold_append, segmentHistory_full enough,
      foldChild_eq, Nat.add_mul, Nat.one_mul]

private theorem fold_drop (cut base : Nat) (step : α → Nat → Bytes → α)
    (seed : α) (batches : List Bytes) :
    foldBatchesFrom (after cut step) base seed batches =
      foldBatchesFrom step (max cut base) seed (batches.drop (cut - base)) := by
  induction batches generalizing base seed with
  | nil => simp [foldBatchesFrom]
  | cons batch rest ih =>
    rw [foldBatchesFrom, ih]
    by_cases includeBatch : cut < base + 1
    · have leBase : cut ≤ base := by omega
      simp [after, includeBatch, Nat.max_eq_right leBase, Nat.sub_eq_zero_of_le leBase,
        Nat.max_eq_right (by omega : cut ≤ base + 1), Nat.sub_eq_zero_of_le (by omega : cut ≤ base + 1),
        foldBatchesFrom]
    · have advance : cut - base = (cut - (base + 1)) + 1 := by omega
      simp [after, includeBatch, advance, Nat.max_eq_left (by omega : base ≤ cut),
        Nat.max_eq_left (by omega : base + 1 ≤ cut)]

/-- Compose the native schedule's pure result over the exact selected child
histories. The consumer sees precisely the retained suffix with absolute IDs. -/
theorem scanReadyWith_selected (session : CompactSession) (history : List Bytes)
    (seed : α) (step : α → Nat → Bytes → α)
    (lower : session.control.active * session.control.capacity ≤ history.length)
    (upper : history.length ≤ (session.control.active + 1) * session.control.capacity) :
    scanReadyWith (m := Id) session seed (foldChild session.control history step)
      (foldChild session.control history step session.control.active) =
        (session.bounds, foldBatchesFrom step session.control.discarded seed
          (history.drop session.control.discarded)) := by
  let c := session.control
  change c.active * c.capacity ≤ history.length at lower
  change history.length ≤ (c.active + 1) * c.capacity at upper
  have first : c.firstNeeded ≤ c.active := Nat.min_le_left ..
  have exactSpan : c.firstNeeded + (c.active - c.firstNeeded) = c.active := by omega
  have fullSpan : (c.firstNeeded + (c.active - c.firstNeeded)) * c.capacity ≤ history.length := by
    rwa [exactSpan]
  have width : (segmentWindow c.capacity c.firstNeeded (c.active - c.firstNeeded) history).length =
      (c.active - c.firstNeeded) * c.capacity := by
    rw [segmentWindow_eq, List.length_take, List.length_drop, Nat.min_eq_left]
    have sum : c.firstNeeded * c.capacity + (c.active - c.firstNeeded) * c.capacity =
        c.active * c.capacity := by rw [← Nat.add_mul, exactSpan]
    omega
  have join : c.firstNeeded * c.capacity + (c.active - c.firstNeeded) * c.capacity =
      c.active * c.capacity := by rw [← Nat.add_mul, exactSpan]
  have retained : c.firstNeeded * c.capacity ≤ c.discarded :=
    Nat.le_trans (Nat.mul_le_mul_right c.capacity (Nat.min_le_right ..)) (Nat.div_mul_le_self ..)
  change (session.bounds, foldChild c history step c.active
      (foldSealedWith (m := Id) (foldChild c history step) c.firstNeeded
        (c.active - c.firstNeeded) seed)) = _
  rw [fold_window _ _ _ _ _ _ fullSpan, foldChild_eq]
  rw [← join, ← width, ← fold_append, fold_drop,
    Nat.max_eq_left retained, selectedHistory_eq c history upper]

theorem compactBounds_eq {session : Session} {disk : Model.Disk}
    (ready : Installed session disk) :
    (⟨session.control, session.activeCount⟩ : CompactSession).bounds =
      ⟨session.view.base, session.view.tail⟩ := by
  obtain ⟨history, shape, ready, _, _⟩ := ready
  have lower := ready.layout.lower
  have covered := ready.layout.discardedFits
  have count := segmentHistory_active_length (active := session.control.active) ready.layout.upper
  rw [shape]
  simp only [CompactSession.bounds, sessionOf]
  rw [historyView_tail covered, count]
  simp only [historyView]
  congr 1
  omega

end WalRecoverySlice.Segmented.Native
