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
