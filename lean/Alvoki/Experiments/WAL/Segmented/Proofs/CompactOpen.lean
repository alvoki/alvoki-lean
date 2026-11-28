import Alvoki.Experiments.WAL.Segmented.Proofs.CompactScan
import Alvoki.Experiments.WAL.Segmented.Proofs.NativeAppend

namespace WalRecoverySlice.Segmented.Native
open Persistence
open SingleFile (foldBatchesFrom)

/-- The healthy compact worker closes each exact sealed child before moving
on. This proof uses the cursor and fold from local child open, never a list
returned to or retained by the segmented executable. -/
theorem recoverCompactWith_delivers
    (select : EStateM String σ Control)
    (openChild : Control → Nat → α → EStateM String σ (child × Cursor × α))
    (close : child → EStateM String σ Unit) (collect : Control → EStateM String σ Unit)
    (register : Nat → child → EStateM String σ Unit) (inv : σ → Prop)
    (ready : Control → child → σ → Prop) (history : List Bytes)
    (seed : α) (step : α → Nat → Bytes → α)
    (before selected : σ) (c : Control)
    (picked : select before = .ok c selected) (admissible : inv selected)
    (lower : c.active * c.capacity ≤ history.length)
    (upper : history.length ≤ (c.active + 1) * c.capacity)
    (discarded : c.discarded ≤ history.length)
    (sealed : ∀ id, c.firstNeeded ≤ id → id < c.active → ∀ acc s, inv s →
      ∃ held opened released,
        openChild c id acc s = .ok
          (held, historyCursor (segmentHistory c.capacity id history), foldChild c history step id acc) opened ∧
        close held opened = .ok () released ∧ inv released)
    (active : ∀ acc s, inv s → ∃ held opened collected registered,
      openChild c c.active acc s = .ok
        (held, historyCursor (segmentHistory c.capacity c.active history),
          foldChild c history step c.active acc) opened ∧
      collect c opened = .ok () collected ∧ register c.active held collected = .ok () registered ∧
      ready c held registered) :
    ∃ held after,
      recoverCompactWith id select openChild close collect register seed before =
        .ok (⟨c, history.length - c.active * c.capacity⟩,
          foldBatchesFrom step c.discarded seed (history.drop c.discarded)) after ∧ ready c held after := by
  let readSealed (idx : Nat) (acc : α) : EStateM String σ α :=
    recoverSealedWith id c.capacity (openChild c idx acc) close
  have each (first count : Nat) (start : σ) (seed' : α)
      (startOk : inv start) (lo : c.firstNeeded ≤ first) (hi : first + count ≤ c.active) :
      ∃ finish, foldSealedWith readSealed first count seed' start =
        .ok (foldSealedWith (m := Id) (foldChild c history step) first count seed') finish ∧ inv finish := by
    induction count generalizing first start seed' with
    | zero => exact ⟨start, rfl, startOk⟩
    | succ n ih =>
      obtain ⟨held, opened, released, ran, closed, kept⟩ := sealed first lo (by omega) seed' start startOk
      have full : (segmentHistory c.capacity first history).length = c.capacity :=
        segmentHistory_full (Nat.le_trans (Nat.mul_le_mul_right c.capacity (by omega)) lower)
      have leaf : readSealed first seed' start = .ok (foldChild c history step first seed') released := by
        simp [readSealed, recoverSealedWith, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, ran, closed, historyCursor, full,
          Nat.add_comm]
      obtain ⟨finish, result, final⟩ := ih (first + 1) released (foldChild c history step first seed')
        kept (by omega) (by omega)
      exact ⟨finish, by simpa only [foldSealedWith, Bind.bind, EStateM.bind, leaf] using result, final⟩
  let acc := foldSealedWith (m := Id) (foldChild c history step) c.firstNeeded (c.active - c.firstNeeded) seed
  have first : c.firstNeeded ≤ c.active := Nat.min_le_left ..
  obtain ⟨sealedAfter, walk, kept⟩ := each c.firstNeeded (c.active - c.firstNeeded) selected seed admissible
    (Nat.le_refl _) (by omega)
  obtain ⟨held, opened, collected, registered, childRun, collectedRun, registeredRun, owns⟩ :=
    active acc sealedAfter kept
  have count := segmentHistory_active_length (active := c.active) upper
  have cap : history.length - c.active * c.capacity ≤ c.capacity := by
    rw [Nat.add_mul, Nat.one_mul] at upper
    omega
  have release : c.discarded ≤ c.active * c.capacity + (history.length - c.active * c.capacity) := by omega
  let compact : CompactSession := ⟨c, history.length - c.active * c.capacity⟩
  have foldEq := congrArg Prod.snd (scanReadyWith_selected compact history seed step lower upper)
  change foldChild c history step c.active acc = _ at foldEq
  refine ⟨held, registered, ?_, owns⟩
  change foldSealedWith
    (fun idx acc => recoverSealedWith id c.capacity (openChild c idx acc) close)
    c.firstNeeded (c.active - c.firstNeeded) seed selected = .ok acc sealedAfter at walk
  simp only [recoverCompactWith, Bind.bind, EStateM.bind, picked, walk]
  simp [withActiveChild, cleanupOnError, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
    childRun, historyCursor, count, Nat.not_lt_of_ge cap, Nat.not_lt_of_ge release, CompactSession.bounds,
    collectedRun, registeredRun, foldEq, acc, compact, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch]

/-- A reported failure is propagated from its reached state, after closing
the child acquired by that invocation. A cleanup error is secondary. -/
theorem withActiveChild_reportedFailure
    (acquire : EStateM ε σ child) (close : child → EStateM ε σ Unit)
    (resume : child → EStateM ε σ α)
    (acquired : acquire before = .ok held opened)
    {reachedState : σ} (failed : resume held opened = .error primary reachedState) :
    withActiveChild (error := ε) acquire close resume before =
      .error primary (match close held reachedState with
        | .ok () after | .error _ after => after) := by
  cases outcome : close held reachedState with
  | ok done after =>
    cases done
    simp only [withActiveChild, cleanupOnError, Bind.bind, EStateM.bind, acquired, failed,
      outcome, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch,
      EStateM.Backtrackable.restore, EStateM.dummyRestore]
    rfl
  | error error after =>
    simp only [withActiveChild, cleanupOnError, Bind.bind, EStateM.bind, acquired, failed,
      outcome, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch,
      EStateM.Backtrackable.restore, EStateM.dummyRestore, Pure.pure, EStateM.pure]
    rfl

end WalRecoverySlice.Segmented.Native
