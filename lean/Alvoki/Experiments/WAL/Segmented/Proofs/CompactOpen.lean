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
  simp [withActiveChild, finishCompactRecoveryWith, cleanupOnError, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
    childRun, historyCursor, count, Nat.not_lt_of_ge cap, Nat.not_lt_of_ge release, CompactSession.bounds,
    collectedRun, registeredRun, foldEq, acc, compact, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch]

private theorem runCompactBind
    (a : ExceptT String (EStateM abort σ) v)
    (next : v → ExceptT String (EStateM abort σ) w) (before : σ) :
    (a >>= next).run before =
      match a.run before with
      | .ok (.ok value) after => (next value).run after
      | .ok (.error err) after => .ok (.error err) after
      | .error token after => .error token after := by
  change EStateM.bind a.run (ExceptT.bindCont next) before = _
  cases ran : a.run before with
  | error => simp [EStateM.bind, ran]
  | ok response after => cases response <;> simp [EStateM.bind, ran, ExceptT.bindCont] <;> rfl

/-- Expand the compact worker at the same cuts used by the root and child
reports. Reported errors close the exact acquired active child. A stop
passes through to the process-exit resource contract. -/
theorem recoverCompactWith_reached
    (select : ExceptT String (EStateM abort σ) Control)
    (openChild : Control → Nat → α → ExceptT String (EStateM abort σ) (child × Cursor × α))
    (close : child → ExceptT String (EStateM abort σ) Unit)
    (collect : Control → ExceptT String (EStateM abort σ) Unit)
    (register : Nat → child → ExceptT String (EStateM abort σ) Unit)
    (seed : α) (before : σ) :
    (recoverCompactWith id select openChild close collect register seed).run before =
      match select.run before with
      | .error token reached => .error token reached
      | .ok (.error err) reached => .ok (.error err) reached
      | .ok (.ok c) selected =>
        match (foldSealedWith
          (fun idx acc => recoverSealedWith id c.capacity (openChild c idx acc) close)
          c.firstNeeded (c.active - c.firstNeeded) seed).run selected with
        | .error token reached => .error token reached
        | .ok (.error err) reached => .ok (.error err) reached
        | .ok (.ok acc) walked =>
          match (openChild c c.active acc).run walked with
          | .error token reached => .error token reached
          | .ok (.error err) reached => .ok (.error err) reached
          | .ok (.ok (held, cursor, folded)) opened =>
            match (finishCompactRecoveryWith id collect register c (held, cursor, folded)).run opened with
            | .ok (.error err) reached =>
              match (close held).run reached with
              | .ok _ after => .ok (.error err) after
              | .error token after => .error token after
            | other => other := by
  rw [recoverCompactWith, runCompactBind]
  cases select.run before with
  | error => rfl
  | ok value selected =>
    cases value with
    | error => rfl
    | ok c =>
      dsimp only
      rw [runCompactBind]
      cases (foldSealedWith
        (fun idx acc => recoverSealedWith id c.capacity (openChild c idx acc) close)
        c.firstNeeded (c.active - c.firstNeeded) seed).run selected with
      | error => rfl
      | ok response walked =>
        cases response with
        | error => rfl
        | ok acc =>
          dsimp only
          have activeCut := withActiveChild_reached (openChild c c.active acc).run
            (fun (acquired : child × Cursor × α) => close acquired.1)
            (finishCompactRecoveryWith id collect register c) walked
          change (withActiveChild (error := String) (ExceptT.mk (openChild c c.active acc).run)
            (fun acquired => close acquired.1) (finishCompactRecoveryWith id collect register c)).run walked = _
          rw [activeCut]
          cases (openChild c c.active acc).run walked with
          | error => rfl
          | ok result opened =>
            cases result with
            | error => rfl
            | ok triple =>
              obtain ⟨held, cursor, folded⟩ := triple
              dsimp only
              cases (finishCompactRecoveryWith id collect register c (held, cursor, folded)).run opened with
              | error => rfl
              | ok response reached =>
                cases response with
                | ok => rfl
                | error =>
                  dsimp only
                  cases (close held).run reached with
                  | error => rfl
                  | ok response after =>
                    cases response with
                    | error => rfl
                    | ok value => cases value; rfl

open Model in
/-- Once the active cursor has passed the bounds checks, the native
continuation inherits the checked collection loop's disk frame at every
cut. Successful registration affects only the private active reference. -/
theorem finishCompactRecoveryWith_disk {callbacks : Ops Model.M} {ChildHandle : Type}
    (effects : CollectionEffects callbacks) (c : Control) (s : State)
    (held : ChildHandle) (cursor : Cursor) (folded : α)
    (count : cursor.nextSeq - 1 ≤ c.capacity)
    (released : c.discarded ≤ (⟨c, cursor.nextSeq - 1⟩ : CompactSession).bounds.tail)
    (register : Nat → ChildHandle → Model.M Unit)
    (registered : ∀ t, (register c.active held).run t =
      .ok (.ok ()) {t with activeEntry := some c.active}) :
    DiskPost (fun result disk =>
      result = (⟨c, cursor.nextSeq - 1⟩, folded) ∧
      CollectionFrame c.firstNeeded s.disk disk ∧
      disk.durableControl = disk.liveControl ∧ disk.durableNames = disk.liveNames ∧
      ∀ id ∈ disk.liveNames, c.firstNeeded ≤ id)
      (CollectionFrame c.firstNeeded s.disk)
      ((finishCompactRecoveryWith id (Segmented.collect callbacks.toRootOps) register c
        (held, cursor, folded)).run s) := by
  unfold finishCompactRecoveryWith
  dsimp only
  simp only [Nat.not_lt_of_ge count, Nat.not_lt_of_ge released, ↓reduceIte]
  apply bindPost (collectWith_cases effects c s)
  intro value reached frame
  cases value
  rw [runCompactBind, registered]
  exact ⟨rfl, frame⟩

end WalRecoverySlice.Segmented.Native
