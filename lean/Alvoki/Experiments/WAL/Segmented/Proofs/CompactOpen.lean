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

namespace WalRecoverySlice.Segmented.Native
open Persistence
open SingleFile (foldBatchesFrom)

abbrev CompactRecoveryM (stop world : Type) := ExceptT String (EStateM stop world)

/-- A reported I/O error unwinds the scopes. An interruption observes their
last reached state and transfers the resources to process-exit custody. -/
def CompactPost (success : α → σ → Prop) (failed stopped : σ → Prop) :
    EStateM.Result abort σ (Except String α) → Prop
  | .ok (.ok value) after => success value after
  | .ok (.error _) after => failed after
  | .error _ after => stopped after

private theorem CompactPost.bind
    {a : CompactRecoveryM abort σ α} {next : α → CompactRecoveryM abort σ β}
    {before : σ} {P : α → σ → Prop} {Q : β → σ → Prop} {F S : σ → Prop}
    (first : CompactPost P F S (a.run before))
    (rest : ∀ value after, P value after → CompactPost Q F S ((next value).run after)) :
    CompactPost Q F S ((a >>= next).run before) := by
  rw [runCompactBind]
  cases ran : a.run before with
  | error => simpa only [ran, CompactPost] using first
  | ok response after =>
    rw [ran] at first
    cases response with
    | error => exact first
    | ok value => exact rest value after first

private theorem CompactPost.map
    {result : EStateM.Result abort σ (Except String α)}
    {P Q : α → σ → Prop} {F G S T : σ → Prop}
    (post : CompactPost P F S result) (ok : ∀ value after, P value after → Q value after)
    (error : ∀ after, F after → G after) (stop : ∀ after, S after → T after) :
    CompactPost Q G T result := by
  cases result with
  | error _ after => exact stop after post
  | ok response after =>
    cases response with
    | error => exact error after post
    | ok value => exact ok value after post

/-- A sealed child is acquired and folded once. Check the returned cursor
after releasing its exact handle, even if a caller supplied a malformed
child report. On a reported open failure no handle is available to close. -/
theorem recoverSealedWith_post
    {openChild : CompactRecoveryM abort σ (child × Cursor × α)}
    (close : child → CompactRecoveryM abort σ Unit) (capacity : Nat)
    (before : σ) (expected : α) (owned : child → σ → Prop) (ready failed stopped : σ → Prop)
    (openPost : CompactPost
      (fun out after => owned out.1 after ∧ out.2.1.nextSeq = capacity + 1 ∧ out.2.2 = expected)
      failed stopped (openChild.run before))
    (closePost : ∀ held after, owned held after →
      CompactPost (fun _ state => ready state) failed stopped ((close held).run after)) :
    CompactPost (fun out after => ready after ∧ out = expected) failed stopped
      ((recoverSealedWith id capacity openChild close).run before) := by
  unfold recoverSealedWith
  apply CompactPost.bind openPost
  rintro ⟨held, cursor, folded⟩ after ⟨owns, next, rfl⟩
  apply CompactPost.bind (closePost held after owns)
  intro value released kept
  change cursor.nextSeq = capacity + 1 at next
  simp only [next, beq_self_eq_true, ↓reduceIte]
  exact ⟨kept, rfl⟩

/-- The sealed prefix shares one deterministic position-indexed fold with
scan. Each local scope starts in the state reached by the preceding release. -/
theorem foldSealedWith_post
    (read : Nat → α → CompactRecoveryM abort σ α) (expected : Nat → α → α)
    (first count : Nat) (seed : α) (before : σ) (ready failed stopped : σ → Prop)
    (start : ready before)
    (reads : ∀ idx, first ≤ idx → idx < first + count → ∀ acc state, ready state →
      CompactPost (fun value after => ready after ∧ value = expected idx acc)
        failed stopped ((read idx acc).run state)) :
    CompactPost
      (fun value after => ready after ∧ value = foldSealedWith (m := Id) expected first count seed)
      failed stopped ((foldSealedWith read first count seed).run before) := by
  induction count generalizing first seed before with
  | zero => exact ⟨start, rfl⟩
  | succ count ih =>
    rw [foldSealedWith]
    apply CompactPost.bind (reads first (by omega) (by omega) seed before start)
    rintro _ after ⟨kept, rfl⟩
    exact ih (first + 1) (expected first seed) after kept
      (fun idx low high => reads idx (by omega) (by omega))

end WalRecoverySlice.Segmented.Native

namespace WalRecoverySlice.Segmented.Native
open Persistence
open SingleFile (foldBatchesFrom)

private theorem CompactPost.withActive
    (acquire : CompactRecoveryM abort σ child)
    (close : child → CompactRecoveryM abort σ Unit)
    (resume : child → CompactRecoveryM abort σ α)
    (before : σ) (held cleanup : child → σ → Prop)
    (ready : α → σ → Prop) (failed stopped : σ → Prop)
    (acquired : CompactPost held failed stopped (acquire.run before))
    (run : ∀ h s, held h s → CompactPost ready (cleanup h) stopped ((resume h).run s))
    (closed : ∀ h s, cleanup h s →
      CompactPost (fun _ => failed) failed stopped ((close h).run s)) :
    CompactPost ready failed stopped ((withActiveChild (error := String) acquire close resume).run before) := by
  change CompactPost ready failed stopped
    ((withActiveChild (error := String) (ExceptT.mk acquire.run) close resume).run before)
  rw [withActiveChild_reached]
  cases opened : acquire.run before with
  | error => rw [opened] at acquired; exact acquired
  | ok outcome after =>
    rw [opened] at acquired
    cases outcome with
    | error => exact acquired
    | ok h =>
      dsimp only
      have result := run h after acquired
      cases ran : (resume h).run after with
      | error => rw [ran] at result; exact result
      | ok reply reached =>
        rw [ran] at result
        cases reply with
        | ok => exact result
        | error =>
          have released := closed h reached result
          dsimp only
          cases finished : (close h).run reached with
          | error => rw [finished] at released; exact released
          | ok response _ =>
            rw [finished] at released
            cases response with
            | error => exact released
            | ok done => cases done; exact released

/-- The active child determines the selected logical history. Its choice may
extend the last child, but the sealed range and its prior fold are fixed. -/
structure CompactSelection (c : Control) (prior final : List Bytes) : Prop where
  lower : c.active * c.capacity ≤ final.length
  upper : final.length ≤ (c.active + 1) * c.capacity
  released : c.discarded ≤ final.length
  sealed : ∀ idx, idx < c.active →
    segmentHistory c.capacity idx prior = segmentHistory c.capacity idx final

private theorem foldSelectedSealed (c : Control) (prior final : List Bytes)
    (step : α → Nat → Bytes → α) (first count : Nat) (seed : α)
    (bound : first + count ≤ c.active) (same : CompactSelection c prior final) :
    foldSealedWith (m := Id) (foldChild c prior step) first count seed =
      foldSealedWith (m := Id) (foldChild c final step) first count seed := by
  induction count generalizing first seed with
  | zero => rfl
  | succ n ih =>
    have leaf : foldChild c prior step first seed = foldChild c final step first seed := by
      simp only [foldChild, same.sealed first (by omega)]
    change foldSealedWith (m := Id) (foldChild c prior step) (first + 1) n _ =
      foldSealedWith (m := Id) (foldChild c final step) (first + 1) n _
    rw [leaf, ih _ _ (by omega)]

/-- The compact continuation checks the returned cursor before collection.
The postcondition for failed collection still owns this exact child. -/
private theorem finishCompactRecoveryWith_post
    (collect : Control → CompactRecoveryM abort σ Unit)
    (register : Nat → child → CompactRecoveryM abort σ Unit)
    (c : Control) (held : child) (cursor : Cursor) (folded : α) (before : σ)
    (count : cursor.nextSeq - 1 ≤ c.capacity)
    (released : c.discarded ≤ (⟨c, cursor.nextSeq - 1⟩ : CompactSession).bounds.tail)
    (collected cleanup stopped installed : σ → Prop)
    (collection : CompactPost (fun _ => collected) cleanup stopped ((collect c).run before))
    (registration : ∀ t, collected t →
      CompactPost (fun _ => installed) cleanup stopped ((register c.active held).run t)) :
    CompactPost (fun out after => installed after ∧ out = (⟨c, cursor.nextSeq - 1⟩, folded))
      cleanup stopped ((finishCompactRecoveryWith id collect register c (held, cursor, folded)).run before) := by
  unfold finishCompactRecoveryWith
  dsimp only
  simp only [Nat.not_lt_of_ge count, Nat.not_lt_of_ge released, ↓reduceIte]
  apply CompactPost.bind collection
  intro _ after kept
  apply CompactPost.bind (registration after kept)
  intro _ _ owned
  exact ⟨owned, rfl⟩

/-- Compose the executable compact worker from local stage reports. The
ghost history is recovered from the exact child that registration receives.
No hypothesis supplies the result of the entire recovery worker. -/
theorem recoverCompactWith_local
    (select : CompactRecoveryM abort σ Control)
    (openChild : Control → Nat → α → CompactRecoveryM abort σ (child × Cursor × α))
    (close : child → CompactRecoveryM abort σ Unit)
    (collect : Control → CompactRecoveryM abort σ Unit)
    (register : Nat → child → CompactRecoveryM abort σ Unit)
    (c : Control) (prior : List Bytes) (before : σ) (seed : α) (step : α → Nat → Bytes → α)
    (prefixReady failed stopped : σ → Prop)
    (sealedHeld : Nat → child → σ → Prop)
    (activeHeld : List Bytes → child → σ → Prop)
    (cleaned : List Bytes → child → σ → Prop)
    (installed : List Bytes → child → σ → Prop)
    (permitted : List Bytes → Prop)
    (selected : CompactPost (fun chosen after => chosen = c ∧ prefixReady after)
      failed stopped (select.run before))
    (sealedOpen : ∀ idx, c.firstNeeded ≤ idx → idx < c.active → ∀ acc s, prefixReady s →
      CompactPost
        (fun out after => sealedHeld idx out.1 after ∧ out.2.1.nextSeq = c.capacity + 1 ∧
          out.2.2 = foldChild c prior step idx acc)
        failed stopped ((openChild c idx acc).run s))
    (sealedClose : ∀ idx h s, sealedHeld idx h s →
      CompactPost (fun _ => prefixReady) failed stopped ((close h).run s))
    (activeOpen : ∀ acc s, prefixReady s →
      CompactPost (fun out after => ∃ final, CompactSelection c prior final ∧ permitted final ∧
        activeHeld final out.1 after ∧
        out.2.1 = historyCursor (segmentHistory c.capacity c.active final) ∧
        out.2.2 = foldChild c final step c.active acc)
        failed stopped ((openChild c c.active acc).run s))
    (collection : ∀ final h s, activeHeld final h s →
      CompactPost (fun _ => cleaned final h) (activeHeld final h) stopped ((collect c).run s))
    (registration : ∀ final h s, cleaned final h s →
      CompactPost (fun _ => installed final h) (activeHeld final h) stopped ((register c.active h).run s))
    (activeClose : ∀ final h s, activeHeld final h s →
      CompactPost (fun _ => failed) failed stopped ((close h).run s)) :
    CompactPost (fun out after => ∃ final held, permitted final ∧ installed final held after ∧
        out.1.control = c ∧ out.1.bounds = ⟨c.discarded, final.length⟩ ∧
        out.2 = foldBatchesFrom step c.discarded seed (final.drop c.discarded))
      failed stopped ((recoverCompactWith id select openChild close collect register seed).run before) := by
  unfold recoverCompactWith
  apply CompactPost.bind selected
  rintro chosen atRoot ⟨same, ready⟩
  subst chosen
  have first : c.firstNeeded ≤ c.active := Nat.min_le_left ..
  let read := fun idx acc => recoverSealedWith id c.capacity (openChild c idx acc) close
  have leaves (idx : Nat) (lo : c.firstNeeded ≤ idx)
      (hi : idx < c.firstNeeded + (c.active - c.firstNeeded)) (acc : α) (s : σ) (ps : prefixReady s) :=
    recoverSealedWith_post close c.capacity s (foldChild c prior step idx acc)
      (sealedHeld idx) prefixReady failed stopped (sealedOpen idx lo (by omega) acc s ps) (sealedClose idx)
  apply CompactPost.bind
    (foldSealedWith_post read (foldChild c prior step) c.firstNeeded (c.active - c.firstNeeded)
      seed atRoot prefixReady failed stopped ready leaves)
  rintro acc afterWalk ⟨retained, rfl⟩
  apply CompactPost.withActive (held := fun out after => ∃ final, CompactSelection c prior final ∧
      permitted final ∧ activeHeld final out.1 after ∧
      out.2.1 = historyCursor (segmentHistory c.capacity c.active final) ∧
      out.2.2 = foldChild c final step c.active
        (foldSealedWith (m := Id) (foldChild c prior step) c.firstNeeded (c.active - c.firstNeeded) seed))
    (cleanup := fun out after => ∃ final, activeHeld final out.1 after)
  · exact activeOpen _ _ retained
  · rintro ⟨held, cursor, folded⟩ opened ⟨final, layout, allowed, owns, exactCursor, exactFold⟩
    change cursor = historyCursor (segmentHistory c.capacity c.active final) at exactCursor
    subst cursor
    have used : (historyCursor (segmentHistory c.capacity c.active final)).nextSeq - 1 =
        final.length - c.active * c.capacity := by
      simp [historyCursor, segmentHistory_active_length layout.upper]
    have count : final.length - c.active * c.capacity ≤ c.capacity := by
      have upper := layout.upper
      rw [Nat.add_mul, Nat.one_mul] at upper
      omega
    let compact : CompactSession := ⟨c, (historyCursor (segmentHistory c.capacity c.active final)).nextSeq - 1⟩
    have exactBounds : compact.bounds = ⟨c.discarded, final.length⟩ := by
      have lower := layout.lower
      change CompactSession.bounds _ = _
      simp only [compact, CompactSession.bounds, used]
      congr 1
      omega
    have reached := finishCompactRecoveryWith_post collect register c held
      (historyCursor (segmentHistory c.capacity c.active final)) folded opened (used ▸ count)
      (show c.discarded ≤ compact.bounds.tail by rw [exactBounds]; exact layout.released)
      (cleaned final held) (activeHeld final held) stopped (installed final held)
      (collection final held opened owns) (registration final held)
    apply reached.map
    · rintro _ after ⟨registered, rfl⟩
      have fold := congrArg Prod.snd (scanReadyWith_selected compact final seed step layout.lower layout.upper)
      change foldChild c final step c.active
        (foldSealedWith (m := Id) (foldChild c final step) c.firstNeeded (c.active - c.firstNeeded) seed) = _ at fold
      have sealed := foldSelectedSealed c prior final step c.firstNeeded (c.active - c.firstNeeded)
        seed (by omega) layout
      exact ⟨final, held, allowed, registered, rfl, exactBounds, exactFold.trans ((congrArg _ sealed).trans fold)⟩
    · exact fun _ held => ⟨final, held⟩
    · exact fun _ h => h
  · rintro ⟨h, _, _⟩ after ⟨final, owns⟩
    exact activeClose final h after owns

end WalRecoverySlice.Segmented.Native

namespace WalRecoverySlice.Segmented.Native
open Persistence Model

/-- A compact child succeeds on the same survivor as the single-file
model. Use the abstract active-choice lemma already used by segmented
reopen to attach that survivor to the selected sealed range. -/
theorem compactActive_selected (dir : System.FilePath) (reports : SingleFile.OpenReports)
    (c : Control) (prior : List Bytes) (pending : Option Bytes) (disk : Disk)
    (source : Readable c prior pending disk)
    (allowed : ∀ final, WalRecoverySlice.Contract.Permitted prior pending final →
      PermittedView known req (historyView c final))
    (seed : α) (step : α → Nat → Bytes → α)
    (ran : SingleFile.openCompactModel dir c.policy reports {image := disk.segment c.active}
      seed (retainedStep c c.active step) = .ok (.ok (phase, cursor, folded)) after) :
    ∃ final, CompactSelection c prior final ∧ PermittedView known req (historyView c final) ∧
      ReadyLayout c final (disk.setSegment c.active after.image cursor) ∧
      after.held = true ∧
      phase = .active .lock ⟨SingleFile.appendFiles .writer .reader (SingleFile.markersFor c.policy), .reader⟩ cursor () ∧
      cursor = historyCursor (segmentHistory c.capacity c.active final) ∧
      folded = foldChild c final step c.active seed := by
  have result := SingleFile.openCompactModel_refines dir c.policy reports
    {image := disk.segment c.active} rfl source.active.dirty source.active.markers
    seed (retainedStep c c.active step)
  dsimp only at result
  rw [ran] at result
  obtain ⟨_, _, localHistory, permitted, ready, held, _, _, durable, pos, installed, fold⟩ := result
  have bounded : ∀ b ∈ localHistory, b.length ≤ 32 := by
    intro b member
    apply source.active.dirty.bounded b
    rcases permitted with rfl | rfl
    · exact List.mem_append_left _ member
    · exact member
  obtain ⟨final, reasonable, slice, sealed, extend⟩ := resolve_active source permitted bounded
  have shape := extend disk source.layout
  have moved : Layout c final (disk.setSegment c.active after.image cursor) :=
    shape.frame (by exact shape.names) (fun idx _ lt => by
      simp [Disk.setSegment, Nat.ne_of_lt lt])
  have clean : Child.Installed c.policy
      ((disk.setSegment c.active after.image cursor).segment c.active)
      ((disk.setSegment c.active after.image cursor).cursor c.active)
      (segmentHistory c.capacity c.active final) := by
    simpa only [Disk.setSegment, ↓reduceIte, slice] using
      (show Child.Installed c.policy after.image cursor localHistory from ⟨⟨ready, durable⟩, pos⟩)
  refine ⟨final, ⟨shape.lower, shape.upper, shape.discardedFits, fun i lt => (sealed i lt).symm⟩,
    allowed final reasonable, ⟨moved, clean⟩, held, installed, slice.symm ▸ pos, ?_⟩
  simpa only [foldChild, slice, SingleFile.foldBatches] using fold

/-- Actual CONTROL decoding and the following directory sync determine the
selected layout before a compact worker can enter any child scope. A lost
sync acknowledgement may already have made the selected CONTROL durable. -/
theorem selectControl_compactPost {callbacks : Ops Model.M} {healthyRoot : Prop}
    (root : OpenRootEffects callbacks healthyRoot) (start : State)
    (prior : Recoverable known req start.disk) (c : Control)
    (visible : start.disk.liveControl = some c)
    (source : Readable c history pending start.disk)
    (allowed : ∀ final, WalRecoverySlice.Contract.Permitted history pending final →
      PermittedView known req (historyView c final)) :
    CompactPost (fun chosen after => chosen = c ∧ Readable c history pending after.disk ∧
      after.disk.liveControl = some c ∧ after.disk.durableControl = some c)
      (fun after => Recoverable known req after.disk) (fun after => Recoverable known req after.disk)
      ((Segmented.selectControl callbacks.toRootOps).run start) := by
  unfold Segmented.selectControl
  have read := root.control start c visible
  have readPost : CompactPost (fun chosen after => chosen = c ∧ after.disk = start.disk)
      (fun after => Recoverable known req after.disk) (fun after => Recoverable known req after.disk)
      (callbacks.readControl.run start) := by
    cases ran : callbacks.readControl.run start with
    | error _ after => rw [ran] at read; exact read.symm ▸ prior
    | ok response after =>
      rw [ran] at read
      cases response with
      | error => exact read.symm ▸ prior
      | ok => exact read
  apply CompactPost.bind readPost
  rintro value beforeSync ⟨same, sameDisk⟩
  subst value
  have nonzero : c.capacity ≠ 0 := Nat.ne_of_gt source.layout.capacityPositive
  have release := Nat.le_trans source.layout.discardedFits source.layout.upper
  simp only [nonzero, decide_false, Bool.false_or, Bool.false_eq_true,
    Nat.not_lt_of_ge source.layout.capacityFits, Nat.not_lt_of_ge release, ↓reduceIte]
  have sync := root.collection.sync beforeSync
  have stable : Readable c history pending beforeSync.disk.syncRoot ∧
      beforeSync.disk.syncRoot.liveControl = some c ∧ beforeSync.disk.syncRoot.durableControl = some c := by
    rw [sameDisk]
    exact ⟨source.frame (fun id selected =>
      let names := source.layout.names id selected
      ⟨names.1, names.1⟩) (fun _ _ => rfl), visible, visible⟩
  have retry {later : Disk} (possible : later = beforeSync.disk ∨ later = beforeSync.disk.syncRoot) :
      Recoverable known req later := by
    rcases possible with rfl | rfl
    · exact sameDisk.symm ▸ prior
    · exact ⟨⟨c, stable.2.1, history, pending, stable.1, allowed⟩,
        ⟨c, stable.2.2, history, pending, stable.1, allowed⟩⟩
  have syncPost : CompactPost (fun _ after => after.disk = beforeSync.disk.syncRoot)
      (fun after => Recoverable known req after.disk) (fun after => Recoverable known req after.disk)
      (callbacks.syncRoot.run beforeSync) := by
    cases ran : callbacks.syncRoot.run beforeSync with
    | error _ after => rw [ran] at sync; exact retry sync
    | ok response after =>
      rw [ran] at sync
      cases response with
      | error => exact retry sync
      | ok => exact sync
  apply CompactPost.bind syncPost
  intro _ after synced
  exact ⟨rfl, synced.symm ▸ stable⟩

end WalRecoverySlice.Segmented.Native

namespace WalRecoverySlice.Segmented.Native
open Persistence Model

/-- A failed active open updates exactly that child's bytes, leaves its
previous cursor in the layout, and relinquishes the attempted child lock. -/
theorem compactActive_retry (dir : System.FilePath) (reports : SingleFile.OpenReports)
    (c : Control) (prior : List Bytes) (pending : Option Bytes) (disk : Disk)
    (source : Readable c prior pending disk)
    (live : disk.liveControl = some c) (durable : disk.durableControl = some c)
    (allowed : ∀ final, WalRecoverySlice.Contract.Permitted prior pending final →
      PermittedView known req (historyView c final))
    (seed : α) (step : α → Nat → Bytes → α)
    (failure : match SingleFile.openCompactModel dir c.policy reports {image := disk.segment c.active}
      seed (retainedStep c c.active step) with
      | .ok (.ok _) _ => False
      | .ok (.error _) after | .error _ after => after = reachedState) :
    reachedState.held = false ∧
      Recoverable known req (disk.setSegment c.active reachedState.image (disk.cursor c.active)) := by
  have post := SingleFile.openCompactModel_refines dir c.policy reports
    {image := disk.segment c.active} rfl source.active.dirty source.active.markers
    seed (retainedStep c c.active step)
  dsimp only at post
  have retry (after : SingleFile.OpenImage)
      (dirty : Dirty c.policy (segmentHistory c.capacity c.active prior) pending after.image)
      (markers : c.policy = .logOnly → after.image.MarkersSettled)
      (unlocked : after.held = false) :
      after.held = false ∧ Recoverable known req (disk.setSegment c.active after.image (disk.cursor c.active)) := by
    let changed := disk.setSegment c.active after.image (disk.cursor c.active)
    have keep : Layout c prior changed :=
      source.layout.frame (by exact source.layout.names) (fun idx _ lt => by
        simp [changed, Disk.setSegment, Nat.ne_of_lt lt])
    have child : Child.Recoverable c.policy (segmentHistory c.capacity c.active prior) pending
        (changed.segment c.active) := by
      simpa only [changed, Disk.setSegment, ↓reduceIte] using
        (show Child.Recoverable c.policy _ _ after.image from ⟨dirty, markers⟩)
    have choice : RecoveryChoice known req c changed :=
      ⟨prior, pending, ⟨keep, source.room, child⟩, allowed⟩
    exact ⟨unlocked, ⟨⟨c, live, choice⟩, ⟨c, durable, choice⟩⟩⟩
  cases ran : SingleFile.openCompactModel dir c.policy reports {image := disk.segment c.active}
      seed (retainedStep c c.active step) with
  | error token after =>
    rw [ran] at post failure
    change after = reachedState at failure
    subst reachedState
    exact retry after post.1 post.2.1 post.2.2
  | ok outcome after =>
    rw [ran] at post failure
    cases outcome with
    | ok => exact failure.elim
    | error =>
      change after = reachedState at failure
      subst reachedState
      exact retry after post.1 post.2.1 post.2.2

end WalRecoverySlice.Segmented.Native

namespace WalRecoverySlice.Segmented.Native

theorem loadCompactReadyWith_post (owned : store)
    (recover : CompactRecoveryM abort σ (CompactSession × α)) (before : σ)
    (selected : CompactSession → α → σ → Prop) (failed stopped : σ → Prop)
    (worker : CompactPost (fun result => selected result.1 result.2) failed stopped (recover.run before)) :
    CompactPost (fun out after => ∃ session, out.1 = .ready owned session ∧
      out.2.1 = session.bounds ∧ selected session out.2.2 after)
      failed stopped ((loadCompactReadyWith owned recover).run before) := by
  unfold loadCompactReadyWith
  apply CompactPost.bind worker
  rintro ⟨session, folded⟩ after facts
  exact ⟨session, rfl, rfl, facts⟩

/-- Model the outer public schedule at its actual load, phase-cell and
mutex calls. A reported failure returns from release of this invocation's
store; a stop leaves the resources issued so far to process-exit custody. -/
theorem openWithStore_post
    (acquire : CompactRecoveryM abort σ store)
    (load : store → CompactRecoveryM abort σ phase)
    (newRef : phase → CompactRecoveryM abort σ ref)
    (newMutex : CompactRecoveryM abort σ mutex)
    (release : store → CompactRecoveryM abort σ Unit)
    (before : σ) (lease cleanup : store → σ → Prop)
    (loaded : store → phase → σ → Prop)
    (allocated : store → ref → σ → Prop)
    (ready : (ref × mutex) → σ → Prop)
    (failed stopped : σ → Prop)
    (acquired : CompactPost lease failed stopped (acquire.run before))
    (loadPost : ∀ s t, lease s t → CompactPost (loaded s) (cleanup s) stopped ((load s).run t))
    (allocPost : ∀ s p t, loaded s p t → CompactPost (allocated s) (cleanup s) stopped ((newRef p).run t))
    (mutexPost : ∀ s cell t, allocated s cell t →
      CompactPost (fun mutex' after => ready (cell, mutex') after) (cleanup s) stopped (newMutex.run t))
    (released : ∀ s t, cleanup s t → CompactPost (fun _ => failed) failed stopped ((release s).run t)) :
    CompactPost ready failed stopped ((openWithStore (error := String) acquire load newRef newMutex release).run before) := by
  change CompactPost ready failed stopped ((withActiveChild (error := String) acquire release
    (fun owned => do
      let p ← load owned
      let cell ← newRef p
      return (cell, ← newMutex))).run before)
  apply CompactPost.withActive _ _ _ _ lease cleanup _ _ _ acquired _ released
  intro owned atLoad held
  apply CompactPost.bind (loadPost owned atLoad held)
  intro phase' atAlloc selected
  apply CompactPost.bind (allocPost owned phase' atAlloc selected)
  intro cell atMutex stored
  apply CompactPost.bind (mutexPost owned cell atMutex stored)
  intro mutex' after result
  exact result

end WalRecoverySlice.Segmented.Native

namespace WalRecoverySlice.Segmented.Native
open Persistence

/-- Reuse the settled child invariant at the actual compact open. Neither
writeback, repair, EIO nor interruption changes the sealed image. On success
the fold and the returned cursor describe the entire sealed segment. -/
theorem compactSealed_open (dir : System.FilePath) (policy : Policy) (r : SingleFile.OpenReports)
    (image : Image) (history : List Bytes)
    (settled : Child.Settled policy image history)
    (bounded : ∀ b ∈ history, b.length ≤ 32) (fits : history.length ≤ 255)
    (seed : α) (step : α → Nat → Bytes → α) :
    let outcome := SingleFile.openCompactModel dir policy r {image} seed step
    (SingleFile.postState outcome).image = image ∧
      match outcome with
      | .ok (.ok (phase, cursor, folded)) after =>
        after.held = true ∧ cursor = historyCursor history ∧
          phase = .active .lock ⟨SingleFile.appendFiles .writer .reader (SingleFile.markersFor policy), .reader⟩ cursor () ∧
          folded = SingleFile.foldBatches history seed step
      | .ok (.error _) after | .error _ after => after.held = false := by
  let start : SingleFile.OpenImage := {image}
  let child := settled.recoverable bounded fits
  have model := SingleFile.openExisting_worker dir policy r start rfl child.dirty child.markers
  dsimp only at model
  have stable := reopensSettledSegmentScheduled settled.ready settled.clean bounded fits r.worker r.writebacks
  rw [← SingleFile.recoverScheduled_eq] at stable
  dsimp only [start] at model
  have before := settleFiles_clean r.beforeWorker image settled.clean
  have after := settleFiles_clean r.afterWorker image settled.clean
  have frame : (SingleFile.postState (SingleFile.openExistingModel dir policy r start)).image = image := by
    rcases model.1 with left | right
    · simpa only [before, after] using left
    · simpa only [before, stable.1, after] using right
  have projected : (SingleFile.postState (SingleFile.openCompactModel dir policy r start seed step)).image = image := by
    rw [SingleFile.openCompactModel_projects]
    cases ran : SingleFile.openExistingModel dir policy r start <;> rw [ran] at frame <;> exact frame
  refine ⟨projected, ?_⟩
  have post := SingleFile.openCompactModel_refines dir policy r start rfl child.dirty child.markers seed step
  dsimp only at post
  cases ran : SingleFile.openCompactModel dir policy r start seed step with
  | error =>
    rw [ran] at post
    exact post.2.2
  | ok result reached =>
    rw [ran] at post
    cases result with
    | error => exact post.2.2
    | ok out =>
      obtain ⟨phase, cursor, folded⟩ := out
      obtain ⟨_, _, found, permitted, _, held, _, _, _, pos, phaseSet, foldedEq⟩ := post
      have same : found = history := by simpa [WalRecoverySlice.Contract.Permitted] using permitted
      exact ⟨held, same ▸ pos, phaseSet, same ▸ foldedEq⟩

end WalRecoverySlice.Segmented.Native
