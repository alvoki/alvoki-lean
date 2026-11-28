import Alvoki.Experiments.WAL.Segmented.Proofs.RuntimeOpen
import Alvoki.Experiments.WAL.Segmented.Proofs.NativeRootIO
import Alvoki.Experiments.WAL.Segmented.Proofs.Invariant

namespace WalRecoverySlice.Segmented.Native
open Alvoki.NativePost System
open Model (Disk)

private theorem checked_post (run : Returns a w ok failed) : IOReturns (checked a) w ok failed := by
  unfold Returns at run
  unfold IOReturns checked
  cases r : a.run w with
  | error e t => rw [r] at run; simpa [Bind.bind, instMonadEIO._aux_13, EST.bind, r] using run
  | ok value t =>
    rw [r] at run
    cases value <;> simpa [Bind.bind, instMonadEIO._aux_13, EST.bind, r, Pure.pure, instMonadEIO._aux_5,
      EST.pure, throw, throwThe, MonadExceptOf.throw, instMonadExceptOfEIO._aux_1, EST.throw] using run

private theorem cleanup_post {action : IO α} {cleanup : IO Unit}
    (run : IOReturns action w ok needsClose)
    (release : ∀ u, needsClose u → IOReturns cleanup u (fun _ t => failed t) failed) :
    IOReturns (cleanupOnError (error := IO.Error) action cleanup) w ok failed := by
  unfold IOReturns at *
  cases result : action w with
  | ok a u =>
    rw [result] at run
    simpa [cleanupOnError, tryCatchThe, MonadExceptOf.tryCatch, instMonadExceptOfEIO._aux_3,
      EST.tryCatch, result] using run
  | error e u =>
    rw [result] at run
    have rel := release u run
    cases released : cleanup u <;> rw [released] at rel <;>
      simpa [cleanupOnError, tryCatchThe, MonadExceptOf.tryCatch, instMonadExceptOfEIO._aux_3,
        EST.tryCatch, result, released, Bind.bind, instMonadEIO._aux_13, EST.bind,
        Pure.pure, instMonadEIO._aux_5, EST.pure, throw, throwThe, MonadExceptOf.throw,
        instMonadExceptOfEIO._aux_1, EST.throw] using rel

theorem Store.readSealedChild_post (s : Store) {id : Nat}
    {held : SingleFile.Handle → W → Prop} {ok failed : W → Prop}
    (acquire : IOReturns (s.acquireChild p id) w held failed)
    (scan : ∀ h u, held h u → IOReturns (SingleFile.scan h) u
      (fun bytes t => bytes = expected ∧ held h t) (held h))
    (close : ∀ h u, held h u → IOReturns (SingleFile.close h) u
      (fun _ t => ok t ∧ failed t) failed) :
    IOReturns (s.readSealedChild p id) w (fun bytes t => bytes = expected ∧ ok t) failed := by
  unfold Store.readSealedChild readSealedChildWith
  apply IOReturns.bind acquire
  intro h u owns
  have release (v) (entry : held h v) : IOReturns (SingleFile.close h) v (fun _ t => failed t) failed := by
    have closed := close h v entry
    unfold IOReturns at *
    cases run : SingleFile.close h v <;> rw [run] at closed <;> first | exact closed.2 | exact closed
  apply IOReturns.bind (cleanup_post (scan h u owns) release)
  intro bs t result
  apply IOReturns.bind (close h t result.2)
  exact fun _ _ post => ⟨result.1, post.1⟩

private theorem readSealed_post (s : Store) (c : Control) (history : List Bytes)
    (first count : Nat) (acc : Array Bytes) (P bad : W → Prop)
    (start : P w) (retry : ∀ u, P u → bad u)
    (leaf : ∀ id, first ≤ id → id < first + count → ∀ u, P u →
      IOReturns (s.readSealedChild c.policy id) u
        (fun bs t => bs = segmentHistory c.capacity id history ∧ P t) bad) :
    Returns (readSealed s.callbacks c.policy c.capacity first count acc) w
      (fun rows t => rows.toList = acc.toList ++ segmentWindow c.capacity first count history ∧ P t) bad := by
  induction count generalizing first acc w with
  | zero => exact ⟨by simp [segmentWindow], start⟩
  | succ n ih =>
    unfold readSealed
    apply Returns.bind (Returns.liftIO (leaf first (by omega) (by omega) w start))
    intro rows t post
    by_cases full : rows.length = c.capacity
    · simp [full]
      apply Returns.mapPost (ih (first+1) (acc ++ rows.toArray) post.2
        (fun id lo hi => leaf id (by omega) (by omega)))
      · intro result u done
        exact ⟨by simpa [segmentWindow, post.1, List.append_assoc] using done.1, done.2⟩
      · exact fun _ h => h
    · simp [full]
      exact retry _ post.2

/-- The scoped open worker consumes each child in turn. The active descriptor
is retained across collection and returned on success. Failure after acquiring
it runs its close on the precise world left by scan or collection. -/
theorem Store.recoverChild_post (s : Store) (c : Control) (history : List Bytes)
    (P0 P : W → Prop) (held : SingleFile.Handle → W → Prop) (bad : W → Prop)
    (source : Returns s.callbacks.readControl w (fun observed t => observed = c ∧ P0 t) bad)
    (retry0 : ∀ t, P0 t → bad t) (retry : ∀ t, P t → bad t)
    (sync : ∀ t, P0 t → Returns s.callbacks.syncRoot t (fun _ u => P u) bad)
    (sealed : ∀ id, c.firstNeeded ≤ id → id < c.active → ∀ u, P u →
      IOReturns (s.readSealedChild c.policy id) u
        (fun bs t => bs = segmentHistory c.capacity id history ∧ P t) bad)
    (acquire : ∀ u, P u → IOReturns (s.acquireChild c.policy c.active) u held bad)
    (scan : ∀ h u, held h u → IOReturns (SingleFile.scan h) u
      (fun bs t => bs = segmentHistory c.capacity c.active history ∧ held h t) (held h))
    (close : ∀ h u, held h u → IOReturns (SingleFile.close h) u (fun _ t => bad t) bad)
    (collect : ∀ h u, held h u → Returns (Segmented.collect s.callbacks c) u
      (fun _ t => held h t) (held h))
    (upper : history.length ≤ (c.active + 1) * c.capacity) :
    IOReturns s.recoverChild w
      (fun out t => out.1 = sessionOf c history ∧ held out.2 t) bad := by
  unfold Store.recoverChild
  apply checked_post
  unfold reopenWith reopenPrefix
  apply Returns.bind (middle := fun pair t => pair.1 = c ∧
    pair.2.toList = segmentWindow c.capacity c.firstNeeded (c.active-c.firstNeeded) history ∧ P t)
  · apply Returns.bind source
    intro observed t read
    obtain ⟨rfl, before⟩ := read
    dsimp only
    split
    · exact retry0 t before
    · split
      · exact retry0 t before
      · apply Returns.bind (sync t before)
        intro _ u after
        apply Returns.bind (readSealed_post s _ history _ _ #[] P bad after retry ?_)
        · intro rows v post
          exact ⟨rfl, by simpa using post.1, post.2⟩
        · intro id lo hi
          have le : observed.firstNeeded ≤ observed.active := Nat.min_le_left ..
          exact sealed id lo (by omega)
  · rintro ⟨observed, rows⟩ u ⟨rfl, rowsEq, frame⟩
    dsimp only at rowsEq upper
    apply Returns.liftIO
    unfold withActiveChild
    apply IOReturns.bind (acquire u frame)
    intro h v owned
    apply cleanup_post (needsClose := held h) _ (close h)
    apply IOReturns.bind (scan h v owned)
    rintro bytes a ⟨rfl, scanned⟩
    apply checked_post
    unfold finishReopen
    apply Returns.bind (middle := fun session t => session = sessionOf observed history ∧ held h t)
    · dsimp only
      split
      · exact scanned
      · split
        · exact scanned
        · apply Returns.bind (collect h a scanned)
          intro _ b collected
          exact ⟨by simp [sessionOf, rowsEq, selectedHistory_eq observed history upper, historyView], collected⟩
    · exact fun session _ frame => ⟨frame.1, frame.2⟩

/-- The two phase allocations and the active-slot write only change memory.
These frames are quantified over the actual allocated objects and worlds. -/
structure InstallFrame (P : W → Prop) : Prop where
  attach : ∀ (r : IO.Ref (Option (Nat × SingleFile.Handle))) id h w, P w →
    P ((r.set (some (id, h)) : BaseIO Unit) w).state
  phase : ∀ s session w, P w → P ((IO.mkRef (.ready s session : Phase Store) : BaseIO _) w).state
  mutex : ∀ w, P w → P (Std.BaseMutex.new w).state

private theorem IOReturns.atOk {a : IO α} (h : IOReturns a w ok fail) (run : a w = .ok x t) :
    ok x t := by simpa only [IOReturns, run] using h

private theorem IOReturns.atError {a : IO α} (h : IOReturns a w ok fail)
    (run : a w = .error e t) : fail t := by simpa only [IOReturns, run] using h

/-- Move the recovery post through registration, phase installation, and
startup unwind. On the error path the slot is still empty; the store invokes
its root unlock on the reached world after taking the slot. -/
theorem openExisting_diskPost_of_worker (heap : PhaseMemory) (dir : FilePath)
    (disk : W → Disk) (known : Contract.View) (Q : W → Prop) (owned : Store → W → Prop)
    (acquire : IOReturns (acquireStore dir) w owned (fun t => Recoverable known none (disk t) ∧ Q t))
    (worker : ∀ s u, owned s u → IOReturns s.recoverChild u
      (fun out t => Installed out.1 (disk t) ∧ out.1.view = known ∧ Q t)
      (fun t => heap.holds s.active none t ∧ Recoverable known none (disk t) ∧ Q t))
    (install : ∀ session, InstallFrame (fun t => Installed session (disk t) ∧ Q t))
    (take : ∀ (s : Store) t, Recoverable known none (disk t) ∧ Q t →
      let next := ((s.active.swap none : BaseIO _) t).state
      Recoverable known none (disk next) ∧ Q next)
    (unlock : ∀ (s : Store) u, Recoverable known none (disk u) ∧ Q u →
      IOReturns s.lock.unlock u (fun _ t => Recoverable known none (disk t) ∧ Q t)
        (fun t => Recoverable known none (disk t) ∧ Q t)) :
    IOReturns (openExisting dir) w
      (fun h t => ∃ session, heap.Ready h session t ∧ Installed session (disk t) ∧ session.view = known ∧ Q t)
      (fun t => Recoverable known none (disk t) ∧ Q t) := by
  unfold IOReturns
  cases opened : openExisting dir w with
  | ok h t =>
    obtain ⟨session, origin, ready⟩ := openExisting_ready heap dir opened
    obtain ⟨s, u, child, v, raw, recovery, _, _, rfl⟩ := origin
    obtain ⟨installed, eq, keep⟩ := IOReturns.atOk (worker s u (IOReturns.atOk acquire raw)) recovery
    let F := install session
    have final := F.mutex _ (F.phase s session _ (F.attach s.active session.control.active child _ ⟨installed, keep⟩))
    exact ⟨session, ready, final.1, eq, final.2⟩
  | error e t =>
    rcases openExisting_failure dir opened with early | ⟨s, u, v, raw, err, rfl⟩
    · exact IOReturns.atError acquire early
    · obtain ⟨empty, offline⟩ := IOReturns.atError (worker s u (IOReturns.atOk acquire raw)) err
      let slot := (s.active.swap none : BaseIO _) v
      have isEmpty : slot.val = none := heap.swap none empty
      have taken : (s.active.swap none : IO _) v = .ok none slot.state := by
        change EST.Out.ok slot.val slot.state = EST.Out.ok none slot.state
        rw [isEmpty]
      rw [s.release_empty taken]
      have freed := unlock s slot.state (take s v offline)
      cases released : s.lock.unlock slot.state <;> rw [IOReturns, released] at freed <;> exact freed

end WalRecoverySlice.Segmented.Native
