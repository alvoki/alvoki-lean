import Alvoki.Experiments.WAL.Segmented.Native
import Alvoki.Experiments.WAL.Segmented.Proofs.Layout

namespace WalRecoverySlice.Segmented.Native
open System

private abbrev F := ExceptT String IO
private abbrev W := Void IO.RealWorld

private theorem ioBind_ok {action : IO α} {next : α → IO β}
    (ran : (action >>= next) w = .ok y v) :
    ∃ x t, action w = .ok x t ∧ next x t = .ok y v := by
  cases first : action w with
  | error => simp [Bind.bind, instMonadEIO._aux_13, EST.bind, first] at ran
  | ok x t => exact ⟨x, t, rfl, by simpa [Bind.bind, instMonadEIO._aux_13, EST.bind, first] using ran⟩

private theorem fileBind_ok {action : F α} {next : α → F β}
    (ran : (action >>= next).run w = .ok (.ok y) v) :
    ∃ x t, action.run w = .ok (.ok x) t ∧ (next x).run t = .ok (.ok y) v := by
  rw [ExceptT.run_bind] at ran
  obtain ⟨r, t, first, cont⟩ := ioBind_ok ran
  cases r with
  | error e => cases (EST.Out.ok.inj cont).1
  | ok x => exact ⟨x, t, first, cont⟩

private theorem checked_ok {action : F α} (ran : checked action w = .ok x t) :
    action.run w = .ok (.ok x) t := by
  obtain ⟨result, v, first, cont⟩ := ioBind_ok ran
  cases result with
  | error => contradiction
  | ok a => obtain ⟨rfl, rfl⟩ := EST.Out.ok.inj cont; exact first

private theorem cleanup_ok {action : IO α} {cleanup : IO Unit}
    (ran : cleanupOnError (error := IO.Error) action cleanup w = .ok x t) :
    action w = .ok x t := by
  cases result : action w with
  | ok a u =>
    simpa [cleanupOnError, tryCatchThe, MonadExceptOf.tryCatch, instMonadExceptOfEIO._aux_3,
      EST.tryCatch, result] using ran
  | error e u =>
    cases released : cleanup u <;>
      simp [cleanupOnError, tryCatchThe, MonadExceptOf.tryCatch, instMonadExceptOfEIO._aux_3,
        EST.tryCatch, result, released, Bind.bind, instMonadEIO._aux_13, EST.bind, Pure.pure,
        instMonadEIO._aux_5, EST.pure, throw, throwThe, MonadExceptOf.throw,
        instMonadExceptOfEIO._aux_1, EST.throw] at ran

/-- Reached acquisitions, public child reads and closes on the protected
segment names, in the same order as the executable sealed prefix. -/
inductive SealedReads (store : Store) (policy : Policy) (capacity : Nat) :
    Nat → Nat → W → W → List Bytes → Prop where
  | nil : SealedReads store policy capacity first 0 w w []
  | cons :
    store.acquireChild policy first w = .ok child opened →
    SingleFile.scan child opened = .ok batchList scanned →
    SingleFile.close child scanned = .ok () closed →
    batchList.length = capacity →
    SealedReads store policy capacity (first + 1) n closed done tail →
    SealedReads store policy capacity first (n + 1) w done (batchList ++ tail)

private theorem fileLift_ok {action : IO α}
    (ran : (liftM action : F α).run w = .ok (.ok x) t) :
    action w = .ok x t := by
  have lifted : (liftM action : F α).run = (do return (Except.ok (← action) : Except String α) : IO _) := rfl
  rw [lifted] at ran
  cases first : action w <;> simp [Bind.bind, instMonadEIO._aux_13, EST.bind, first,
    Pure.pure, instMonadEIO._aux_5, EST.pure] at ran ⊢ <;> exact ran

private theorem readSealedChild_ok {id : Nat} (s : Store)
    (ran : s.readSealedChild policy id w = .ok bs t) :
    ∃ child opened scanned,
      s.acquireChild policy id w = .ok child opened ∧
      SingleFile.scan child opened = .ok bs scanned ∧
      SingleFile.close child scanned = .ok () t := by
  obtain ⟨h, u, acquire, rest⟩ := ioBind_ok ran
  obtain ⟨b, v, read, rest⟩ := ioBind_ok rest
  obtain ⟨⟨⟩, z, close, pureRun⟩ := ioBind_ok rest
  obtain ⟨rfl, rfl⟩ := EST.Out.ok.inj pureRun
  exact ⟨h, u, v, acquire, cleanup_ok read, close⟩

theorem readSealed_returns (s : Store) (policy : Policy) (capacity first count : Nat)
    (acc : Array Bytes) (ran : (readSealed s.callbacks policy capacity first count acc).run w =
      .ok (.ok out) t) :
    ∃ tail, SealedReads s policy capacity first count w t tail ∧ out = acc ++ tail.toArray := by
  induction count generalizing first acc w with
  | zero =>
    obtain ⟨ok, rfl⟩ := EST.Out.ok.inj ran
    cases ok
    exact ⟨[], .nil, by simp⟩
  | succ n ih =>
    unfold readSealed at ran
    obtain ⟨bs, u, read, rest⟩ := fileBind_ok ran
    have concrete : s.readSealedChild policy first w = .ok bs u := fileLift_ok read
    obtain ⟨h, opened, scanned, acquire, scan, close⟩ := readSealedChild_ok s concrete
    by_cases full : bs.length = capacity
    · simp [full] at rest
      obtain ⟨tail, later, eq⟩ := ih _ _ rest
      exact ⟨_, .cons acquire scan close full later, by simpa [Array.append_assoc] using eq⟩
    · simp [full] at rest
      obtain ⟨_, _, impossible, _⟩ := fileBind_ok rest
      cases (EST.Out.ok.inj impossible).1

/-- Operations that actually produced the recovery view. The CONTROL value
and each child scan are reached through the same store's protected paths. -/
inductive RecoveredFrom (store : Store) (session : Session) (child : SingleFile.Handle)
    (w done : W) : Prop where
  | reached {c} {control synced sealed acquired activeRead : W} {rows active : List Bytes} :
    store.callbacks.readControl.run w = .ok (.ok c) control →
    0 < c.capacity → c.capacity ≤ 255 → c.discarded ≤ (c.active + 1) * c.capacity →
    store.callbacks.syncRoot.run control = .ok (.ok ()) synced →
    SealedReads store c.policy c.capacity c.firstNeeded (c.active - c.firstNeeded) synced sealed rows →
    store.acquireChild c.policy c.active sealed = .ok child acquired →
    SingleFile.scan child acquired = .ok active activeRead →
    active.length ≤ c.capacity → c.discarded ≤ c.active * c.capacity + active.length →
    (collect store.callbacks c).run activeRead = .ok (.ok ()) done →
    session = ⟨c, active.length, ⟨c.discarded,
      (rows ++ active).drop (c.discarded - c.firstNeeded * c.capacity)⟩⟩ →
    RecoveredFrom store session child w done

private theorem prefix_ok (s : Store)
    (ran : (reopenPrefix s.callbacks).run w = .ok (.ok (c, sealed)) t) :
    ∃ u v pre, s.callbacks.readControl.run w = .ok (.ok c) u ∧
      0 < c.capacity ∧ c.capacity ≤ 255 ∧ c.discarded ≤ (c.active + 1) * c.capacity ∧
      s.callbacks.syncRoot.run u = .ok (.ok ()) v ∧
      SealedReads s c.policy c.capacity c.firstNeeded (c.active - c.firstNeeded) v t pre ∧
      sealed = pre.toArray := by
  unfold reopenPrefix at ran
  obtain ⟨observed, u, read, rest⟩ := fileBind_ok ran
  by_cases valid : observed.capacity ≠ 0 ∧ observed.capacity ≤ 255
  · simp only [Bool.or_eq_true, decide_eq_true_eq] at rest
    simp [valid.1, Nat.not_lt_of_ge valid.2] at rest
    by_cases release : observed.discarded ≤ (observed.active + 1) * observed.capacity
    · simp [Nat.not_lt_of_ge release] at rest
      obtain ⟨⟨⟩, v, synced, rest⟩ := fileBind_ok rest
      obtain ⟨a, z, scanned, pureRun⟩ := fileBind_ok rest
      obtain ⟨val, rfl⟩ := EST.Out.ok.inj pureRun
      cases val
      obtain ⟨pre, steps, same⟩ := readSealed_returns s _ _ _ _ _ scanned
      exact ⟨u, v, pre, read, Nat.pos_of_ne_zero valid.1, valid.2, release, synced, steps, by simpa using same⟩
    · simp [Nat.lt_of_not_ge release] at rest
      obtain ⟨_, _, impossible, _⟩ := fileBind_ok rest
      cases (EST.Out.ok.inj impossible).1
  · have bad : observed.capacity = 0 ∨ 255 < observed.capacity := by omega
    rcases bad with zero | big
    all_goals
      first | simp [zero] at rest | simp [big] at rest
      obtain ⟨_, _, impossible, _⟩ := fileBind_ok rest
      cases (EST.Out.ok.inj impossible).1

private theorem finish_ok (s : Store) (c : Control) (sealed : Array Bytes) (active : List Bytes)
    (ran : (finishReopen s.callbacks c sealed active).run w = .ok (.ok session) t) :
    active.length ≤ c.capacity ∧ c.discarded ≤ c.active * c.capacity + active.length ∧
      (collect s.callbacks c).run w = .ok (.ok ()) t ∧
      session = ⟨c, active.length, ⟨c.discarded,
        (sealed.toList ++ active).drop (c.discarded - c.firstNeeded * c.capacity)⟩⟩ := by
  unfold finishReopen at ran
  by_cases fits : active.length ≤ c.capacity
  · simp [Nat.not_lt_of_ge fits] at ran
    by_cases release : c.discarded ≤ c.active * c.capacity + active.length
    · simp [Nat.not_lt_of_ge release] at ran
      obtain ⟨⟨⟩, u, cleanup, eq⟩ := fileBind_ok ran
      obtain ⟨val, rfl⟩ := EST.Out.ok.inj eq
      cases val
      exact ⟨fits, release, cleanup, rfl⟩
    · simp [Nat.lt_of_not_ge release] at ran
      obtain ⟨_, _, impossible, _⟩ := fileBind_ok ran
      cases (EST.Out.ok.inj impossible).1
  · simp [Nat.lt_of_not_ge fits] at ran
    obtain ⟨_, _, impossible, _⟩ := fileBind_ok ran
    cases (EST.Out.ok.inj impossible).1

theorem recoverChild_returns (s : Store)
    (ran : s.recoverChild w = .ok (session, child) v) :
    RecoveredFrom s session child w v := by
  have file := checked_ok ran
  obtain ⟨⟨c, sealed⟩, t, ranPrefix, rest⟩ := fileBind_ok file
  obtain ⟨controlled, synced, first, readControl, positive, bounded, discard,
    syncRoot, traced, exactPrefix⟩ := prefix_ok s ranPrefix
  have ranActive := fileLift_ok rest
  obtain ⟨held, entered, opened, continuation⟩ := ioBind_ok ranActive
  have resumed := cleanup_ok continuation
  obtain ⟨active, next, scanned, result⟩ := ioBind_ok resumed
  obtain ⟨returned, after, finish, done⟩ := fileBind_ok (checked_ok result)
  obtain ⟨val, rfl⟩ := EST.Out.ok.inj done
  cases val
  obtain ⟨fits, release, collected, eq⟩ := finish_ok s c sealed active finish
  exact .reached readControl positive bounded discard syncRoot traced opened scanned
    fits release collected (by simpa [exactPrefix] using eq)

/-- Consume each sealed child's exact acquire/scan/close from the state
reached by the previous close. The frame may express physical disk facts
preserved by the successful child operation. -/
theorem SealedReads.window {store : Store} {P : W → Prop} {history : List Bytes}
    (steps : SealedReads store policy capacity first count w t rows)
    (start : P w)
    (leaf : ∀ id, first ≤ id → id < first + count →
      ∀ h u opened bs scanned closed, P u →
      store.acquireChild policy id u = .ok h opened →
      SingleFile.scan h opened = .ok bs scanned →
      SingleFile.close h scanned = .ok () closed →
      bs = segmentHistory capacity id history ∧ P closed) :
    rows = segmentWindow capacity first count history ∧ P t := by
  induction steps with
  | nil => exact ⟨rfl, start⟩
  | @cons id u h opened bs scanned closed n done tail acquire read close full later ih =>
    obtain ⟨rowsEq, after⟩ := leaf id (by omega) (by omega) h u opened bs scanned closed start acquire read close
    obtain ⟨suffix, reached⟩ := ih after (fun i lo hi => leaf i (by omega) (by omega))
    exact ⟨by simp [rowsEq, suffix, segmentWindow], reached⟩

/-- An algebraic consequence of the actual child reads. The control, active
and sealed histories are supplied on their own reached operations. No
result of public open or cached segmented view is assumed. -/
theorem RecoveredFrom.view {store : Store} {P : W → Prop} (c : Control) (history : List Bytes)
    (steps : RecoveredFrom store session child w done)
    (upper : history.length ≤ (c.active + 1) * c.capacity)
    (control : ∀ d t, store.callbacks.readControl.run w = .ok (.ok d) t → d = c ∧ P t)
    (barrier : ∀ u v, P u → store.callbacks.syncRoot.run u = .ok (.ok ()) v → P v)
    (sealed : ∀ id, c.firstNeeded ≤ id → id < c.active →
      ∀ h u opened bs scanned closed, P u →
      store.acquireChild c.policy id u = .ok h opened →
      SingleFile.scan h opened = .ok bs scanned →
      SingleFile.close h scanned = .ok () closed →
      bs = segmentHistory c.capacity id history ∧ P closed)
    (active : ∀ u opened bs scanned, P u →
      store.acquireChild c.policy c.active u = .ok child opened →
      SingleFile.scan child opened = .ok bs scanned →
      bs = segmentHistory c.capacity c.active history ∧ P scanned)
    (collects : ∀ u v, P u → (collect store.callbacks c).run u = .ok (.ok ()) v → P v) :
    session.view = ⟨c.discarded, history.drop c.discarded⟩ ∧ P done := by
  cases steps with
  | reached readControl positive bounded release synced sealedReads acquired scanned fits within collected sessionEq =>
    obtain ⟨sameControl, frame⟩ := control _ _ readControl
    cases sameControl.symm
    have endId : c.firstNeeded ≤ c.active := Nat.min_le_left ..
    obtain ⟨window, afterSealed⟩ := sealedReads.window (barrier _ _ frame synced)
      (fun id lo hi => sealed id lo (by omega))
    obtain ⟨last, afterActive⟩ := active _ _ _ _ afterSealed acquired scanned
    exact ⟨by rw [sessionEq, window, last]; simp only [selectedHistory_eq c history upper],
      collects _ _ afterActive collected⟩

end WalRecoverySlice.Segmented.Native
