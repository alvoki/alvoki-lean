import Alvoki.Experiments.WAL.Segmented.Proofs.Layout
import Alvoki.Experiments.WAL.Segmented.Proofs.NativeRootIO
import Alvoki.Experiments.WAL.Segmented.Proofs.Writeback

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
    (P0 P : W → Prop) (held : List Bytes → SingleFile.Handle → W → Prop) (bad : W → Prop)
    (source : Returns s.callbacks.readControl w (fun observed t => observed = c ∧ P0 t) bad)
    (retry0 : ∀ t, P0 t → bad t) (retry : ∀ t, P t → bad t)
    (sync : ∀ t, P0 t → Returns s.callbacks.syncRoot t (fun _ u => P u) bad)
    (sealed : ∀ id, c.firstNeeded ≤ id → id < c.active → ∀ u, P u →
      IOReturns (s.readSealedChild c.policy id) u
        (fun bs t => bs = segmentHistory c.capacity id history ∧ P t) bad)
    (acquire : ∀ u, P u → IOReturns (s.acquireChild c.policy c.active) u (fun h t => ∃ final, held final h t) bad)
    (scan : ∀ final h u, held final h u → IOReturns (SingleFile.scan h) u
      (fun bs t => bs = segmentHistory c.capacity c.active final ∧ held final h t) (held final h))
    (close : ∀ final h u, held final h u → IOReturns (SingleFile.close h) u (fun _ t => bad t) bad)
    (collect : ∀ final h u, held final h u → Returns (Segmented.collect s.callbacks c) u
      (fun _ t => held final h t) (held final h))
    (layout : ∀ final h t, held final h t → final.length ≤ (c.active + 1) * c.capacity ∧
      segmentWindow c.capacity c.firstNeeded (c.active-c.firstNeeded) history =
      segmentWindow c.capacity c.firstNeeded (c.active-c.firstNeeded) final) :
    IOReturns s.recoverChild w
      (fun out t => ∃ final, out.1 = sessionOf c final ∧ held final out.2 t) bad := by
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
    dsimp only at rowsEq
    apply Returns.liftIO
    unfold withActiveChild
    apply IOReturns.bind (acquire u frame)
    rintro h v ⟨final, owned⟩
    obtain ⟨upper, earlier⟩ := layout final h v owned
    rw [earlier] at rowsEq
    apply cleanup_post (needsClose := held final h) _ (close final h)
    apply IOReturns.bind (scan final h v owned)
    rintro bytes a ⟨rfl, scanned⟩
    apply checked_post
    unfold finishReopen
    apply Returns.bind (middle := fun session t => session = sessionOf observed final ∧ held final h t)
    · dsimp only
      split
      · exact scanned
      · split
        · exact scanned
        · apply Returns.bind (collect final h a scanned)
          intro _ b collected
          exact ⟨by simp [sessionOf, rowsEq, selectedHistory_eq observed final upper, historyView], collected⟩
    · exact fun session _ frame => ⟨final, frame.1, frame.2⟩

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

/-- A recovery exception on the very store returned by this public acquisition. -/
def StoreUnwinding (dir : FilePath) (s : Store) (stopped : W) : Prop :=
  ∃ start acquired e, acquireStore dir start = .ok s acquired ∧ s.recoverChild acquired = .error e stopped

/-- The unwinder took the empty slot and now executes this store's lock release. -/
def StoreUnlockAt (dir : FilePath) (s : Store) (t : W) : Prop :=
  ∃ stopped, StoreUnwinding dir s stopped ∧ (s.active.swap none : IO _) stopped = .ok none t

theorem openExisting_unwind_error (dir : FilePath) (s : Store)
    (acquire : acquireStore dir start = .ok s acquired)
    (fail : s.recoverChild acquired = .error primary stopped)
    (take : (s.active.swap none : IO _) stopped = .ok none taken)
    (unlock : s.lock.unlock taken = .error secondary finish) :
    openExisting dir start = .error primary finish := by
  rw [openExisting_run, acquire]
  simp only [fail, s.release_empty take, unlock, returnedWorld]

/-- Move the recovery post through registration, phase installation, and
startup unwind. On the error path the slot is still empty; the store invokes
its root unlock on the reached world after taking the slot. -/
theorem openExisting_registered_of_worker (heap : PhaseMemory) (dir : FilePath)
    (disk : W → Disk) (known : Contract.View) (req : Option Contract.Request) (Q : W → Prop)
    (C : Store → Session → SingleFile.Handle → W → Prop) (owned lease : Store → W → Prop)
    (acquire : IOReturns (acquireStore dir) w owned (fun t => Recoverable known req (disk t) ∧ Q t))
    (rootLock : ∀ s u, acquireStore dir w = .ok s u → RootLockAt s.root s.lock)
    (worker : ∀ s u, owned s u → IOReturns s.recoverChild u
      (fun out t => (∃ fd, ChildLockAt (segmentPath s.root out.1.control.active) out.2 fd) ∧
        C s out.1 out.2 t ∧ PermittedView known req out.1.view ∧ Q t)
      (fun t => heap.holds s.active none t ∧ lease s t ∧ Recoverable known req (disk t) ∧ Q t))
    (install : ∀ s session h, InstallFrame (fun t => C s session h t ∧ Q t))
    (take : ∀ (s : Store) t, StoreUnwinding dir s t → heap.holds s.active none t → lease s t →
      Recoverable known req (disk t) ∧ Q t → let next := ((s.active.swap none : BaseIO _) t).state
      lease s next ∧ Recoverable known req (disk next) ∧ Q next)
    (unlock : ∀ (s : Store) u, StoreUnlockAt dir s u → lease s u → Recoverable known req (disk u) ∧ Q u →
      IOReturns s.lock.unlock u (fun _ t => Recoverable known req (disk t) ∧ Q t)
        (fun t => Recoverable known req (disk t) ∧ Q t)) :
    IOReturns (openExisting dir) w
      (fun h t => ∃ reg, Origin dir h reg w t ∧ heap.Registered h reg t ∧ LocksFrom reg ∧
        C reg.store reg.session reg.child t ∧ PermittedView known req reg.session.view ∧ Q t)
      (fun t => Recoverable known req (disk t) ∧ Q t) := by
  unfold IOReturns
  cases opened : openExisting dir w with
  | ok h t =>
    obtain ⟨session, origin, _⟩ := openExisting_ready heap dir opened
    obtain ⟨s, u, child, v, raw, recovery, stateEq, mutexEq, rfl⟩ := origin
    obtain ⟨childLock, installed, eq, keep⟩ := IOReturns.atOk (worker s u (IOReturns.atOk acquire raw)) recovery
    let F := install s session child
    have final := F.mutex _ (F.phase s session _ (F.attach s.active session.control.active child _ ⟨installed, keep⟩))
    let registration : Registration := ⟨session, s, child⟩
    refine ⟨registration, ?_, ?_, ⟨rootLock s u raw, childLock⟩, final.1, eq, final.2⟩
    · exact ⟨u, v, raw, recovery, stateEq, mutexEq, rfl⟩
    · unfold PhaseMemory.Registered
      rw [stateEq]
      exact ⟨heap.fresh _ (heap.set _ _ _), heap.newMutex (heap.allocate _ _),
        heap.newMutex (heap.allocateFrame _ (heap.set _ _ _))⟩
  | error e t =>
    rcases openExisting_failure dir opened with early | ⟨s, u, v, raw, err, rfl⟩
    · exact IOReturns.atError acquire early
    · obtain ⟨empty, held, offline⟩ := IOReturns.atError (worker s u (IOReturns.atOk acquire raw)) err
      let slot := (s.active.swap none : BaseIO _) v
      have isEmpty : slot.val = none := heap.swap none empty
      have taken : (s.active.swap none : IO _) v = .ok none slot.state := by
        change EST.Out.ok slot.val slot.state = EST.Out.ok none slot.state
        rw [isEmpty]
      rw [s.release_empty taken]
      have path : StoreUnwinding dir s v := ⟨w, u, e, raw, err⟩
      obtain ⟨stillHeld, kept⟩ := take s v path empty held offline
      have freed := unlock s slot.state ⟨v, path, taken⟩ stillHeld kept
      cases released : s.lock.unlock slot.state <;> rw [IOReturns, released] at freed <;> exact freed

/-- Only the opened segment's image and cursor can be changed by a child reopen. -/
def ChildChange (id : Nat) (before after : Disk) : Prop :=
  ∃ saved, Writebacks before saved ∧ after = saved.setSegment id (after.segment id) (after.cursor id)

def AfterClose (before after : Disk) : Prop :=
  ∃ saved, Writebacks before saved ∧ after = {saved with cursor := after.cursor}

/-- A selected segment is qualified by its actual directory, policy and
registered handle. Scanning consumes that binding; closing need only retain
file contents, since the closed descriptor's cursor is no longer live. -/
structure ChildAccess (s : Store) (disk : W → Disk) (Q : W → Prop) where
  owns : Nat → SingleFile.Handle → List Bytes → W → Prop
  source : ∀ id h bs u, owns id h bs u → ∃ fd, ChildLockAt (segmentPath s.root id) h fd
  select : ∀ p id bs pending u, Q u → id ∈ (disk u).liveNames →
    Child.Recoverable p bs pending ((disk u).segment id) →
    IOReturns (s.acquireChild p id) u
      (fun h t => Q t ∧ ChildChange id (disk u) (disk t) ∧ ∃ actual,
        WalRecoverySlice.Contract.Permitted bs pending actual ∧ owns id h actual t ∧
        Child.Installed p ((disk t).segment id) ((disk t).cursor id) actual ∧
        (pending = none → Child.Settled p ((disk u).segment id) bs → (disk t).segment id = (disk u).segment id))
      (fun t => Q t ∧ ChildChange id (disk u) (disk t) ∧
        Child.Recoverable p bs pending ((disk t).segment id) ∧
        (pending = none → Child.Settled p ((disk u).segment id) bs → (disk t).segment id = (disk u).segment id))
  scan : ∀ id h bs u, owns id h bs u → Q u → IOReturns (SingleFile.scan h) u
    (fun bytes t => bytes = bs ∧ owns id h bs t ∧ Q t ∧ Writebacks (disk u) (disk t))
    (fun t => owns id h bs t ∧ Q t ∧ Writebacks (disk u) (disk t))
  close : ∀ id h bs u, owns id h bs u → Q u → IOReturns (SingleFile.close h) u
    (fun _ t => Q t ∧ AfterClose (disk u) (disk t))
    (fun t => Q t ∧ AfterClose (disk u) (disk t))

theorem ChildAccess.acquire (op : ChildAccess s disk Q) (p : Policy) (id : Nat) (bs : List Bytes) (u : W)
    (held : Q u) (named : id ∈ (disk u).liveNames) (clean : Child.Recoverable p bs none ((disk u).segment id)) :
    IOReturns (s.acquireChild p id) u
      (fun h t => Q t ∧ ChildChange id (disk u) (disk t) ∧ op.owns id h bs t ∧
        Child.Installed p ((disk t).segment id) ((disk t).cursor id) bs ∧
        (Child.Settled p ((disk u).segment id) bs → (disk t).segment id = (disk u).segment id))
      (fun t => Q t ∧ ChildChange id (disk u) (disk t) ∧ Child.Recoverable p bs none ((disk t).segment id) ∧
        (Child.Settled p ((disk u).segment id) bs → (disk t).segment id = (disk u).segment id)) := by
  have out := op.select p id bs none u held named clean
  simpa [WalRecoverySlice.Contract.Permitted] using out

private structure OpenLayout (c : Control) (history : List Bytes) (pending : Option Bytes) (d : Disk) : Prop where
  readable : Readable c history pending d
  live : d.liveControl = some c
  durable : d.durableControl = some c

private theorem OpenLayout.retry (o : OpenLayout c history pending d)
    (permit : ∀ actual, WalRecoverySlice.Contract.Permitted history pending actual →
      PermittedView known req (historyView c actual)) : Recoverable known req d := by
  have choice : RecoveryChoice known req c d := ⟨history, pending, o.readable, permit⟩
  exact ⟨⟨c, o.live, choice⟩, ⟨c, o.durable, choice⟩⟩

private theorem OpenLayout.writebacks (o : OpenLayout c history pending before) (steps : Writebacks before after) :
    OpenLayout c history pending after := ⟨steps.readable o.readable, steps.live.trans o.live, steps.durable.trans o.durable⟩

private theorem OpenLayout.child {id : Nat} (o : OpenLayout c history pending before) (delta : ChildChange id before after)
    (clean : Child.Settled p (before.segment id) bs)
    (unchanged : after.segment id = before.segment id) : OpenLayout c history pending after := by
  obtain ⟨saved, writes, delta⟩ := delta
  have middle := o.writebacks writes
  have names : ∀ i, c.selects i → i ∈ after.liveNames ∧ i ∈ after.durableNames := by
    rw [delta]; exact middle.readable.layout.names
  have same (i : Nat) : after.segment i = saved.segment i := by
    by_cases eq : i = id
    · subst i; exact unchanged.trans (writes.settled clean).symm
    · calc after.segment i = (saved.setSegment id (after.segment id) (after.cursor id)).segment i :=
             congrArg (fun d : Disk => d.segment i) delta
           _ = _ := Disk.setSegment_other _ _ _ eq
  exact ⟨middle.readable.frame names (fun i _ => same i), (congrArg Disk.liveControl delta).trans middle.live,
    (congrArg Disk.durableControl delta).trans middle.durable⟩

private theorem OpenLayout.activeLayout (o : OpenLayout c history pending before)
    (delta : ChildChange c.active before after) :
    Layout c history after ∧ after.liveControl = some c ∧ after.durableControl = some c := by
  obtain ⟨saved, writes, delta⟩ := delta
  have prior := o.writebacks writes
  refine ⟨?_, (congrArg Disk.liveControl delta).trans prior.live, (congrArg Disk.durableControl delta).trans prior.durable⟩
  apply prior.readable.layout.frame
  · rw [delta]; exact prior.readable.layout.names
  · intro i _ sealed
    calc after.segment i = (saved.setSegment c.active (after.segment c.active) (after.cursor c.active)).segment i :=
             congrArg (fun d : Disk => d.segment i) delta
         _ = _ := Disk.setSegment_other _ _ _ (Nat.ne_of_lt sealed)

private theorem OpenLayout.activeFail (o : OpenLayout c history pending before)
    (delta : ChildChange c.active before after)
    (retained : Child.Recoverable c.policy (segmentHistory c.capacity c.active history) pending (after.segment c.active)) :
    OpenLayout c history pending after :=
  ⟨⟨(o.activeLayout delta).1, o.readable.room, retained⟩, (o.activeLayout delta).2.1, (o.activeLayout delta).2.2⟩

private theorem OpenLayout.cursors (o : OpenLayout c history pending before)
    (eq : AfterClose before after) : OpenLayout c history pending after := by
  obtain ⟨_, steps, eq⟩ := eq
  have o := o.writebacks steps
  exact ⟨o.readable.frame (by rw [eq]; exact o.readable.layout.names)
    (fun i _ => by rw [eq]), (congrArg Disk.liveControl eq).trans o.live,
    (congrArg Disk.durableControl eq).trans o.durable⟩

private theorem Recoverable.cursors {request : Option Contract.Request} (o : Recoverable known request before)
    (eq : AfterClose before after) : Recoverable known request after := by
  obtain ⟨saved, steps, eq⟩ := eq
  have o := steps.recoverable o
  obtain ⟨c, live, choice⟩ := o.live
  obtain ⟨d, durable, old⟩ := o.durable
  have keeps {c} (r : RecoveryChoice known request c saved) : RecoveryChoice known request c after := by
    obtain ⟨history, p, readable, permits⟩ := r
    exact ⟨history, p, readable.frame (by rw [eq]; exact readable.layout.names)
      (fun i _ => by rw [eq]), permits⟩
  exact ⟨⟨c, (congrArg Disk.liveControl eq).trans live, keeps choice⟩,
    ⟨d, (congrArg Disk.durableControl eq).trans durable, keeps old⟩⟩

private theorem mapIO {a : IO α} {ok : α → W → Prop} {fail : W → Prop}
    {done : α → W → Prop} {bad : W → Prop}
    (h : IOReturns a w ok fail) (success : ∀ x t, ok x t → done x t)
    (failure : ∀ t, fail t → bad t) : IOReturns a w done bad := by
  unfold IOReturns at *
  cases r : a w with
  | ok x t => rw [r] at h; exact success x t h
  | error e t => rw [r] at h; exact failure t h

private theorem ChildAccess.readSealed {id : Nat} (ops : ChildAccess s disk Q)
    (permit : ∀ actual, WalRecoverySlice.Contract.Permitted history pending actual → PermittedView known req (historyView c actual))
    (o : OpenLayout c history pending (disk u)) (keep : Q u) (lo : c.firstNeeded ≤ id) (lt : id < c.active) :
    IOReturns (s.readSealedChild c.policy id) u
      (fun rows t => rows = segmentHistory c.capacity id history ∧ Q t ∧ OpenLayout c history pending (disk t))
      (fun t => Q t ∧ Recoverable known req (disk t)) := by
  let bs := segmentHistory c.capacity id history
  let Frame := fun t => Q t ∧ OpenLayout c history pending (disk t)
  let Failure := fun t => Q t ∧ Recoverable known req (disk t)
  let held := fun h t => ops.owns id h bs t ∧ Frame t
  have selected : c.selects id := ⟨lo, Nat.le_of_lt lt⟩
  have settled := o.readable.layout.sealed id selected lt
  have raw := ops.acquire c.policy id bs u keep (o.readable.layout.names id selected).1
    (settled.recoverable (segmentHistory_bounded o.readable.layout id)
      (Nat.le_trans (segmentHistory_fits ..) o.readable.layout.capacityFits))
  apply Store.readSealedChild_post s (ok := Frame) (failed := Failure) (held := held)
  · apply mapIO raw
    · rintro h t ⟨q, change, owned, _, physical⟩
      exact ⟨owned, q, o.child change settled (physical settled)⟩
    · rintro t ⟨q, change, _, physical⟩
      exact ⟨q, (o.child change settled (physical settled)).retry permit⟩
  · rintro h v ⟨owned, q, prior⟩
    apply mapIO (ops.scan id h bs v owned q)
    · rintro bytes t ⟨rfl, owns, qt, same⟩
      exact ⟨rfl, owns, qt, prior.writebacks same⟩
    · rintro t ⟨owns, qt, same⟩
      exact ⟨owns, qt, prior.writebacks same⟩
  · rintro h v ⟨owned, q, prior⟩
    have after {t} (post : Q t ∧ AfterClose (disk v) (disk t)) : Frame t ∧ Failure t :=
      ⟨⟨post.1, prior.cursors post.2⟩, ⟨post.1, (prior.cursors post.2).retry permit⟩⟩
    exact mapIO (ops.close id h bs v owned q) (fun _ _ post => after post) (fun _ post => (after post).2)

/-- Concrete custody after the active child was recovered. The same history
supplies the selected files, active bytes, cursor, and owned child phase. -/
def RecoveredChild (disk : W → Disk) (owns : Nat → SingleFile.Handle → List Bytes → W → Prop)
    (session : Session) (h : SingleFile.Handle) (t : W) : Prop :=
  ∃ history, session = sessionOf session.control history ∧
    owns session.control.active h (segmentHistory session.control.capacity session.control.active history) t ∧
    ReadyLayout session.control history (disk t) ∧
    (disk t).liveControl = some session.control ∧ (disk t).durableControl = some session.control

theorem RecoveredChild.installed (child : RecoveredChild disk owns session h t) : Installed session (disk t) :=
  let ⟨hist, eq, _, ready, live, durable⟩ := child
  ⟨hist, eq, ready, live, durable⟩

/-- The final collection may mutate retired files and names. Its leaf frames
protect the installed active child, its cursor, and the still-selected layout. -/
def ActiveFrame (children : ChildAccess s disk Q) (c : Control) (history : List Bytes)
    (h : SingleFile.Handle) (w : W) : Prop :=
  children.owns c.active h (segmentHistory c.capacity c.active history) w ∧ Q w ∧ ReadyLayout c history (disk w) ∧
    (disk w).liveControl = some c ∧ (disk w).durableControl = some c

structure StoreOperations (s : Store) (disk : W → Disk) (Q : W → Prop)
    (child : Type) (access : child → ChildAccess s disk Q) where
  controlBytes : W → ByteArray
  controlBound : ∀ w, Q w → ControlCodec.decode (controlBytes w) = (disk w).liveControl
  metadata : ∀ w, Q w → IOReturns (s.root / "CONTROL").symlinkMetadata w
    (fun _ t => Q t ∧ Writebacks (disk w) (disk t)) (fun t => Q t ∧ Writebacks (disk w) (disk t))
  file : ∀ before, FileRead.Primitives (s.root / "CONTROL") (fun t => Q t ∧ Writebacks before (disk t))
    controlBytes id
  sync : ∀ w, Q w → IOReturns (syncHandle s.directory) w
    (fun _ t => Q t ∧ Writebacks (disk w).syncRoot (disk t))
    (fun t => Q t ∧ (Writebacks (disk w) (disk t) ∨ Writebacks (disk w).syncRoot (disk t)))
  children : child
  cleanup : ∀ c history h, CollectionIO s.root c.firstNeeded (ActiveFrame (access children) c history h)
  cleanupSync : ∀ c history h, Keeps (ActiveFrame (access children) c history h) (syncHandle s.directory)

abbrev StoreIO (s : Store) (disk : W → Disk) (Q : W → Prop) :=
  StoreOperations s disk Q (ChildAccess s disk Q) id

private theorem decode_bounds {raw : ByteArray} (parsed : ControlCodec.decode raw = some c) :
    c.active ≤ ControlCodec.wordMax ∧ c.discarded ≤ ControlCodec.wordMax := by
  simp only [ControlCodec.decode] at parsed
  split at parsed
  · split at parsed <;> simp_all <;> obtain ⟨⟨bounds, _⟩, rfl⟩ := parsed <;> exact bounds
  · contradiction

private theorem segmentWindow_same (h : ∀ id, id < active → segmentHistory cap id a = segmentHistory cap id b)
    (first count : Nat) (limit : first + count ≤ active) :
    segmentWindow cap first count a = segmentWindow cap first count b := by
  induction count generalizing first with
  | zero => rfl
  | succ n ih => simp only [segmentWindow, h first (by omega), ih (first+1) (by omega)]

/-- The active child resolves its own pending batch. Its actual returned
batches determine the history used for collection and for the public scan. -/
theorem StoreIO.recoverChild_selected (ops : StoreIO s disk Q)
    (start : Q w) (prior : Recoverable known req (disk w)) :
    IOReturns s.recoverChild w
      (fun out t => (∃ fd, ChildLockAt (segmentPath s.root out.1.control.active) out.2 fd) ∧
        Q t ∧ Installed out.1 (disk t) ∧ PermittedView known req out.1.view ∧
        RecoveredChild disk ops.children.owns out.1 out.2 t)
      (fun t => Q t ∧ Recoverable known req (disk t)) := by
  obtain ⟨c, found, history, pending, readable, permit⟩ := prior.live
  let P0 := fun t => Q t ∧ Writebacks (disk w) (disk t)
  let P := fun t => Q t ∧ OpenLayout c history pending (disk t)
  let bad := fun t => Q t ∧ Recoverable known req (disk t)
  let held := fun final h t => PermittedView known req (historyView c final) ∧
    final.length ≤ (c.active+1)*c.capacity ∧
    (∀ id, id < c.active → segmentHistory c.capacity id history = segmentHistory c.capacity id final) ∧
    ActiveFrame ops.children c final h t
  let bs := segmentHistory c.capacity c.active history
  have control : ∀ t, P0 t → ControlCodec.decode (ops.controlBytes t) = some c := by
    rintro t ⟨q, same⟩
    rw [ops.controlBound t q, same.live, found]
  have bounds := decode_bounds (control w ⟨start, .nil⟩)
  have src := s.readControl_fromFile (ops.metadata w start) (ops.file (disk w))
    (fun t pt => ControlCodec.canonical_of_decode (control t pt)) bounds.1 bounds.2
  have barrier {t} (steps : Writebacks (disk w) (disk t)) : OpenLayout c history pending (disk t).syncRoot :=
    let reached := steps.readable readable
    let bound := steps.live.trans found
    ⟨reached.frame (fun id selected => ⟨(reached.layout.names id selected).1,
      (reached.layout.names id selected).1⟩) (fun _ _ => rfl), bound, bound⟩
  apply mapIO (s.recoverChild_post c history P0 P held bad ?source ?retry0 ?retry ?sync ?sealed ?acquire ?scan ?close ?collect ?layout)
  case success =>
    rintro ⟨_, child⟩ t ⟨final, rfl, allowed, _, _, owned, q, installed⟩
    exact ⟨ops.children.source c.active child _ t owned, q, ⟨final, rfl, installed⟩, allowed, _, rfl, owned, installed⟩
  case failure => exact fun _ h => h
  case source =>
    exact src.mapPost (fun _ _ result => ⟨result.2, result.1⟩) (fun _ result => ⟨result.1, result.2.recoverable prior⟩)
  case retry0 => exact fun _ result => ⟨result.1, result.2.recoverable prior⟩
  case retry => exact fun _ result => ⟨result.1, result.2.retry permit⟩
  case sync =>
    rintro t ⟨q, same⟩
    apply Returns.mapPost (s.syncRoot_io (ops.sync t q))
    · rintro _ u ⟨q', steps⟩
      exact ⟨q', (barrier same).writebacks steps⟩
    · rintro u ⟨q', steps | steps⟩
      · exact ⟨q', (same.trans steps).recoverable prior⟩
      · exact ⟨q', ((barrier same).writebacks steps).retry permit⟩
  case sealed => exact fun id lo lt u post => ops.children.readSealed permit post.2 post.1 lo lt
  case acquire =>
    rintro u ⟨q, entry⟩
    apply mapIO (ops.children.select c.policy c.active bs pending u q
      (entry.readable.layout.names _ c.selectsActive).1 entry.readable.active)
    · rintro h v ⟨q', change, actual, choice, owned, installed, _⟩
      have bounded (b) (member : b ∈ actual) : b.length ≤ 32 := by
        apply entry.readable.active.dirty.bounded b
        rcases choice with rfl | rfl
        · exact List.mem_append_left _ member
        · exact member
      obtain ⟨final, good, slice, earlier, extend⟩ := Model.resolve_active entry.readable choice bounded
      obtain ⟨layout, live, durable⟩ := entry.activeLayout change
      have finalLayout := extend _ layout
      refine ⟨final, permit final good, finalLayout.upper, fun id lt => (earlier id lt).symm, ?_, q', ?_⟩
      · exact slice.symm ▸ owned
      · exact ⟨⟨finalLayout, slice.symm ▸ installed⟩, live, durable⟩
    · rintro v ⟨q', change, kept, _⟩
      exact ⟨q', (entry.activeFail change kept).retry permit⟩
  case scan =>
    rintro final h u ⟨choice, upper, before, owned, q, installed⟩
    apply mapIO (ops.children.scan c.active h _ u owned q)
    · rintro bytes t ⟨rfl, owns, qt, same⟩
      exact ⟨rfl, choice, upper, before, owns, qt, same.readyLayout installed.1, same.live.trans installed.2.1, same.durable.trans installed.2.2⟩
    · rintro t ⟨owns, qt, same⟩
      exact ⟨choice, upper, before, owns, qt, same.readyLayout installed.1, same.live.trans installed.2.1, same.durable.trans installed.2.2⟩
  case close =>
    rintro final h u ⟨choice, upper, before, owned, q, installed⟩
    have after {t} (r : Q t ∧ AfterClose (disk u) (disk t)) : bad t :=
      ⟨r.1, Recoverable.cursors ((show Installed (sessionOf c final) (disk u) from ⟨final, rfl, installed⟩).offline choice) r.2⟩
    exact mapIO (ops.children.close c.active h _ u owned q) (fun _ _ post => after post) (fun _ post => after post)
  case collect =>
    rintro final h u ⟨choice, upper, before, active⟩
    exact (CollectionIO.collect s c (ops.cleanup c final h) (ops.cleanupSync c final h) active).mapPost
      (fun _ _ next => ⟨choice, upper, before, next⟩) (fun _ next => ⟨choice, upper, before, next⟩)
  case layout =>
    rintro final h u ⟨_, upper, before, _⟩
    exact ⟨upper, segmentWindow_same before _ _ (by have := Nat.min_le_left c.active (c.discarded / c.capacity); unfold Control.firstNeeded; omega)⟩

theorem StoreIO.recoverChild_disk (ops : StoreIO s disk Q)
    (start : Q w) (prior : Recoverable known none (disk w)) :
    IOReturns s.recoverChild w
      (fun out t => (∃ fd, ChildLockAt (segmentPath s.root out.1.control.active) out.2 fd) ∧
        Q t ∧ Installed out.1 (disk t) ∧ out.1.view = known)
      (fun t => Q t ∧ Recoverable known none (disk t)) := by
  exact mapIO (ops.recoverChild_selected start prior) (fun _ _ v => ⟨v.1, v.2.1, v.2.2.1,
    by simpa [PermittedView] using v.2.2.2.1⟩) (fun _ h => h)

end WalRecoverySlice.Segmented.Native
