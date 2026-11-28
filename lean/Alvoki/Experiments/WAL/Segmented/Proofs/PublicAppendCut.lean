import Alvoki.Experiments.WAL.Segmented.Proofs.ChildCutCoverage
import Alvoki.Experiments.WAL.Segmented.Proofs.PrepareCutCoverage
import Alvoki.Experiments.WAL.Segmented.Proofs.CloseCutCoverage

namespace WalRecoverySlice.Segmented.Native.AppendCut
open Model (Disk)
open Observed (leaf finallyUnlock bindCuts bindRun resultCuts)
open AppendIO (LocalIO Active sourceState inputContext issuedWorld installedWorld)
open Alvoki.NativePost (W IOReturns)

inductive PublicStop (cell : IO.Ref (Phase Store)) (mutex : Std.BaseMutex) (store : Store)
    (session : Session) (batch : Bytes) (w : W) (stop : Stop) (d : Disk) : Prop where
  | lock : stop (liftM mutex.lock : IO Unit) w d → PublicStop cell mutex store session batch w stop d
  | read : stop (cell.get : IO _) (mutex.lock w).state d → PublicStop cell mutex store session batch w stop d
  | poison : stop (cell.set (.poisoned store) : IO _) ((cell.get : BaseIO _) (mutex.lock w).state).state d →
      PublicStop cell mutex store session batch w stop d
  | worker : ((sites store session stop).appendSession session batch).cuts
      (issuedWorld cell mutex store w) d → PublicStop cell mutex store session batch w stop d
  | install : store.appendSession session batch (issuedWorld cell mutex store w) = .ok next t →
      stop (cell.set (.ready store next) : IO _) t d → PublicStop cell mutex store session batch w stop d
  | leave : store.appendSession session batch (issuedWorld cell mutex store w) = .ok next t →
      stop (liftM mutex.unlock : IO Unit) (installedWorld cell store next t) d → PublicStop cell mutex store session batch w stop d
  | fail : store.appendSession session batch (issuedWorld cell mutex store w) = .error e t →
      stop (liftM mutex.unlock : IO Unit) t d → PublicStop cell mutex store session batch w stop d

/-- Source-side observations of the nested operating-system calls. The
proof below transforms them into the prefix evidence used by the disk model. -/
def sourceSites (s : Store) (session : Session) (stop : Stop) : Sites s :=
  { sites s session stop with
    prepare := fun _ _ => (PrepareCutIO.program s session.control stop).cuts
    publish := fun _ => (ControlCutIO.program s session.control stop).cuts
    write := ChildCutIO.source stop
    close := closeSource stop
    oldClose := (oldCloseProgram s stop).cuts }

private structure Covers (source certified : Observed α) : Prop where
  erase : source.run = certified.run
  covered : ∀ {w d}, source.cuts w d → certified.cuts w d

private theorem Covers.bind {a b : Observed α} {f g : α → Observed β} (first : Covers a b)
    (rest : ∀ x, Covers (f x) (g x)) : Covers (a >>= f) (b >>= g) := by
  refine ⟨?_, ?_⟩
  · change (a.run >>= fun x => (f x).run) = (b.run >>= fun x => (g x).run)
    rw [first.erase]
    exact congrArg (Bind.bind b.run) (funext fun x => (rest x).erase)
  · rintro w d (cut | ⟨x,t,ran,cut⟩)
    · exact Or.inl (first.covered cut)
    · exact Or.inr ⟨x,t,first.erase ▸ ran,(rest x).covered cut⟩

private theorem Covers.catch {a b : Observed α} {f g : IO.Error → Observed α} (first : Covers a b)
    (rest : ∀ x, Covers (f x) (g x)) :
    Covers (tryCatchThe IO.Error a f) (tryCatchThe IO.Error b g) := by
  refine ⟨?_, ?_⟩
  · change tryCatchThe IO.Error a.run (fun e => (f e).run) = tryCatchThe IO.Error b.run (fun e => (g e).run)
    rw [first.erase]
    exact congrArg (tryCatchThe IO.Error b.run) (funext fun x => (rest x).erase)
  · rintro w d (cut | ⟨x,t,ran,cut⟩)
    · exact Or.inl (first.covered cut)
    · exact Or.inr ⟨x,t,first.erase ▸ ran,(rest x).covered cut⟩

private theorem Covers.refl (a : Observed α) : Covers a a := ⟨rfl, fun h => h⟩

private theorem bodyCovered (s : Store) (session : Session) (batch : Bytes) (stop : Stop) :
    Covers ((sourceSites s session stop).appendSession session batch)
      ((sites s session stop).appendSession session batch) := by
  unfold Sites.appendSession appendOwnedWith
  apply Covers.bind (Covers.refl _)
  intro _
  dsimp only
  split
  · apply Covers.bind
    · exact ⟨rfl, fun hit => oldCloseCovered hit⟩
    intro _
    unfold withActiveChild cleanupOnError
    apply Covers.bind
    · exact ⟨rfl, fun hit => PrepareCutIO.covered hit⟩
    intro h
    apply Covers.catch
    · apply Covers.bind (Covers.refl _)
      intro _
      apply Covers.bind
      · exact ⟨rfl, fun hit => ControlCutIO.covered hit⟩
      intro _
      apply Covers.bind
      · exact ⟨rfl, fun hit => ChildCutIO.sourceCovered hit⟩
      · exact fun _ => Covers.refl _
    · intro _
      apply Covers.bind
      · apply Covers.catch
        · exact ⟨rfl, fun hit => closeCovered hit⟩
        · exact fun _ => Covers.refl _
      · exact fun _ => Covers.refl _
  · apply Covers.bind (Covers.refl _)
    intro slot
    cases slot with
    | none => exact Covers.refl _
    | some pair =>
      obtain ⟨id,h⟩ := pair
      dsimp only
      split
      · apply Covers.bind
        · exact ⟨rfl, fun hit => ChildCutIO.sourceCovered hit⟩
        · exact fun _ => Covers.refl _
      · apply Covers.bind (Covers.refl _)
        intro _
        apply Covers.bind
        · exact ⟨rfl, fun hit => ChildCutIO.sourceCovered hit⟩
        · exact fun _ => Covers.refl _

/-- Instantiate the executable phase update and child scheduling code with
primitive observations. The lock and the finalizer surround the same body
for successful and failed calls. -/
def publicProgram (cell : IO.Ref (Phase Store)) (mutex : Std.BaseMutex) (batch : Bytes)
    (stop : Stop) : Observed Nat := appendPositionWith do
  let _ ← leaf stop (liftM mutex.lock : IO Unit)
  finallyUnlock (updateWith IO.userError (leaf stop (cell.get : IO _))
    (fun ph => leaf stop (cell.set ph : IO Unit))
    (fun store session => (sourceSites store session stop).appendSession session batch)) mutex stop

private theorem readReady (cell : IO.Ref (Phase Store)) (mu : Std.BaseMutex) (stop : Stop) (w : W)
    (ready : ((cell.get : BaseIO _) (mu.lock w).state).val = .ready s session) :
    (leaf stop (cell.get : IO _)).run (mu.lock w).state =
      .ok (.ready s session) ((cell.get : BaseIO _) (mu.lock w).state).state := by
  change EST.Out.ok _ _ = _
  rw [← ready]
  rfl

private theorem updateOutput (cell : IO.Ref (Phase Store)) (mu : Std.BaseMutex) (stop : Stop)
    (batch : Bytes) (w : W) (ready : ((cell.get : BaseIO _) (mu.lock w).state).val = .ready s session) :
    (updateWith IO.userError (leaf stop (cell.get : IO _))
      (fun ph => leaf stop (cell.set ph : IO Unit))
      (fun store session => (sourceSites store session stop).appendSession session batch)).run (mu.lock w).state =
      match s.appendSession session batch (issuedWorld cell mu s w) with
      | .error e t => .error e t
      | .ok next t => .ok next (installedWorld cell s next t) := by
  unfold updateWith
  rw [bindRun, readReady cell mu stop w ready]
  change (((sourceSites s session stop).appendSession session batch).run >>= _) (issuedWorld cell mu s w) = _
  rw [Sites.erase]
  cases a : s.appendSession session batch (issuedWorld cell mu s w) <;>
    simp [Bind.bind, instMonadEIO._aux_13, EST.bind, a] <;> rfl

theorem publicProgram_run {wal : Handle} (parts : wal.Parts cell mu) (stop : Stop) (batch : Bytes) (w : W)
    (ready : ((cell.get : BaseIO _) (mu.lock w).state).val = .ready s session) :
    (publicProgram cell mu batch stop).run w = append wal batch w := by
  rw [append_ready_run parts batch w ready]
  unfold publicProgram appendPositionWith
  simp only [bindRun]
  have held : (leaf stop (liftM mu.lock : IO Unit)).run w = .ok () (mu.lock w).state := rfl
  simp only [held]
  have cleanup (act : IO Session) (t : W) :
      (try act finally mu.unlock : IO Session) t =
      match act t with
      | .ok x u => .ok x (mu.unlock u).state | .error e u => .error e (mu.unlock u).state := by
    simp only [tryFinally, tryFinally', MonadFinally.tryFinally', instMonadFinallyEIO._aux_1, Functor.map, instMonadEIO._aux_1, EST.bind]
    cases act t <;> rfl
  simp only [finallyUnlock, cleanup, updateOutput cell mu stop batch w ready]
  simp only [issuedWorld]
  cases s.appendSession session batch ((cell.set (.poisoned s) : BaseIO _) ((cell.get : BaseIO _) (mu.lock w).state).state).state <;> rfl

/-- Reverse coverage: every raw observation emitted by this instantiation
of the actual update goes to an admitted stop, including both unlock paths. -/
theorem publicProgram_covered (cell : IO.Ref (Phase Store)) (mu : Std.BaseMutex) (stop : Stop)
    (batch : Bytes) (w : W) (ready : ((cell.get : BaseIO _) (mu.lock w).state).val = .ready s session)
    (obs : (publicProgram cell mu batch stop).cuts w d) : PublicStop cell mu s session batch w stop d := by
  unfold publicProgram appendPositionWith at obs
  rw [resultCuts, bindCuts] at obs
  rcases obs with early | body
  · exact .lock early
  change _ ∨ stop _ (returnedWorld _) d at body
  rcases body with inner | leaving
  · unfold updateWith at inner
    rw [bindCuts] at inner
    rcases inner with early | phase
    · exact .read early
    simp only [readReady cell mu stop w ready] at phase
    rw [bindCuts] at phase
    rcases phase with early | work
    · exact .poison early
    change (_ >>= _ : Observed _).cuts (issuedWorld cell mu s w) d at work
    rw [bindCuts, Sites.erase] at work
    rcases work with early | installed
    · exact .worker ((bodyCovered s session batch stop).covered early)
    cases ran : s.appendSession session batch (issuedWorld cell mu s w) with
    | error e t => rw [ran] at installed; contradiction
    | ok next t =>
      rw [ran] at installed
      exact .install ran ((resultCuts ..).mp installed)
  · rw [updateOutput cell mu stop batch w ready] at leaving
    cases ran : s.appendSession session batch (issuedWorld cell mu s w) with
    | error e t => rw [ran] at leaving; exact .fail ran leaving
    | ok next t => rw [ran] at leaving; exact .leave ran leaving

/-- The physical pending state is already available upon ordinary worker
return, before updating the outer WAL phase or releasing its mutex. -/
private theorem afterWorker {disk : W → Disk} {mem : ChildMemory disk}
    (op : LocalIO mem heap Q wal reg batch w) (active : Active mem heap wal reg w) (q : Q w)
    (size : batch.length ≤ 32) (room : reg.session.view.tail < Contract.maxPosition)
    (linux : System.Platform.isWindows = false) :
    let retry t := Recoverable reg.session.view (some (.append batch)) (disk t)
    IOReturns (reg.store.appendSession reg.session batch) (issuedWorld op.cell op.mutex reg.store w)
      (fun next t => Installed next (disk t) ∧ next.view = reg.session.view.append batch) retry := by
  obtain ⟨phase,ready,typed⟩ := op.begin active q
  let c := inputContext mem heap Q op.cell reg
  let s := sourceState disk w reg phase
  let begin := issuedWorld op.cell op.mutex reg.store w
  have bounds := Model.successor_controlRepresentable ready.installed room
  have tied := AppendIO.appendSession (w := begin) (s := s) op.reports reg.store reg.session size room
    (done := c.Done batch) (bad := c.Failed)
    (fun ne => (op.inside phase ne typed).assemble typed.1 rfl ne)
    (fun full => (op.rotate phase full typed).assemble typed bounds.1 bounds.2 full linux)
  let r := op.reports
  have model := Model.nativeAppendModel_refines reg.store.root r.directory r.removal r.effects r.create r.close
    reg.session (r.append reg.session.control.policy) s ready rfl size room linux
  dsimp only at model
  unfold AppendIO.At at tied
  dsimp only
  change IOReturns (reg.store.appendSession reg.session batch) begin _ _
  unfold IOReturns
  cases ar : reg.store.appendSession reg.session batch begin <;> cases mr : (r.action reg.store reg.session).run s with
    | error => rw [ar,mr] at tied; contradiction
    | ok response after =>
      rw [ar,mr] at tied
      unfold AppendIO.Reports.action at mr
      rw [mr] at model
      cases response <;> try contradiction
      first
      | obtain ⟨shape,rfl,child,base,_⟩ := tied
        refine ⟨base.2.1.installed model.2.1.installed, ?_⟩
        rw [shape]
        unfold AppendIO.nextSession
        split <;> rfl
      | obtain ⟨slot,base,_⟩ := tied
        exact base.2.1.recoverable model.1

inductive BeforeWorker (cell : IO.Ref (Phase Store)) (mutex : Std.BaseMutex) (store : Store)
    (w : W) (stop : Stop) (d : Disk) : Prop where
  | lock : stop (liftM mutex.lock : IO Unit) w d → BeforeWorker cell mutex store w stop d
  | read : stop (cell.get : IO _) (mutex.lock w).state d → BeforeWorker cell mutex store w stop d
  | poison : stop (cell.set (.poisoned store) : IO _) ((cell.get : BaseIO _) (mutex.lock w).state).state d →
      BeforeWorker cell mutex store w stop d

inductive AfterSuccess (cell : IO.Ref (Phase Store)) (mutex : Std.BaseMutex) (store : Store)
    (session : Session) (batch : Bytes) (w : W) (stop : Stop) (d : Disk) : Prop where
  | install : store.appendSession session batch (issuedWorld cell mutex store w) = .ok next t →
      stop (cell.set (.ready store next) : IO _) t d → AfterSuccess cell mutex store session batch w stop d
  | leave : store.appendSession session batch (issuedWorld cell mutex store w) = .ok next t →
      stop (liftM mutex.unlock : IO Unit) (installedWorld cell store next t) d →
      AfterSuccess cell mutex store session batch w stop d

theorem BeforeWorker.writes (cut : BeforeWorker cell mutex store w stop d) (volatile : VolatileIO disk stop) :
    Writebacks (disk w) d := by
  cases cut with
  | lock cut => exact (volatile.stopped _ (.lock _) _ _ cut)
  | read cut => exact ((volatile.lock mutex w).trans (volatile.stopped _ (.get _) _ _ cut))
  | poison cut =>
    exact (((volatile.lock mutex w).trans (volatile.get cell _)).trans
      (volatile.stopped _ (.set _ _) _ _ cut))

theorem recoverBefore {disk : W → Disk} {mem : ChildMemory disk}
    (op : LocalIO mem heap Q wal reg batch w) (prim : CutRuntime disk reg.store reg.session stop)
    (active : Active mem heap wal reg w) (cut : BeforeWorker op.cell op.mutex reg.store w stop d) :
    Recoverable reg.session.view none d := by
  obtain ⟨_,_,_,_,_,ready⟩ := active
  have prior : Recoverable reg.session.view none (disk w) := ready.installed.offline (.inl rfl)
  exact (cut.writes prim.volatile).recoverable prior

theorem recoverAfterSuccess {disk : W → Disk} {mem : ChildMemory disk}
    (op : LocalIO mem heap Q wal reg batch w) (volatile : VolatileIO disk stop)
    (active : Active mem heap wal reg w) (q : Q w) (size : batch.length ≤ 32)
    (room : reg.session.view.tail < Contract.maxPosition) (linux : System.Platform.isWindows = false)
    (cut : AfterSuccess op.cell op.mutex reg.store reg.session batch w stop d) :
    Recoverable (reg.session.view.append batch) none d := by
  have returned := afterWorker op active q size room linux
  dsimp only at returned
  cases cut with
  | install ran cut =>
    rw [IOReturns,ran] at returned
    exact (volatile.stopped _ (.set _ _) _ _ cut).recoverable (returned.1.offline (.inl returned.2))
  | leave ran cut =>
    rw [IOReturns,ran] at returned
    exact ((volatile.set op.cell _ _).trans (volatile.stopped _ (.leave _) _ _ cut)).recoverable
      (returned.1.offline (.inl returned.2))

private theorem uncertainNew {new : Contract.View} (pinned : Recoverable new none d)
    (choice : PermittedView old (some (.append batch)) new) : Recoverable old (some (.append batch)) d := by
  have select c (prior : RecoveryChoice new none c d) : RecoveryChoice old (some (.append batch)) c d := by
    obtain ⟨hist,p,readable,allowed⟩ := prior
    refine ⟨hist,p,readable,fun actual permit => ?_⟩
    have eq : historyView c actual = new := by simpa [PermittedView] using allowed actual permit
    exact eq ▸ choice
  obtain ⟨c,l,v⟩ := pinned.live
  obtain ⟨q,r,u⟩ := pinned.durable
  exact ⟨⟨_, l, select _ v⟩, ⟨_, r, select _ u⟩⟩

theorem recoverPublic {disk : W → Disk} {mem : ChildMemory disk}
    (op : LocalIO mem heap Q wal reg batch w) (prim : CutRuntime disk reg.store reg.session stop)
    (active : Active mem heap wal reg w) (q : Q w) (size : batch.length ≤ 32)
    (room : reg.session.view.tail < Contract.maxPosition) (linux : System.Platform.isWindows = false)
    (cut : PublicStop op.cell op.mutex reg.store reg.session batch w stop d) : Recoverable reg.session.view (some (.append batch)) d := by
  cases cut with
  | lock cut => exact allowPending (recoverBefore op prim active (.lock cut)) _
  | read cut => exact allowPending (recoverBefore op prim active (.read cut)) _
  | poison cut => exact allowPending (recoverBefore op prim active (.poison cut)) _
  | worker cut => exact recoverBody op prim active q size room linux cut
  | install ran cut =>
    exact uncertainNew (recoverAfterSuccess op prim.volatile active q size room linux (.install ran cut))
      (.inr (by simp [Contract.Request.apply,room]))
  | leave ran cut =>
    exact uncertainNew (recoverAfterSuccess op prim.volatile active q size room linux (.leave ran cut))
      (.inr (by simp [Contract.Request.apply,room]))
  | fail ran cut =>
    have returned := afterWorker op active q size room linux
    dsimp only at returned
    rw [IOReturns,ran] at returned
    exact (prim.volatile.stopped _ (.leave _) _ _ cut).recoverable returned

end WalRecoverySlice.Segmented.Native.AppendCut
