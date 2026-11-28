import Alvoki.Experiments.WAL.Segmented.Proofs.AppendRotationIO

namespace WalRecoverySlice.Segmented.Native.AppendIO
open Alvoki.NativePost (W)
open Model (Disk State AppendReady successor)

def FreshPhase (p : Policy) : SingleFile.AppendPhase :=
  .active .lock (SingleFile.appendBindings p) (Persistence.historyCursor []) []

def NewLayout (session : Session) (st : Work) : Prop :=
  let next := successor session
  ∃ history, session.view = historyView next history ∧ ReadyLayout next history st.1.disk ∧
    st.1.disk.liveControl = some next ∧ st.1.disk.durableControl = some next ∧
    segmentHistory next.capacity next.active history = [] ∧
    history.length < (next.active + 1) * next.capacity ∧ st.2 = FreshPhase next.policy

def ModelFrame (session : Session) (batch : Bytes) (point : Point) (st : Work) : Prop :=
  let id := (successor session).active
  match point with
  | .cleared => Installed session st.1.disk
  | .prepared => Installed session st.1.disk ∧ id ∈ st.1.disk.liveNames ∧
      st.1.disk.segment id = Persistence.freshImage ∧ st.1.disk.cursor id = {} ∧ st.2 = FreshPhase session.control.policy
  | .synced => Installed session st.1.disk ∧ id ∈ st.1.disk.liveNames ∧ id ∈ st.1.disk.durableNames ∧
      Child.Installed session.control.policy (st.1.disk.segment id) (st.1.disk.cursor id) [] ∧ st.2 = FreshPhase session.control.policy
  | .published => NewLayout session st
  | .written | .unwind => Recoverable session.view (some (.append batch)) st.1.disk

private theorem unwrap {b : Model.M α} {ret : Except String α}
    (run : (Model.liftRootAction b).run s = .ok ret t) : b.run s.1 = .ok ret t.1 ∧ t.2 = s.2 := by
  unfold Model.liftRootAction at run
  dsimp only [ExceptT.run] at run
  split at run <;> cases run
  exact ⟨by assumption,rfl⟩

private theorem published_step {r : Reports batch} (c : Context disk) (st : Work)
    (before : ModelFrame c.session batch .synced st)
    (full : c.session.activeCount = c.session.control.capacity) (room : c.session.view.tail < Contract.maxPosition) :
    let op := (Segmented.publish (Model.nativeControlOps c.store.root r.directory r.effects) (successor c.session))
    Model.DiskPost (fun _ d => ∃ history,
        c.session.view = historyView (successor c.session) history ∧ ReadyLayout (successor c.session) history d ∧
        d.liveControl = some (successor c.session) ∧ d.durableControl = some (successor c.session) ∧
        segmentHistory (successor c.session).capacity (successor c.session).active history = [] ∧
        history.length < ((successor c.session).active + 1) * (successor c.session).capacity)
      (Recoverable c.session.view none) (op.run st.1) := by
  dsimp only
  obtain ⟨⟨history,shape,layout,l,d⟩,named,saved,child,_⟩ := before
  have visible := congrArg Session.view shape
  change c.session.view = historyView c.session.control history at visible
  have count := congrArg Session.activeCount shape
  change c.session.activeCount = (segmentHistory c.session.control.capacity c.session.control.active history).length at count
  have proved := Model.publishPreparedChild c.store.root r.directory r.effects c.session.control history st.1
    layout l d (count.symm.trans full) (visible ▸ room) ⟨named,saved⟩ child
  dsimp only at proved
  let next := successor c.session
  change Model.DiskPost _ _ ((Segmented.publish (Model.nativeControlOps c.store.root r.directory r.effects) next).run st.1) at proved ⊢
  cases ran : (Segmented.publish (Model.nativeControlOps c.store.root r.directory r.effects) next).run st.1 with
  | error => rw [ran] at proved; exact visible ▸ proved
  | ok response after =>
    rw [ran] at proved
    cases response with
    | error => exact visible ▸ proved
    | ok =>
      obtain ⟨⟨_,_,_,l,d⟩,_,entry⟩ := proved
      have empty := segmentHistory_next_empty layout.layout.upper
      have positive := layout.layout.capacityPositive
      have upper := layout.layout.upper
      refine ⟨history,visible,entry,l,d,empty,?_⟩
      change history.length < (c.session.control.active + 1 + 1) * c.session.control.capacity
      rw [Nat.add_mul,Nat.one_mul]; omega

private theorem write_step {r : Reports batch} (c : Context disk) (st : Work)
    (before : NewLayout c.session st) (size : batch.length ≤ 32) (room : c.session.view.tail < Contract.maxPosition)
    (ran : (Model.writeAs c.session (r.append c.session.control.policy) (.acquired c.nextId) (.acquired c.nextId) batch).run st =
      .ok report u) : Recoverable c.session.view (some (.append batch)) u.1.disk := by
  obtain ⟨history,view,entry,l,d,empty,spare,phase⟩ := before
  let next := successor c.session
  have post := Model.writeActive_refines next history batch st.1 entry l d spare size (view ▸ room) (r.append _)
  dsimp only at post
  rw [empty] at post
  have phaseEq : st.2 = .active .lock (SingleFile.appendBindings next.policy) (Persistence.historyCursor []) [] := phase
  rw [← phaseEq] at post
  simp [Model.writeAs, Model.writeRequested, Model.AppendChild.segment] at ran
  change (Model.writeActive next.policy next.active (r.append next.policy)).run (st.1,st.2) = _ at ran
  rw [ran] at post
  cases report with
  | error => exact view ▸ post
  | ok =>
    obtain ⟨installed,l,d⟩ := post
    have whole : Installed (sessionOf next (history ++ [batch])) u.1.disk :=
      ⟨_,rfl,installed,l,d⟩
    apply whole.offline
    right
    rw [view]
    simp [Contract.Request.apply, ← view,room,sessionOf]
    rw [view]
    exact (historyView_append entry.layout.discardedFits batch).symm

theorem Prefix.layout {c : Context disk} {r : Reports batch}
    (ready : AppendReady c.session s) (size : batch.length ≤ 32)
    (room : c.session.view.tail < Contract.maxPosition) (full : c.session.activeCount = c.session.control.capacity)
    (linux : System.Platform.isWindows = false) (path : Prefix c r w s point child t st) :
    ModelFrame c.session batch point st := by
  induction path with
  | close ret =>
    have live : LivePhase s := by obtain ⟨_,_,_,_,_,eq⟩ := ready; exact .inr ⟨_,_,_,eq⟩
    have eq := ret.2
    rw [model_close s live] at eq
    split at eq <;> cases eq
    exact ready.installed
  | create prev ret ih =>
    have eq := ret.2
    simp only [Model.acquireSuccessor, ExceptT.run] at eq
    split at eq <;> try cases eq
    rename_i ran
    have facts := Model.prepareNativeChild_frames c.store.root r.removal (fun n => r.effects.prepare n c.nextId)
      r.create c.nextId c.session _ ih (Nat.lt_succ_self _)
    dsimp only [ExceptT.run] at facts
    rw [ran] at facts
    have fresh := Model.prepareNativeChild_authority _ _ _ _ _ _ linux ran
    exact ⟨facts.1,facts.2,fresh.1,fresh.2.1,fresh.2.2.1⟩
  | sync prev ret ih =>
    obtain ⟨installed,named,image,cursor,phase⟩ := ih
    obtain ⟨run,same⟩ := unwrap ret.2
    have post := Model.settlePreparedChild c.store.root r.directory r.effects c.session _ installed named
    rw [run] at post
    obtain ⟨new,l,d,files,positions⟩ := post
    exact ⟨new,l,d,by rw [files,positions,image,cursor]; exact Child.Installed.fresh _,same.trans phase⟩
  | syncError prev ret ih =>
    obtain ⟨_,_,_,ran⟩ := ret
    obtain ⟨run,_⟩ := unwrap ran
    have post := Model.settlePreparedChild c.store.root r.directory r.effects c.session _ ih.1 ih.2.1
    rw [run] at post
    exact post.offline (.inl rfl)
  | publish prev ret ih =>
    obtain ⟨run,same⟩ := unwrap ret.2
    have post := published_step (r := r) c _ ih full room
    dsimp only at post
    rw [run] at post
    obtain ⟨hist,v,e,l,d,empty,spare⟩ := post
    exact ⟨hist,v,e,l,d,empty,spare,same.trans ih.2.2.2.2⟩
  | publishError prev ret ih =>
    obtain ⟨_,_,_,ran⟩ := ret
    obtain ⟨run,_⟩ := unwrap ran
    have post := published_step (r := r) c _ ih full room
    dsimp only at post
    rw [run] at post
    exact Model.noAppend_pending post
  | write prev ret ih => exact write_step (r := r) c _ ih size room ret.2
  | writeError prev ret ih =>
    obtain ⟨_,_,_,ran⟩ := ret
    exact write_step (r := r) c _ ih size room ran

end WalRecoverySlice.Segmented.Native.AppendIO
